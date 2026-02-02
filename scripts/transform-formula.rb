#!/usr/bin/env ruby
# frozen_string_literal: true

require 'yaml'
require 'parser/current'
require 'unparser'

CONFIG_PATH = File.expand_path('../config/transforms.yml', __dir__)

module FormulaTransforms
  # Base class for AST transformations
  class Transform
    attr_reader :config

    def initialize(config = {})
      @config = config
    end

    def applies?(_content, _ast)
      true
    end

    def apply(content, ast)
      raise NotImplementedError
    end

    protected

    def find_class_node(ast)
      return ast if ast.type == :class
      ast.children.each do |child|
        next unless child.is_a?(Parser::AST::Node)
        result = find_class_node(child)
        return result if result
      end
      nil
    end
  end

  # Hoists method definitions from nested blocks to class level
  class HoistMethods < Transform
    def applies?(content, _ast)
      methods = config['methods'] || %w[install test caveats]
      # Check if any target method is nested (indent > 2)
      methods.any? { |m| content.match?(/^   +def #{m}\b/) }
    end

    def apply(_content, ast)
      class_node = find_class_node(ast)
      return ast unless class_node

      methods = (config['methods'] || %w[install test caveats]).map(&:to_sym)
      extracted = extract_methods(class_node, methods)
      return ast if extracted.empty?

      cleaned = remove_methods(class_node, methods)
      result = insert_methods_in_class(cleaned, extracted, methods)

      replace_class_node(ast, class_node, result)
    end

    private

    def extract_methods(node, target_methods, found = {}, depth = 0)
      return found unless node.is_a?(Parser::AST::Node)

      if node.type == :def && target_methods.include?(node.children[0])
        method_name = node.children[0]
        found[method_name] ||= node if depth > 1 # only if nested
      end

      node.children.each { |child| extract_methods(child, target_methods, found, depth + 1) }
      found
    end

    def remove_methods(node, target_methods)
      return node unless node.is_a?(Parser::AST::Node)

      # For class nodes, only process the body (3rd child)
      if node.type == :class
        name, superclass, body = node.children
        new_body = remove_methods(body, target_methods)
        return node.updated(nil, [name, superclass, new_body])
      end

      # Track which children we're removing (target methods only)
      removals = []
      new_children = node.children.each_with_index.map do |child, idx|
        if child.is_a?(Parser::AST::Node)
          if child.type == :def && target_methods.include?(child.children[0])
            removals << idx
            nil
          else
            remove_methods(child, target_methods)
          end
        else
          child # preserve non-AST children (symbols, strings, etc.)
        end
      end

      # Only compact if we actually removed something, and only for :begin nodes
      if node.type == :begin
        new_children = new_children.compact
        return nil if new_children.empty?
      elsif node.type == :block
        # block: [send, args, body] - if body becomes nil after removals, remove block
        new_children = new_children.map.with_index do |c, i|
          i == 2 && removals.any? ? nil : c
        end
        body = new_children[2]
        return nil if body.nil? || (body.is_a?(Parser::AST::Node) && body.type == :begin && body.children.empty?)
      end

      node.updated(nil, new_children)
    end

    def insert_methods_in_class(class_node, methods, order)
      name, superclass, body = class_node.children

      body_nodes = case body&.type
                   when nil then []
                   when :begin then body.children.dup
                   else [body]
                   end

      # Sort extracted methods by their position in the config's order array
      sorted_methods = methods.keys.sort_by { |m| order.index(m) || Float::INFINITY }
      sorted_methods.each { |m| body_nodes << methods[m] }

      new_body = Parser::AST::Node.new(:begin, body_nodes)
      class_node.updated(nil, [name, superclass, new_body])
    end

    def replace_class_node(ast, old_class, new_class)
      return new_class if ast == old_class
      ast.updated(nil, ast.children.map { |c| c == old_class ? new_class : c })
    end
  end

  # Reorders class-level methods and DSL blocks (test do, caveats do) to match config order
  class ReorderMethods < Transform
    def applies?(_content, ast)
      class_node = find_class_node(ast)
      return false unless class_node

      methods = (config['methods'] || %w[install test caveats]).map(&:to_sym)
      body = class_node.children[2]
      return false unless body

      body_nodes = body.type == :begin ? body.children : [body]
      positions = find_method_positions(body_nodes, methods)

      # Check if reordering is needed
      return false if positions.size < 2

      sorted = positions.sort_by { |m, _| methods.index(m) || Float::INFINITY }
      positions.keys != sorted.map(&:first)
    end

    def apply(_content, ast)
      class_node = find_class_node(ast)
      return ast unless class_node

      methods = (config['methods'] || %w[install test caveats]).map(&:to_sym)
      result = reorder_class_body(class_node, methods)

      replace_class_node(ast, class_node, result)
    end

    private

    def reorder_class_body(class_node, method_order)
      name, superclass, body = class_node.children
      return class_node unless body

      body_nodes = body.type == :begin ? body.children.dup : [body]

      # Separate method/block nodes from other nodes
      method_nodes = {}
      other_nodes = []

      body_nodes.each do |node|
        method_name = extract_method_name(node, method_order)
        if method_name
          method_nodes[method_name] = node
        else
          other_nodes << node
        end
      end

      # Rebuild body: other nodes first, then methods in config order
      sorted_methods = method_nodes.keys.sort_by { |m| method_order.index(m) || Float::INFINITY }
      new_body_nodes = other_nodes + sorted_methods.map { |m| method_nodes[m] }

      new_body = Parser::AST::Node.new(:begin, new_body_nodes)
      class_node.updated(nil, [name, superclass, new_body])
    end

    def extract_method_name(node, target_methods)
      return nil unless node.is_a?(Parser::AST::Node)

      # def install / def test / def caveats
      return node.children[0] if node.type == :def && target_methods.include?(node.children[0])

      # test do ... end / caveats do ... end (block with send)
      if node.type == :block
        send_node = node.children[0]
        if send_node.is_a?(Parser::AST::Node) && send_node.type == :send
          method_name = send_node.children[1]
          return method_name if target_methods.include?(method_name)
        end
      end

      nil
    end

    def find_method_positions(body_nodes, target_methods)
      positions = {}
      body_nodes.each_with_index do |node, idx|
        method_name = extract_method_name(node, target_methods)
        positions[method_name] = idx if method_name
      end
      positions
    end

    def replace_class_node(ast, old_class, new_class)
      return new_class if ast == old_class
      ast.updated(nil, ast.children.map { |c| c == old_class ? new_class : c })
    end
  end

  # Registry of available transforms
  REGISTRY = {
    'hoist_methods' => HoistMethods,
    'reorder_methods' => ReorderMethods
  }.freeze
end

class FormulaProcessor
  GORELEASER_MARKER = '# This file was generated by GoReleaser'

  def initialize(config_path = CONFIG_PATH)
    @config = File.exist?(config_path) ? YAML.load_file(config_path) : default_config
    @transforms = load_transforms
  end

  def process(path)
    content = File.read(path)

    unless content.include?(GORELEASER_MARKER)
      puts "Skipping #{path}: not a goreleaser formula"
      return false
    end

    buffer = Parser::Source::Buffer.new(path, source: content)
    ast = Parser::CurrentRuby.new.parse(buffer)

    modified = false
    @transforms.each do |transform|
      next unless transform.applies?(content, ast)

      ast = transform.apply(content, ast)
      modified = true
    end

    return false unless modified

    output = Unparser.unparse(ast)

    # Preserve original header comments
    header = content.lines.take_while { |l| l.start_with?('#') || l.strip.empty? }.join
    output = header + output unless header.empty?

    File.write(path, output)
    puts "Processed #{path}"
    true
  end

  private

  def load_transforms
    @config['transforms'].map do |t|
      klass = FormulaTransforms::REGISTRY[t['name']]
      raise "Unknown transform: #{t['name']}" unless klass
      klass.new(t['config'] || {})
    end
  end

  def default_config
    {
      'transforms' => [
        { 'name' => 'hoist_methods', 'config' => { 'methods' => %w[install test caveats] } },
        { 'name' => 'reorder_methods', 'config' => { 'methods' => %w[install test caveats] } }
      ]
    }
  end
end

if __FILE__ == $PROGRAM_NAME
  require 'optparse'

  config_path = CONFIG_PATH
  OptionParser.new do |opts|
    opts.on('--config PATH', 'Path to transforms.yml') { |p| config_path = p }
  end.parse!

  processor = FormulaProcessor.new(config_path)

  files = ARGV.empty? ? Dir.glob('Formula/*.rb') : ARGV
  files.each { |f| processor.process(f) }
end
