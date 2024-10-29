import json
from itertools import product
from anytree import Node, RenderTree

def print_tree(root, indentation):
    indent = '\t'*indentation
    for pre, _, node in RenderTree(root):
        print(indent + f"{pre}{node.name}")

class Parser:
    def __init__(self, proposition):
        self.proposition = proposition.replace(" ", "").replace("→", "⇒")
        self.index = 0
        self.length = len(self.proposition)
        self.operation_count = 0
        self.root = None

    def current_chr(self):
        return self.proposition[self.index] if self.index < self.length else None

    def is_chr(self, char):
        return char.isalpha() and char.isupper()

    def parse_atomic(self):
        start_index = self.index
        char = self.current_chr()

        if char and self.is_chr(char):
            atomic_proposition = char
            self.index += 1

            while self.index < self.length and self.proposition[self.index].isdigit():
                atomic_proposition += self.proposition[self.index]
                self.index += 1

            print(f"\t{atomic_proposition} is an atomic {'subformula' if self.operation_count else 'formula'}, index: {start_index}")
            node = Node(atomic_proposition)
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        return None

    def parse_unary(self):
        if self.current_chr() == "(" and self.proposition[self.index + 1] == "¬":
            self.operation_count += 1
            self.index += 1
            print(f"\tDetected unary connective: ¬, at index: {self.index}.")
            self.index += 1

            sub_node = self.parse_expression()
            if not sub_node:
                raise Exception(f"Error: Expected an expression following ¬, at index: {self.index}.")
            if self.current_chr() != ")":
                raise Exception(f"Error: Expected closing parenthesis after unary expression, at index: {self.index}.")
            self.index += 1
            node = Node("¬", children=[sub_node])
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        return None

    def parse_binary(self):
        if self.current_chr() == "(":
            self.operation_count += 1
            self.index += 1
            left_node = self.parse_expression()
            if not left_node:
                raise Exception(
                    f"Error: Expected an expression on the left side of a binary operator, at index: {self.index}.")

            connective = self.current_chr()
            if connective not in ['∧', '∨', '⇒', '⇔']:
                raise Exception(f"Error: Expected a binary operator (∧, ∨, ⇒, ⇔), at index: {self.index}.")
            print(f"\tDetected binary connective: {connective}, at index: {self.index}")
            self.index += 1

            right_node = self.parse_expression()
            if not right_node:
                raise Exception(
                    f"Error: Expected an expression on the right side of '{connective}', at index: {self.index}.")

            if self.current_chr() != ")":
                raise Exception(
                    f"Error: Expected closing parenthesis after binary expression with '{connective}', at index: {self.index}.")
            self.index += 1
            node = Node(connective, children=[left_node, right_node])
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        return None

    def parse_expression(self):
        return self.parse_atomic() or self.parse_unary() or self.parse_binary()

    def parse(self):
        print(f"Starting parsing for: '{self.proposition}'")
        if not self.proposition:
            raise Exception("Error: Empty proposition")

        self.root = self.parse_expression()
        if self.root and self.index == self.length:
            print("The string is a well formed formula.")
            return self.root
        if self.current_chr() in ['∧', '∨', '⇒', '⇔']:
            raise Exception(f"Error: Binary operator '{self.current_chr()}' not enclosed in parentheses.")
        if self.current_chr() == ")" or self.current_chr() is None:
            raise Exception("Error: Unbalanced parentheses detected.")
        if self.current_chr() == "¬" and self.index < self.length - 1:
            raise Exception("Error: '¬' operator must be enclosed in parentheses.")
        raise Exception("Error: Invalid structure.")

    def get_variables(self, node):
        return {node.name} if node.name[0].isupper() and all(c.isalnum() for c in node.name) else {var for child in node.children for var in self.get_variables(child)}

    def evaluate(self, node, values):
        if node.name == "¬":
            return not self.evaluate(node.children[0], values)
        elif node.name in ["∧", "∨", "⇒", "⇔"]:
            left, right = self.evaluate(node.children[0], values), self.evaluate(node.children[1], values)
            return {
                "∧": left and right,
                "∨": left or right,
                "⇒": not left or right,
                "⇔": left == right
            }[node.name]
        elif node.name in values:
            return values[node.name]
        raise Exception(f"Missing truth value for {node.name}")

    def truth_table(self):
        variables = sorted(self.get_variables(self.root))
        return [self.evaluate(self.root, dict(zip(variables, vals))) for vals in
                product([False, True], repeat=len(variables))]

    def validity(self):
        truth_table = self.truth_table()
        if all(truth_table):
            return "The formula is satisfiable and valid."
        elif not any(truth_table):
            return "The formula is unsatisfiable and invalid."
        return "The formula is satisfiable but invalid."


try:
    with open("propositions.json", "r", encoding="utf-8") as file:
        input_file = json.load(file)
    print("Data loaded successfully:", end="\n\n")
    for element in input_file:
        proposition = element["proposition"]
        parser = Parser(proposition)
        try:
            root = parser.parse()
            print("The tree representation of the proposition is:")
            print_tree(root, 1)
            print(parser.validity())

            interpretations = element["interpretations"]
            print("Testing the inserted interpretations:")

            for inter in interpretations:
                try:
                    evaluation = parser.evaluate(root, inter)
                    print(f"\tThe truth value of the proposition with {inter} is {evaluation}")
                except Exception as e:
                    print(f"\tError during evaluation with interpretation {inter}: {e}")
        except Exception as e:
            print(f"{e}\nThe string is not a well formed formula.")
        print(end="\n\n")
except FileNotFoundError:
    print("File not found. Ensure 'propositions.json' is in the correct directory.")
except json.JSONDecodeError:
    print("Failed to decode JSON. Ensure the JSON syntax is correct.")
except Exception as e:
    print("An error occurred:", e)
