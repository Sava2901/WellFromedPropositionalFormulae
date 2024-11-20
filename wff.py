import json
import re
from utility import *


def convert_from_relaxed(prop, is_strong=False, need_print=True):
    if not is_strong:
        converter = ShuntingYardConverter(prop, need_print=need_print)
        prop = converter.convert()
    return prop


class ShuntingYardConverter:
    def __init__(self, expression, need_print=False):
        self.expression = expression.replace(" ", "").replace("→", "⇒")
        self.output_queue = []
        self.operator_stack = []
        self.precedence = {
            '¬': 3,  # Unary NOT
            '∧': 2,  # AND
            '∨': 2,  # OR
            '⇒': 1,  # IMPLIES
            '⇔': 0  # EQUIVALENT
        }
        self.right_associative = {'¬'}
        self.need_print = need_print
        self.print_info = ""


    def is_operator(self, token):
        return token in self.precedence


    def precedence_of(self, token):
        return self.precedence.get(token, 0)


    def convert(self):
        self.print_info += f"Trying to convert {self.expression} to strong syntax.\n"
        if self.expression is "" or self.expression is None:
            print(self.print_info)
            raise Exception("Empty string is not a wff.")
        tokens = re.findall(r"[A-Z][0-9]*|¬|∧|∨|⇒|⇔|[()]|⊤|⊥", self.expression)
        non_matching = re.findall(r"(?![A-Z][0-9]*|¬|∧|∨|⇒|⇔|[()]|⊤|⊥).", self.expression)
        if non_matching:
            print(self.print_info)
            raise Exception(
                f"Found non-matching {'character' if len(non_matching) == 1 else 'characters'} "
                f"{', '.join(non_matching)}.\n {self.expression} cannot be a wff."
            )
        if self.expression.count("(") != self.expression.count(")"):
            print(self.print_info)
            raise Exception(f"Different number of parenthesis.\n{self.expression} is not a wff.")
        for i, token in enumerate(tokens):
            if i:
                if (tokens[i - 1] in ["∧", "∨", "⇒", "⇔", "¬", "("] and token in ["∧", "∨", "⇒", "⇔", ")"]) or (tokens[i - 1] == ")" and token == "("):
                    print(self.print_info)
                    raise Exception(f"Invalid {"parenthesis" if tokens[i - 1] in ["(", ")"] and token in ["(", ")"] else "connectives"} placement: "
                                    f"{tokens[i-1]} cannot be followed by {token}\n{self.expression} cannot be a wff.")
                if re.match(r"[A-Z][0-9]*|⊤|⊥", tokens[i - 1]) and re.match(r"[A-Z][0-9]*|⊤|⊥", token):
                    print(self.print_info)
                    raise Exception(f"An atomic formula '{tokens[i - 1]}' cannot be followed by another atomic formula '{token}'.\n{self.expression} cannot be a wff.")

            if re.match(r"[A-Z][0-9]*|⊤|⊥", token):
                self.output_queue.append(token)
            elif token == '(':
                self.operator_stack.append(token)
            elif token == ')':
                while self.operator_stack and self.operator_stack[-1] != '(':
                    self.output_queue.append(self.operator_stack.pop())
                if len(self.operator_stack) == 0 :
                    print(self.print_info)
                    raise Exception(f"Expression expected before ).\n{self.expression} is not a wff.")
                self.operator_stack.pop()
            elif self.is_operator(token):
                while (self.operator_stack and self.operator_stack[-1] != '(' and
                       (self.precedence_of(self.operator_stack[-1]) > self.precedence_of(token) or
                        (self.precedence_of(self.operator_stack[-1]) == self.precedence_of(token) and
                         token not in self.right_associative))):
                    self.output_queue.append(self.operator_stack.pop())
                self.operator_stack.append(token)
        while self.operator_stack:
            self.output_queue.append(self.operator_stack.pop())

        converted_formula = flatten_connectives(self.construct_expression_from_postfix())
        self.print_info += f"This is the tree representation of the formula {self.expression}:\n" + get_printed_tree(converted_formula,1)
        self.print_info += f"The formula is equivalent to {get_node_expression(converted_formula)}."

        if self.need_print:
            if get_node_expression(converted_formula).replace(" ", "") == self.expression:
                self.print_info = f"Trying to convert {self.expression} to strong syntax.\n"
                self.print_info += "The formula is already in strong syntax."
            print(self.print_info)

        return converted_formula


    def construct_expression_from_postfix(self):
        stack = []
        for token in self.output_queue:
            if token in self.precedence:
                if token == '¬':
                    prop = stack.pop()
                    self.print_info += "\tRemoved subtree from the stack:\n" + get_printed_tree(prop,2)
                    expression = Node("¬", children=[prop])
                    self.print_info += f"\tCreated new subtree:\n" + get_printed_tree(expression,2)
                else:
                    right = stack.pop()
                    left = stack.pop()
                    self.print_info += "\tRemoved subtrees from the stack:\n" + get_printed_tree(left,2) + "\n" + get_printed_tree(right,2)
                    expression = Node(token, children=[left, right])
                    self.print_info += f"\tCreated new subtree:\n" + get_printed_tree(expression,2)
                self.print_info += f"\tAdded {get_node_expression(expression)} to the stack.\n"
                stack.append(expression)
            else:
                self.print_info += f"\tAdded {token} to the stack.\n"
                stack.append(Node(token))
            self.print_info += (
                    f"\tThere {f"are {len(stack)} subtrees" if len(stack) > 1 else 'is one subtree'}:\n"
                    + f"{get_printed_tree(stack[0], 2)}"
                    + "".join(f"\n{get_printed_tree(subtree, 2)}" for subtree in stack[1:])
            )
        if len(stack) != 1:
            print(self.print_info)
            raise Exception(
                f"Received a different number of binary connectives than expected, could not unite subtrees:\n"
                + f"{get_printed_tree(stack[0], 2)}"
                + "".join(f"\n{get_printed_tree(subtree, 2)}" for subtree in stack[1:])
                + f"{self.expression} is not a wff.\n"
            )

        return stack[0]




try:
    with open("propositions.json", "r", encoding="utf-8") as file:
        input_file = json.load(file)
    print("Data loaded successfully:", end="\n\n")
    for element in input_file:
        try:
            proposition = element["proposition"]
            print(f"Started parsing for the proposition: {proposition}")
            if "⊨" in proposition:
                print("Identified a possible consequence as a string.")
                parts = proposition.replace(" ", "").split("⊨")
                left = parts[0].split(",")
                left_prop = "(" + "∧".join(f"({lft})" for lft in left) + ")"
                prop = f"({left_prop}⇒{parts[1]})"
                print(f"The proposition should be equivalent to: {prop}")

                root = convert_from_relaxed(prop)

                truth_table = generate_truth_table(root)
                print("Checking if it is true for all possible interpretations:")
                print_truth_table(root, truth_table)

                if is_valid(root):
                    print(f"The proposition is true for all possible interpretations; therefore, "
                            f"{parts[1]} is a logical consequence of {', '.join(str(elem) for elem in left)}.")
                else:
                    print(f"The proposition is NOT true for all possible interpretations; therefore, "
                            f"{parts[1]} is NOT a logical consequence of {', '.join(str(elem) for elem in left)}.")

            elif "∼" in proposition:
                print("Identified a possible equivalence as a string.")
                parts = [convert_from_relaxed(prop) for prop in proposition.split("∼")]
                for prop in parts[1:]:
                    if not compare_truth_tables(parts[0], prop):
                        print("The formulas are NOT equivalent.")
                        break

            else:
                convert_from_relaxed(proposition)
                print("The string is a wwf.\n")

        except Exception as e:
            print(f"Error: {e}")
        except KeyError:
            print("Proposition not found. Please ensure each element has a 'proposition' key.")
        print(end="\n\n")
except FileNotFoundError:
    print("File not found. Ensure 'propositions.json' is in the correct directory.")
except json.JSONDecodeError:
    print("Failed to decode JSON. Ensure the JSON syntax is correct.")
except Exception as e:
    print("An error occurred:", e)