import re
from utility import *


def relaxed_to_strong(prp, is_strong=False, need_print=True):
    if not is_strong:
        converter = ShuntingYardConverter(prp, need_print=need_print)
        prp = converter.convert()
    return prp


class ShuntingYardConverter:
    def __init__(self, expression, need_print=False):
        self.expression = expression.replace(" ", "").replace("→", "⇒")
        self.output_queue = []
        self.operator_stack = []
        self.parenthesis = []
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


    def verify_integrity(self):
        matching = re.findall(r"[A-Z][0-9]*|¬|∧|∨|⇒|⇔|[()]|⊤|⊥.", self.expression)
        extra_parenthesis = re.findall(r"\([A-Z][0-9]*\)", self.expression)
        if self.expression == "" or self.expression is None:
            print(self.print_info, end="")
            raise Exception("Empty string is not a wff.\n\n")
        if self.expression[-1] in ["∧", "∨", "⇒", "⇔", "¬"]:
            print(self.print_info, end="")
            raise Exception(f"{self.expression[-1]} cannot be last in string.\n{self.expression} is not a wwf.\n\n")
        prop = ""
        for char in matching:
            prop += char
        if prop != self.expression:
            print(self.print_info, end="")
            raise Exception(f"Found non-matching character.")
        if self.expression.count("(") != self.expression.count(")"):
            print(self.print_info, end="")
            raise Exception(f"Different number of opening and closing parenthesis.\n{self.expression} is not a wff.\n\n")
        if extra_parenthesis:
            print(self.print_info, end="")
            raise Exception(
                f"{" ".join(elem for elem in extra_parenthesis)} "
                f"{"has" if len(extra_parenthesis) == 1 else "have"} an extra set of parenthesis.\n{self.expression} is not a wff.\n\n"
            )


    def convert(self):
        self.print_info += f"Trying to convert {self.expression} to strong syntax while checking if it is a wff.\n"
        tokens = re.findall(r"[A-Z][0-9]*|¬|∧|∨|⇒|⇔|[()]|⊤|⊥", self.expression)
        self.verify_integrity()

        for i, token in enumerate(tokens):
            if i:
                if (tokens[i - 1] in ["∧", "∨", "⇒", "⇔", "¬", "("] and token in ["∧", "∨", "⇒", "⇔", ")"]) or (tokens[i - 1] == ")" and token == "("):
                    print(self.print_info, end="")
                    raise Exception(f"Invalid {"parenthesis" if tokens[i - 1] in ["(", ")"] and token in ["(", ")"] else "connectives"} placement: "
                                    f"{tokens[i-1]} cannot be followed by {token}\n{self.expression} cannot be a wff.\n\n")
                if re.match(r"[A-Z][0-9]*|⊤|⊥", tokens[i - 1]) and re.match(r"[A-Z][0-9]*|⊤|⊥", token):
                    print(self.print_info, end="")
                    raise Exception(f"An atomic formula '{tokens[i - 1]}' cannot be followed by another atomic formula '{token}'. "
                                    f"Expected a binary connective between.\n{self.expression} is not a wff.\n\n")

            if re.match(r"[A-Z][0-9]*|⊤|⊥", token):
                self.output_queue.append(token)
            elif token == '(':
                self.parenthesis.append(i)
                self.operator_stack.append(token)
            elif token == ')':
                self.parenthesis.insert(0, (self.parenthesis.pop(), i))
                while self.operator_stack and self.operator_stack[-1] != '(':
                    self.output_queue.append(self.operator_stack.pop())
                if len(self.operator_stack) == 0 :
                    print(self.print_info, end="")
                    raise Exception(f"Valid expression expected before ).\n{self.expression} is not a wff.\n\n")
                self.operator_stack.pop()
            elif self.is_operator(token):
                while (self.operator_stack and self.operator_stack[-1] != '(' and
                       (self.precedence_of(self.operator_stack[-1]) > self.precedence_of(token) or
                        (self.precedence_of(self.operator_stack[-1]) == self.precedence_of(token) and
                         token not in self.right_associative))):
                    self.output_queue.append(self.operator_stack.pop())
                self.operator_stack.append(token)

        for pair in self.parenthesis:
            lft, rgt = pair
            if (lft - 1, rgt + 1) in self.parenthesis:
                print(self.print_info, end="")
                raise Exception(
                    f"Extra set of parenthesis at positions {lft - 1} and {rgt + 1}: "
                    f"{self.expression[lft - 1:rgt + 2]}.\n{self.expression} is not a wwf.\n\n")

        while self.operator_stack:
            self.output_queue.append(self.operator_stack.pop())

        converted_formula = flatten_connectives(self.construct_expression_from_postfix())


        if self.need_print:
            if get_node_expression(converted_formula).replace(" ", "") == self.expression:
                self.print_info += f"The formula is already in strong syntax.\n"
            self.print_info += f"This is the tree representation of the formula {self.expression}:\n" + get_printed_tree(converted_formula, 1)
            self.print_info += f"The formula is equivalent to {get_node_expression(converted_formula)}.\n"
            print(self.print_info, end="")

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
            print(self.print_info, end="")
            raise Exception(
                f"Received a different number of binary connectives than expected, could not unite subtrees:\n"
                + f"{get_printed_tree(stack[0], 2)}"
                + "".join(f"\n{get_printed_tree(subtree, 2)}" for subtree in stack[1:])
                + f"{self.expression} is not a wff.\n\n"
            )

        return stack[0]