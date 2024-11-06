import re

class ShuntingYardConverter:
    def __init__(self, expression):
        self.expression = expression.replace(" ", "")
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

    def is_operator(self, token):
        return token in self.precedence

    def precedence_of(self, token):
        return self.precedence.get(token, 0)

    def convert(self):
        print(f"Trying to convert {self.expression} to strong syntax.")
        tokens = re.findall(r"[A-Z][0-9]*|¬|∧|∨|⇒|⇔|[()]|⊤|⊥", self.expression)
        for token in tokens:
            if re.match(r"[A-Z][0-9]*|⊤|⊥", token):
                self.output_queue.append(token)
            elif token == '(':
                self.operator_stack.append(token)
            elif token == ')':
                while self.operator_stack and self.operator_stack[-1] != '(':
                    self.output_queue.append(self.operator_stack.pop())
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

        return self.construct_expression_from_postfix()

    def construct_expression_from_postfix(self):
        stack = []
        for token in self.output_queue:
            if token in self.precedence:
                if token == '¬':
                    operand = stack.pop()
                    expression = f"(¬{operand})"
                else:
                    right = stack.pop()
                    left = stack.pop()
                    if token in {'∨', '∧'} and re.search(re.escape(token), left) is not None:
                       new_left=left[1:-1]
                       expression = f"({new_left}{token}{right})"
                    else : expression = f"({left}{token}{right})"
                print(f"\tAdded {expression} to the stack.")
                stack.append(expression)
            else:
                print(f"\tAdded {token} to the stack.")
                stack.append(token)
            print(f"\tThe stack is: {stack}")
        if len(stack) != 1:
            print(f"Cannot form a wff from the stack: {stack}")
            raise Exception("Error converting from relaxed syntax to strong syntax")

        return stack[0]

# expressions = [
#     "P ∧ Q ⇒ R¬B ∨ G",
#     "P ⇒ ¬¬¬¬¬B ⇔ Q ∧ S",
#     # "P ∧ (Q ∧ R) ∧ T",
#     # "¬(P ∨ Q)",
#     # "P ⇒ Q ⇔ R",
#     # "(P ⇒ Q) ∨ ¬Q ∨ ¬P",
#     # "P ∧ Q ⇒ R¬B ∨ G",
# ]
#
# for expr in expressions:
#     try:
#         converter = ShuntingYardConverter(expr)
#         strict_syntax = converter.convert()
#         print(f"Original: {expr}\nConverted: {strict_syntax}\n\n")
#     except Exception as e:
#         print(f"{e}\n")