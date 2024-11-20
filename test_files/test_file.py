# def is_wff(s):
#     if not s:
#         print(f"Error: Empty string is not a well formed propositional formula.")
#         return False  # Empty string is not a wff
#
#     if s.isalpha() and s.isupper():
#         print(f"This is an atomic well formed propositional formula: {s}")
#         return True  # Propositional variable
#     else:
#         print(f"Checking subformula: {s}")
#
#     if s[0] == "(" and s[-1] == ")":
#         s = s[1:-1]  # Remove outer parentheses
#         print(f"Removing outer parenthesis, checking subformula: {s}")
#
#         if s[0] == "¬":  # Check if the negation is followed by a valid wff
#             print(f"Negation found. Checking subformula: {s[1:]}")
#             if not is_wff(s[1:]):
#                 return False
#             return True
#
#         # Check for binary connectives
#         balance = 0
#         for i, char in enumerate(s):
#             if char == "(":
#                 balance += 1
#             if char == ")":
#                 balance -= 1
#             if char in ["∧", "∨", "⇒", "⇔"] and balance == 0:  # Check if the parts around the connector are
#                 left = s[:i]
#                 right = s[i + 1:]
#                 print(f"Binary connective '{char}' found. Checking left: '{left}' and right: '{right}'")
#                 if not is_wff(left):
#                     print(f"Error: Invalid left subformula around '{char}': {left}")
#                     return False
#                 if not is_wff(right):
#                     print(f"Error: Invalid right subformula around '{char}': {right}")
#                     return False
#                 return True
#
#     print(f"Error: Invalid structure in subformula: {s}")
#     return False
#
# # Test cases
# strings = [
#     "(((P⇒Q)∨B)⇔T)",
#     "((P⇒(Q∧(S⇒T))))",
#     "(¬(B(¬Q))∧R)",
#     "(P∧((¬Q)∧(¬(¬(Q⇔(¬R))))))",
#     "((P∨Q)⇒(¬(P∨Q)))∧(P∨(¬(¬Q)))",
#     # "((P)⇒(Q))",
#     # "((P Q))",
#     # "(P∧(Q∧))",
#     # "(P)",
#     # "(¬P)",
#     # "P∧Q",
#     # "(P ∧ (¬q))"
# ]
#
# # Test the function with each string
# for string in strings:
#     string = string.replace(" ", "")
#     print(f"Testing the following string: {string}")
#     if is_wff(string):
#         print(f"'{string}' is a well formed formula.", end="\n\n")
#     else:
#         print(f"'{string}' is NOT a well formed formula.", end="\n\n")
#




# class Parser:
#     def __init__(self, proposition, is_strong=False, need_print=True):
#         self.proposition = proposition.replace(" ", "").replace("→", "⇒")
#         self.index = 0
#         self.length = len(self.proposition)
#         self.operation_count = 0
#         self.root = None
#         self.is_equivalence = True if "∼" in self.proposition else False
#         self.is_consequence = True if "⊨" in self.proposition else False
#         self.is_strong = is_strong
#         self.need_print = need_print
#
#
#     def current_chr(self):
#         return self.proposition[self.index] if self.index < self.length else None
#
#
#     def parse_atomic(self):
#         start_index = self.index
#         char = self.current_chr()
#
#         if char in ['⊤', '⊥']:
#             self.index += 1
#             print(f"\t{char} is {'a tautology' if char == '⊤' else 'a contradiction'}, at index: {start_index}") if self.need_print else None
#             node = Node(char)
#             print("\tCurrent subtree representation:") if self.need_print else None
#             print_tree(node, 2) if self.need_print else None
#             return node
#         if char and is_chr(char):
#             atomic_proposition = char
#             self.index += 1
#
#             while self.index < self.length and self.proposition[self.index].isdigit():
#                 atomic_proposition += self.proposition[self.index]
#                 self.index += 1
#
#             print(f"\t{atomic_proposition} is an atomic {'subformula' if self.operation_count else 'formula'}, index: {start_index}") if self.need_print else None
#             node = Node(atomic_proposition)
#             print("\tCurrent subtree representation:") if self.need_print else None
#             print_tree(node, 2) if self.need_print else None
#             return node
#         return None
#
#
#     def parse_unary(self):
#         if self.current_chr() == "(" and self.proposition[self.index + 1] == "¬":
#             self.operation_count += 1
#             self.index += 1
#             print(f"\tDetected unary connective: ¬, at index: {self.index}.") if self.need_print else None
#             self.index += 1
#
#             sub_node = self.parse_expression()
#             if not sub_node:
#                 raise Exception(f"Error: Expected an expression following ¬, at index: {self.index}.")
#             if self.current_chr() != ")":
#                 raise Exception(f"Error: Expected closing parenthesis after unary expression, at index: {self.index}.")
#             self.index += 1
#             node = Node("¬", children=[sub_node])
#             print("\tCurrent subtree representation:") if self.need_print else None
#             print_tree(node, 2) if self.need_print else None
#             return node
#         return None
#
#
#     def parse_binary(self):
#         if self.current_chr() == "(":
#             self.operation_count += 1
#             self.index += 1
#
#             left_node = self.parse_expression()
#             if left_node:
#                 if self.current_chr() in ['∧', '∨', '⇒', '⇔']:
#                     connective = self.current_chr()
#                 else:
#                     raise Exception(f"Error: Expected connective, at index: {self.index}, but found {self.current_chr()}.")
#                 children = [left_node]
#                 while connective in ['∧', '∨']:
#                     print(f"\tDetected binary connective: {connective}, at index: {self.index}.") if self.need_print else None
#                     self.index += 1
#                     next_node = self.parse_expression()
#                     if next_node:
#                         children.append(next_node)
#                     else:
#                         raise Exception(f"Error: Invalid expression after {connective} connective, at index: {self.index}.")
#                     if self.current_chr() == ")":
#                         break
#                 binary_node = Node(connective, children=children)
#                 if connective in ['⇒', '⇔']:
#                     print(f"\tDetected binary connective: {connective}, at index: {self.index}.") if self.need_print else None
#                     self.index += 1
#                     right_node = self.parse_expression()
#                     if right_node:
#                         binary_node = Node(connective, children=[left_node, right_node])
#                     else:
#                         raise Exception(f"Error: Invalid expression after {connective} connective, at index: {self.index}.")
#                 if self.current_chr() == ")":
#                     self.index += 1
#                     print("\tCurrent subtree representation:") if self.need_print else None
#                     print_tree(binary_node, 2) if self.need_print else None
#                     return binary_node
#                 else:
#                     if is_chr(self.current_chr()):
#                         raise Exception(f"Error: Expecting an connective, at index: {self.index}, but found {self.current_chr()}.")
#                     else:
#                         raise Exception(f"Error: Missing closing parenthesis for {connective} operation, at index: {self.index}.")
#         return None
#
#
#     def parse_expression(self):
#         return self.parse_atomic() or self.parse_unary() or self.parse_binary()
#
#
#     def parse_proposition(self):
#         if not self.proposition:
#             raise Exception("Error: Empty proposition")
#         self.root = self.parse_expression()
#         if self.root and self.index == self.length:
#             print("The string is a well formed formula.") if self.need_print else None
#             return self.root
#         elif self.current_chr() in ['∧', '∨', '⇒', '⇔']:
#             raise Exception(f"Error: Binary operator '{self.current_chr()}' not enclosed in parentheses.")
#         elif self.current_chr() == ")" or self.current_chr() is None:
#             raise Exception("Error: Unbalanced parentheses detected.")
#         elif self.current_chr() == "¬" and self.index < self.length - 1:
#             raise Exception("Error: '¬' operator must be enclosed in parentheses.")
#         else:
#             raise Exception("Error: Invalid structure.")
#
#
#     def parse(self):
#         print(f"Starting parsing for: '{self.proposition}'") if self.need_print else None
#         if "∼" in self.proposition:
#             self.is_equivalence = True
#             parts = self.proposition.split("∼", 1)
#             left_prop, right_prop = (convert_from_relaxed(parts[0].strip(), is_strong=self.is_strong, need_print=self.need_print),
#                                      convert_from_relaxed(parts[1].strip(), is_strong=self.is_strong, need_print=self.need_print))
#
#             print(f"Parsing the string on the left of the '∼': '{left_prop}'") if self.need_print else None
#             left_parser = Parser(left_prop)
#             left_root = left_parser.parse_proposition()
#             print("Left expression tree:") if self.need_print else None
#             print_tree(left_root, 1) if self.need_print else None
#             print(check_validity(left_root)) if self.need_print else None
#
#             print(f"Parsing the string on the right of the '∼': '{right_prop}'") if self.need_print else None
#             right_parser = Parser(right_prop)
#             right_root = right_parser.parse_proposition()
#             print("Right expression tree:") if self.need_print else None
#             print_tree(right_root, 1) if self.need_print else None
#             print(check_validity(right_root)) if self.need_print else None
#
#             self.root = Node("∼", children=[left_root, right_root])
#             return self.root
#         elif "⊨" in self.proposition:
#             print("We identified that we have a possible consequence as a string.") if self.need_print else None
#             self.check_consequence(self.proposition)
#         else:
#             self.proposition = convert_from_relaxed(self.proposition, is_strong=self.is_strong, need_print=self.need_print)
#             self.length = len(self.proposition)
#             node = self.parse_proposition()
#             node = flatten_connectives(node)
#             return node
#
#
#     def check_consequence(self, string):
#         parts = string.split("⊨")
#         self.root = Node("⊨", children=[])
#         left_lst = [convert_from_relaxed(s, is_strong=self.is_strong, need_print=self.need_print) for s in parts[0].split(",")]
#         left_prop = "(" + '∧'.join(f'{op}' for op in left_lst) + ")" if len(
#             parts[0].split(",")) > 1 else convert_from_relaxed(parts[0], is_strong=self.is_strong, need_print=self.need_print)
#         right_lst = [convert_from_relaxed(s, is_strong=self.is_strong, need_print=self.need_print) for s in parts[1].split(",")]
#         right_prop = "(" + '∧'.join(f'{op}' for op in right_lst) + ")" if len(
#             parts[1].split(",")) > 1 else convert_from_relaxed(parts[1], is_strong=self.is_strong, need_print=self.need_print)
#         prop = f"({left_prop}⇒{right_prop})"
#         print(f"The proposition should be equivalent to: {prop}") if self.need_print else None
#         print("Checking if it is true for all possible interpretations:") if self.need_print else None
#
#         prs = Parser(prop, is_strong=True)
#         node = prs.parse()
#         print_truth_table(node)
#         truth_table = generate_truth_table(node)
#         prop_header = get_all_nodes(node)[-1]
#
#         all_true = True
#         for idx, row in enumerate(truth_table):
#             if not row[prop_header]:
#                 all_true = False
#                 print(f"Failed case at row {idx + 1}:") if self.need_print else None
#                 print(f"Interpretation: {row}") if self.need_print else None
#                 break
#
#         if all_true:
#             print(f"The proposition is true for all possible interpretations; therefore, "
#                   f"{', '.join(str(elem) for elem in right_lst)} is a logical consequence of "
#                   f"{', '.join(str(elem) for elem in left_lst)}.") if self.need_print else None
#         else:
#             print(f"The proposition is NOT true for all possible interpretations; therefore, "
#                   f"{', '.join(str(elem) for elem in right_lst)} is NOT a logical consequence of "
#                   f"{', '.join(str(elem) for elem in left_lst)}.") if self.need_print else None