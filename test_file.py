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

from nutree import Tree, Node
tree = Tree("")
tree.add("asd")
print(tree.children[0].name)
print(tree.format())
