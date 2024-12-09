from utility import *
from anytree import Node
import re


def format_language(inp):
    def get_category_content(input_str, category):
        pattern = rf"{category}\s*=\s*\{{([^}}]+)\}}"
        match = re.search(pattern, input_str)
        if match:
            items = match.group(1).split(", ")
            return items
        return []
    lang = {
        "functions": {elem.split("/")[0]: int(elem.split("/")[1]) for elem in get_category_content(inp, "Functions")},
        "predicates": {elem.split("/")[0]: int(elem.split("/")[1]) for elem in get_category_content(inp, "Predicates")},
        "constants": get_category_content(inp, "Constants")
    }
    return lang


def is_variable(var):
    if not var[0].isalpha():
        return False
    for i in range(1, len(var)):
        if not var[i].isdigit():
            return False
    return True


class FirstOrderPredicateLogicParser:
    def __init__(self, expression, lang):
        self.proposition = expression.replace(" ", "")
        self.index = 0
        self.length = len(self.proposition)
        self.functions = lang["functions"]
        self.predicates = lang["predicates"]
        self.constants = lang["constants"]
        self.errors = ""


    def current_chr(self):
        return self.proposition[self.index] if self.index < self.length else None


    def expression_type(self, node):
        if node.name in ['∧', '∨', '⇒', '⇔'] or node.name in self.predicates:
            return "The expression is a formula."
        if node.name in self.functions or node.name in self.constants or is_variable(node.name):
            return "The expression is a term."
        if node.name in ['∀', '∃']:
            return "The expression is a quantifier."
        return "The expression is unknown."


    def parse_constant(self):
        char = self.current_chr()
        if char in self.constants and (char.islower() or char.isdigit()):
            var = char
            self.index += 1
            while self.index < self.length and self.proposition[self.index].isdigit():
                var += self.proposition[self.index]
                self.index += 1
            print(f"\tFound constant: {var}")
            node = Node(var)
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        return None


    def parse_variable(self):
        char = self.current_chr()
        if char.islower() and char not in self.constants:
            var = char
            self.index += 1
            while self.index < self.length and self.proposition[self.index].isdigit():
                var += self.proposition[self.index]
                self.index += 1
            print(f"\tFound variable: {var}")
            node = Node(var)
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        return None


    def parse_function(self):
        start = self.index
        char = self.current_chr()
        self.index += 1
        while self.index < self.length and self.proposition[self.index].isalpha():
            char += self.proposition[self.index]
            self.index += 1
        if char in self.functions:
            print(f"\tFound function: {char}")
            node = Node(char)
            if self.current_chr() == '(':
                self.index += 1
                children = []
                arity = self.functions[char]
                for i in range(arity):
                    if self.current_chr() == ')':
                        self.index = start
                        self.errors += f"Unexpected closing parenthesis. Expected {arity} arguments.\n"
                        return
                    child = (self.parse_function() or self.parse_variable() or self.parse_constant())
                    if not child:
                        self.index = start
                        self.errors += f"Invalid argument for function '{char}'."
                        return
                    children.append(child)
                    if i < arity - 1:
                        if self.current_chr() == ',':
                            self.index += 1
                        else:
                            self.index = start
                            self.errors += f"Expected ',' between arguments of function '{char}'."
                            return
                node.children = children
                if self.current_chr() == ')':
                    self.index += 1
                else:
                    self.index = start
                    self.errors += f"Expected closing parenthesis after function '{char}'."
                    return
                print("\tCurrent subtree representation:")
                print_tree(node, 2)
                return node
            else:
                self.index = start
                self.errors += "Parenthesis expected after function."
                return
        else:
            self.index = start
        return None


    def get_predicate(self):
        l = []
        index = self.index
        char = self.current_chr()
        if not char.isalpha() and char in self.predicates:
            return char
        index += 1
        while index < self.length and self.proposition[index].isalpha():
            if char in self.predicates:
                l.append(char)
            char += self.proposition[index]
            index += 1
        if l:
            self.index += len(l[-1]) - 1
            return l[-1]
        else:
            return None


    def parse_predicate(self):
        return self.predicate_first() or self.predicate_inside() or self.predicate_last()


    def predicate_first(self):
        start = self.index
        char = self.get_predicate()
        self.index += 1
        if char in self.predicates:
            print(f"\tFound predicate: {char}")
            node = Node(char)
            if self.current_chr() == '(':
                self.index += 1
                children = []
                arity = self.predicates[char]
                for i in range(arity):
                    if self.current_chr() == ')':
                        self.index = start
                        self.errors += f"Unexpected closing parenthesis. Expected {arity} arguments."
                        return
                    child = self.parse_function() or self.parse_variable() or self.parse_constant()
                    if not child:
                        self.index = start
                        self.errors += f"Invalid argument for predicate '{char}'."
                        return
                    children.append(child)
                    if i < arity - 1:
                        if self.current_chr() == ',':
                            self.index += 1
                        else:
                            self.index = start
                            self.errors += f"Expected ',' between arguments of predicate '{char}'."
                            return
                node.children = children
                if self.current_chr() == ')':
                    self.index += 1
                else:
                    self.index = start
                    self.errors += f"Expected closing parenthesis after predicate '{char}'."
                    return
                print("\tCurrent subtree representation:")
                print_tree(node, 2)
                return node
            else:
                self.index = start
                self.errors += "Parenthesis expected after predicate."
                return
        else:
            self.index = start
        return None


    def predicate_inside(self):
        start = self.index
        expect_closing = False
        if self.current_chr() == '(':
            expect_closing = True
            self.index += 1
        child1 = self.parse_function() or self.parse_variable() or self.parse_constant()
        if not child1:
            self.index = start
            self.errors += f"Invalid child."
            return
        pred = self.get_predicate()
        self.index += 1
        if pred not in self.predicates:
            self.index = start
            self.errors += f"Not predicate."
            return
        print(f"\tFound predicate: {pred}")
        if self.predicates[pred] != 2:
            self.index = start
            self.errors += f"Arity different than 2."
            return
        child2 = self.parse_function() or self.parse_variable() or self.parse_constant()
        if not child2:
            self.index = start
            self.errors += f"Invalid child."
            return
        if expect_closing:
            if self.current_chr() == ')':
                self.index += 1
            else:
                self.index = start
                self.errors += f"Expected closing parenthesis."
                return
        node = Node(pred, children=[child1, child2])
        print("\tCurrent subtree representation:")
        print_tree(node, 2)
        return node


    def predicate_last(self):
        start = self.index
        if self.current_chr() == '(':
            self.index += 1
            children = []
            while self.index < self.length:
                child = (self.parse_function() or self.parse_variable() or self.parse_constant())
                if not child:
                    self.index = start
                    self.errors += f"Invalid argument."
                    return
                children.append(child)
                if self.current_chr() == ')':
                    break
                if self.current_chr() == ',':
                    self.index += 1
                else:
                    self.index = start
                    self.errors = "Expected comma between arguments."
                    return
            self.index += 1
            pred = self.get_predicate()
            self.index += 1
            if pred not in self.predicates:
                self.index = start
                self.errors += f"Not predicate."
                return
            if self.predicates[pred] != len(children):
                self.index = start
                self.errors += f"Arity is {self.predicates[pred]}, but received {len(children)} arguments."
                return
            node = Node(pred, children=children)
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        else:
            child = self.parse_function() or self.parse_variable() or self.parse_constant()
            if not child:
                self.index = start
                self.errors += f"Invalid argument."
                return
            pred = self.get_predicate()
            self.index += 1
            if pred not in self.predicates:
                self.index = start
                self.errors += f"Not predicate."
                return
            if self.predicates[pred] != 1:
                self.index = start
                self.errors += f"Arity should be 1."
                return
            node = Node(pred, children=[child])
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node


    def parse_quantifier(self):
        start = self.index
        char = self.current_chr()
        if char in ['∀', '∃']:
            print(f"\tFound quantifier: {char}")
            self.index += 1
            left = self.parse_variable()
            if not left:
                self.index = start
                self.errors += f"Expected variable after quantifier '{char}'."
                return
            right = self.parse_unary() or self.parse_binary() or self.parse_quantifier() or self.parse_predicate()
            if not right:
                self.index = start
                self.errors += f"Invalid expression after quantifier '{char}'."
                return
            node = Node(char, children=[left, right])
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        return None


    def parse_unary(self):
        start = self.index
        char = self.current_chr()
        if char == "(" and self.proposition[self.index + 1] == '¬':
            self.index += 2
            print("\tFound unary connective: ¬")
            child = self.parse_unary() or self.parse_binary() or self.parse_quantifier() or self.parse_predicate()
            if not child:
                self.index = start
                self.errors += f"Invalid expression after negation."
                return
            node = Node("¬", children=[child])
            if self.current_chr() == ')':
                self.index += 1
            else:
                self.index = start
                self.errors += "Expected closing parenthesis after negation."
                return
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        return None


    def parse_binary(self):
        start = self.index
        char = self.current_chr()
        if char == '(':
            self.index += 1
            left = self.parse_unary() or self.parse_binary() or self.parse_quantifier() or self.parse_predicate()
            if not left:
                self.index = start
                self.errors += f"Invalid expression before connective."
                return
            connective = self.current_chr()
            if connective not in ['∧', '∨', '⇒', '⇔']:
                self.index = start
                self.errors += f"Expected a binary connective, found '{connective}' instead."
                return
            self.index += 1
            right = self.parse_unary() or self.parse_binary() or self.parse_quantifier() or self.parse_predicate()
            if not left:
                self.index = start
                self.errors += f"Invalid expression before binary connective '{connective}'."
                return
            if not right:
                self.index = start
                self.errors += f"Invalid expression after binary connective '{connective}'."
                return
            node = Node(connective, children=[left, right])
            if self.current_chr() == ')':
                self.index += 1
            else:
                self.index = start
                self.errors += "Expected closing parenthesis after binary expression."
                return
            print("\tCurrent subtree representation:")
            print_tree(node, 2)
            return node
        return None


    def parse_expression(self):
        return (
                self.parse_predicate()
                or self.parse_unary()
                or self.parse_binary()
                or self.parse_quantifier()
                or self.parse_function()
                or self.parse_constant()
                or self.parse_variable()
        )


    def parse(self):
        print(f"Parsing the following string: {self.proposition}")
        rt = self.parse_expression()
        if rt and self.index == self.length:
            print(f"The proposition {self.proposition} is a expression of first order predicate logic over the specified language.")
            return rt
        else:
            raise SyntaxError("Invalid formula.")



# propositions = [
#     "c",
#     "h",
#     "(P ∧ Q)",
#     "P(f(x, a), g(h(c, a, g(y, z)))",
#     "f(g(f(a, h(b, g(x, y)))), Q(a, x))",
#     "∀x((P(x, y) ∨ (R(f(x, y), g(f(y, z)), a))) ⇒ (P(a, b) ⇔ ∃yP(x, y)))",
#     "(R(x, y, c) ∧ ∀aR(a, a, a))",
#     "(h(x, y, c) ∨ ∃xQ(x, x))",
#     "P(a, y) ⇔ ∃xR(x, y, z)",
# ]
# language = "Functions = {f/2, g/1, h/3} Predicates = {P/2, Q/2, R/3} Constants = {a, b, c}"

# propositions = [
#     "(Predicate(x, y) ∧ ∀xP(func(a), x))"
# ]
# language = "Functions = {func/1, g/1, h/3} Predicates = {Predicate/2, P/2, Q/2, R/3} Constants = {a, b, c}"

# propositions = [
#     "((a ≤ y) ⇔ (a ≤ y))",
#     "(a Predicate y)",
#     "(a Predicate y",
#     "a ≤ y",
# ]
propositions = [
    "(≤(a, y) ⇔ (a, y)≤)",
    "(a Predicate y)",
    "(a Predicate y",
    "a ≤ y ",
    "((a, y)≤ ⇔ a!)"
]
language = "Functions = {f/2, g/1, h/3} Predicates = {≤/2, P/2, Predicate/2, Q/2, R/3, !/1} Constants = {a, b, c}"

language = format_language(language)
for proposition in propositions:
    try:
        parser = FirstOrderPredicateLogicParser(proposition, language)
        root = parser.parse()
        print(parser.expression_type(root))
    except Exception as e:
        print(e)
    print(end="\n\n")



