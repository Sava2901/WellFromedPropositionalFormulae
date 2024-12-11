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
        "functions": {elem[0:elem.rindex("/")]: int(elem[elem.rindex("/")+1:len(elem)]) for elem in get_category_content(inp, "Functions")},
        "predicates": {elem.split("/")[0]: int(elem.split("/")[1]) for elem in get_category_content(inp, "Predicates")},
        "constants": get_category_content(inp, "Constants")
    }
    return lang


import re

def add_invisible_multiplication(expression):
    patterns = [
        (r'([a-z])(\d)', r'\1*\2'),
        (r'(\d)([a-z])', r'\1*\2'),
        (r'([a-z])([a-z])', r'\1*\2'),
        (r'([a-z])\(', r'\1*('),
        (r'\)([a-z])', r')*\1'),
        (r'(\d)\(', r'\1*('),
        (r'\)(\d)', r')*\1'),
        (r'([a-z]|\d)(√)', r'\1*\2'),
    ]
    while True:
        new_expression = expression
        for pattern, replacement in patterns:
            new_expression = re.sub(pattern, replacement, new_expression)
        if new_expression == expression:
            break
        expression = new_expression
    expression = re.sub(
        r'([∀∃])([a-z])\*',
        lambda m: m.group(1) + m.group(2),
        expression
    )
    expression = re.sub(
        r'([a-z])\*(\d)',
        lambda m: m.group(1) + m.group(2) if m.group(2) == '1' else m.group(1) + '*' + m.group(2),
        expression
    )
    return expression


def rewrite_operation(expression, operator):
    expression = expression.replace(" ", "")
    replacement_format = f"{operator}""({0},{1})"
    pattern = fr'(\(([^()]+)\)|\w+|\d+)\s*\{operator}\s*(\(([^()]+)\)|\w+|\d+)'
    print(re.findall(pattern, expression))
    while True:
        new_expression = re.sub(pattern, lambda match: replacement_format.format(match.group(1), match.group(3)), expression)
        if new_expression == expression:
            break
        expression = new_expression
    return expression


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
        self.print_info = ""


    def current_chr(self):
        return self.proposition[self.index] if self.index < self.length else None


    def expression_type(self, node):
        if node.name in ['∧', '∨', '⇒', '⇔'] or node.name in self.predicates:
            return "The expression is a formula."
        if node.name in self.functions or node.name in self.constants or is_variable(node.name) or node.name.isnumeric():
            return "The expression is a term."
        if node.name in ['∀', '∃']:
            return "The expression is a quantifier."
        return "The expression is unknown."


    def reset(self, index, print_info, error_message):
        self.index = index
        self.print_info = print_info
        self.errors += error_message


    def parse_constant(self):
        char = self.current_chr()
        if (char in self.constants and char.islower()) or char.isdigit():
            var = char
            self.index += 1
            while self.index < self.length and self.proposition[self.index].isdigit():
                var += self.proposition[self.index]
                self.index += 1
            self.print_info += f"\tFound constant: {var}\n"
            node = Node(var)
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
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
            self.print_info += f"\tFound variable: {var}\n"
            node = Node(var)
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            return node
        return None


    def get_function(self):
        l = []
        index = self.index
        char = self.current_chr()
        if not char.isalpha() and char in self.functions:
            return char
        index += 1
        while index < self.length and self.proposition[index - 1].isalpha():
            if char in self.functions:
                l.append(char)
            char += self.proposition[index]
            index += 1
        if l:
            self.index += len(l[-1]) - 1
            return l[-1]
        else:
            return None


    def parse_function(self):
        return self.function_first() or self.function_chain()


    def function_first(self):
        prev_print = self.print_info
        start = self.index
        char = self.get_function()
        self.index += 1
        if char in self.functions:
            self.print_info += f"\tFound function: {char}\n"
            node = Node(char)
            if self.current_chr() == '(':
                self.index += 1
                children = []
                arity = self.functions[char]
                for i in range(arity):
                    if self.current_chr() == ')':
                        self.reset(start, prev_print, f"Unexpected closing parenthesis. Expected {arity} arguments.\n")
                        return
                    child = (self.parse_function() or self.parse_variable() or self.parse_constant())
                    if not child:
                        self.reset(start, prev_print, f"")
                        return
                    children.append(child)
                    if i < arity - 1:
                        if self.current_chr() == ',':
                            self.index += 1
                        else:
                            self.reset(start, prev_print, f"")
                            return
                node.children = children
                if self.current_chr() == ')':
                    self.index += 1
                else:
                    self.reset(start, prev_print, f"")
                    return
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                return node
            else:
                self.reset(start, prev_print, f"")
                return
        else:
            self.index = start
        return None


    def handle_parenthesis(self):
        prev_print = self.print_info
        start = self.index
        self.index += 1
        node = self.function_chain()
        if not node:
            self.reset(start, prev_print, f"")
            return
        if self.current_chr() != ')':
            self.reset(start, prev_print, f"")
            return
        self.index += 1
        return node


    def function_chain(self):
        prev_print = self.print_info
        start = self.index
        if self.current_chr() == '(':
            node = self.handle_parenthesis()
        else:
            node = self.function_first() or self.parse_variable() or self.parse_constant()
        if not node:
            self.reset(start, prev_print, f"")
            return
        while self.index < self.length:
            if self.current_chr() in [')', ',']:
                return node
            pred = self.get_predicate()
            if pred:
                self.print_info += f"\tFound predicate: {pred}\n"
                self.index += 1
                child = self.parse_function() or self.parse_variable() or self.parse_constant()
                if not child:
                    self.reset(start, prev_print, f"")
                    return
                node = Node(pred, children=[node, child])
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                return node
            func = self.get_function()
            if not func:
                self.reset(start, prev_print, f"")
                return
            self.index += 1
            self.print_info += f"\tFound function: {func}\n"
            if self.current_chr() == ')':
                self.reset(start, prev_print, f"")
                return
            child = self.parse_function() or self.parse_variable() or self.parse_constant()
            if not child:
                self.reset(start, prev_print, f"")
                return
            if child.name in self.predicates:
                temp = child.children[0]
                node = Node(func, children=[node, temp])
                node = Node(child.name, children=[node, child.children[0]])
            else:
                node = Node(func, children=[node, child])
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
        return node


    def get_predicate(self):
        l = []
        index = self.index
        char = self.current_chr()
        if not char.isalpha() and char in self.predicates:
            return char
        index += 1
        while index < self.length and self.proposition[index - 1].isalpha():
            if char in self.predicates:
                l.append(char)
            char += self.proposition[index]
            index += 1
        if char in self.predicates:
            l.append(char)
        if l:
            self.index += len(l[-1]) - 1
            return l[-1]
        else:
            return None


    def parse_predicate(self):
        return self.predicate_first() or self.predicate_inside() or self.predicate_last()


    def predicate_first(self):
        prev_print = self.print_info
        start = self.index
        char = self.get_predicate()
        self.index += 1
        if char in self.predicates:
            self.print_info += f"\tFound predicate: {char}\n"
            node = Node(char)
            if self.current_chr() == '(':
                self.index += 1
                children = []
                arity = self.predicates[char]
                for i in range(arity):
                    if self.current_chr() == ')':
                        self.reset(start, prev_print, f"")
                        return
                    child = self.parse_function() or self.parse_variable() or self.parse_constant()
                    if not child:
                        self.reset(start, prev_print, f"")
                        return
                    children.append(child)
                    if i < arity - 1:
                        if self.current_chr() == ',':
                            self.index += 1
                        else:
                            self.reset(start, prev_print, f"")
                            return
                node.children = children
                if self.current_chr() == ')':
                    self.index += 1
                else:
                    self.reset(start, prev_print, f"")
                    return
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                return node
            else:
                self.reset(start, prev_print, f"")
                return
        else:
            self.index = start
        return None


    def predicate_inside(self):
        prev_print = self.print_info
        start = self.index

        node = self.parse_function()
        if node and node.name in self.predicates:
            return node
        else:
            self.index = start

        expect_closing = False
        if self.current_chr() == '(':
            expect_closing = True
            self.index += 1
        child1 = self.parse_function() or self.parse_variable() or self.parse_constant()
        if not child1:
            self.reset(start, prev_print, f"")
            return
        pred = self.get_predicate()
        self.index += 1
        if pred not in self.predicates:
            self.reset(start, prev_print, f"")
            return
        self.print_info += f"\tFound predicate: {pred}\n"
        if self.predicates[pred] != 2:
            self.reset(start, prev_print, f"")
            return
        child2 = self.parse_variable() or self.parse_constant() or self.parse_function()
        if not child2:
            self.reset(start, prev_print, f"")
            return
        if expect_closing:
            if self.current_chr() == ')':
                self.index += 1
            else:
                self.reset(start, prev_print, f"")
                return
        node = Node(pred, children=[child1, child2])
        self.print_info += "\tCurrent subtree representation:\n"
        self.print_info += get_printed_tree(node, 2)
        return node


    def predicate_last(self):
        prev_print = self.print_info
        start = self.index
        if self.current_chr() == '(':
            self.index += 1
            children = []
            while self.index < self.length:
                child = (self.parse_function() or self.parse_variable() or self.parse_constant())
                if not child:
                    self.reset(start, prev_print, f"")
                    return
                children.append(child)
                if self.current_chr() == ')':
                    break
                if self.current_chr() == ',':
                    self.index += 1
                else:
                    self.reset(start, prev_print, f"")
                    return
            self.index += 1
            pred = self.get_predicate()
            if self.index < self.length:
                self.index += 1
            if pred not in self.predicates:
                self.reset(start, prev_print, f"")
                return
            if self.predicates[pred] != len(children):
                self.reset(start, prev_print, f"")
                return
            node = Node(pred, children=children)
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            return node
        else:
            child = self.parse_function() or self.parse_variable() or self.parse_constant()
            if not child:
                self.reset(start, prev_print, f"")
                return
            pred = self.get_predicate()
            self.index += 1
            if pred not in self.predicates:
                self.reset(start, prev_print, f"")
                return
            if self.predicates[pred] != 1:
                self.reset(start, prev_print, f"")
                return
            node = Node(pred, children=[child])
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            return node


    def parse_quantifier(self):
        prev_print = self.print_info
        start = self.index
        char = self.current_chr()
        if char in ['∀', '∃']:
            self.print_info += f"\tFound quantifier: {char}\n"
            self.index += 1
            left = self.parse_variable()
            if not left:
                self.reset(start, prev_print, f"")
                return
            right = self.parse_unary() or self.parse_binary() or self.parse_quantifier() or self.parse_predicate()
            if not right:
                self.reset(start, prev_print, f"")
                return
            node = Node(char, children=[left, right])
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            return node
        return None


    def parse_unary(self):
        prev_print = self.print_info
        start = self.index
        char = self.current_chr()
        if char == "(" and self.proposition[self.index + 1] == '¬':
            self.index += 2
            self.print_info += "\tFound unary connective: ¬\n"
            child = self.parse_unary() or self.parse_binary() or self.parse_quantifier() or self.parse_predicate()
            if not child:
                self.reset(start, prev_print, f"")
                return
            node = Node("¬", children=[child])
            if self.current_chr() == ')':
                self.index += 1
            else:
                self.reset(start, prev_print, f"")
                return
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            return node
        return None


    def parse_binary(self):
        prev_print = self.print_info
        start = self.index
        char = self.current_chr()
        if char == '(':
            self.index += 1
            left = self.parse_unary() or self.parse_binary() or self.parse_quantifier() or self.parse_predicate()
            if not left:
                self.reset(start, prev_print, f"")
                return
            connective = self.current_chr()
            if connective not in ['∧', '∨', '⇒', '⇔']:
                self.reset(start, prev_print, f"")
                return
            self.print_info += f"\tFound connective: {connective}\n"
            self.index += 1
            right = self.parse_unary() or self.parse_binary() or self.parse_quantifier() or self.parse_predicate()
            if not left:
                self.reset(start, prev_print, f"")
                return
            if not right:
                self.reset(start, prev_print, f"")
                return
            if self.current_chr() == ')':
                self.index += 1
            else:
                self.reset(start, prev_print, f"")
                return
            node = Node(connective, children=[left, right])
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            return node
        return None


    def parse_expression(self):
        return (
                self.parse_unary()
                or self.parse_binary()
                or self.parse_quantifier()
                or self.parse_function()
                or self.parse_predicate()

                or self.parse_constant()
                or self.parse_variable()
        )


    def parse(self):
        print(f"Parsing the following string: {self.proposition}")
        rt = self.parse_expression()
        if rt and self.index == self.length:
            print(self.print_info, end="")
            print(f"The proposition {self.proposition} is a expression of first order predicate logic over the specified language.")
            return rt
        else:
            print(self.errors, end="")
            raise SyntaxError("Invalid formula.")


propositions = [
    # "(≤(1, y) ⇔ (a, y)≤)",
    # "(func(x, y) Predicate y)",
    # "(a Predicate y",
    # "a ≤ y ",
    # "((f(x, y), y)≤ ⇔ a P y)",
    # "a + b",
    # "(8x − 5) + 7 ≥ (3 − 5x ⇔ y > 8z)",
    # "8 * x - 5",
    # "(8 * x - 5 + f(x,y)) + 7",
    # "(8 * x - 5 + f(x,y)) + f(x,y)",
    # "(8 * (x - 5) + f(x,y)) + (7 + f(x,y)) + (7 + f(x,y))",
    # "(8 * (x - 5) + f(x,y))",
    # "8 * (x - 5) + f(x,y)",
    # "P((2+5-f(x,y)), a)",
    # "(((8 * x - 5 + f(x,y)) + (7 + f(x,y)), a)P ⇔ P((8 * x - 5 + f(x,y)) + (7 + f(x,y)), a))",
    # "2+5-f(x,y) Predicate a",
    # "(8 * (x - 5)) Predicate x",
    # "(2+5-f(x,y))",
    # "((8 * x - 5) ≥ 7 ⇔ 3 - 5 * x > 8 * z)",
    # "(¬(x − y < x^2 + y * √(z)))",
    # "∃z((5 + 1) * y = 5*x/y^2)",
    # "∀x(x + 1 > 2)",

    "4",
    "(8*x − 5) + 7 ≥ (3 − 5*x ⇔ y > 8*z)",
    "((¬(x − y < x^2 + y * √(z)))∧∃z((5 + 1) * y = 5*x/y^2))",
    "∀x((x + 1/(x^2 + 5) > (x^3 + 5*x + 11)/(1+(x − 8)/(x^4 − 1)))",
    "((¬P(x, y))   ⇔   ∀x∃y∀z((P(y, z)∨Q(x, y, z))⇒(R(x, z, y)∨(¬P(x, z)))))",
]
language = "Functions = {f/2, func/2, g/1, h/3, +/2, */2, !/1, -/2, −/2, ^/2, √/1, //2} Predicates = {≤/2, P/2, Predicate/2, Q/3, R/3, isEven/1, ≥/2, >/2, </2, =/2} Constants = {a, b, c}"
language = format_language(language)
for proposition in propositions:
    try:
        parser = FirstOrderPredicateLogicParser(proposition, language)
        root = parser.parse()
        print(parser.expression_type(root))
    except Exception as e:
        print(e)
    print(end="\n\n")
