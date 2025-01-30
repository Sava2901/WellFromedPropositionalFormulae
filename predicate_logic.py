from utility import *


def format_language(lang):
    for element in lang:
        if element == "Functions":
            for item, details in lang[element].items():
                if not "arity" in details:
                    raise Exception(f"Missing arity for {item}.")
                if not "type" in details:
                    raise Exception(f"Missing type for {item}.")
                if not "associativity" in details:
                    lang[element][item].update({"associativity":"left"})
                if "precedence" not in lang[element][item]:
                    lang[element][item]["precedence"] = 0
        if element == "Connectives":
            for item, details in lang[element].items():
                if "precedence" not in lang[element][item]:
                    lang[element][item]["precedence"] = 0
    return lang


def format_replacements(repl, lang):
    replace = dict()
    for r in repl:
        r = r.replace(" ", "").split("=")
        replace.update({r[0]: {}})
        for elem in r[1].strip("{}").split(","):
            elem = elem.split("←")
            prs1 = FirstOrderPredicateLogicParser(elem[0], lang, False)
            prs2 = FirstOrderPredicateLogicParser(elem[1], lang, False)
            replace[r[0]].update({prs1.parse(): prs2.parse()})
    return replace


def is_variable(var):
    if not var[0].isalpha():
        return False
    for i in range(1, len(var)):
        if not var[i].isdigit():
            return False
    return True


def get_category(name, lang):
    if name in lang["Connectives"]:
        return "Connective"
    elif name in lang["Functions"]:
        return "Function"
    elif name in lang["Predicates"]:
        return "Predicate"
    elif name in lang["Quantifiers"]:
        return "Quantifier"
    else:
        return None


def get_precedence(name, lang):
    category = get_category(name, lang)
    if category == "Connective":
        return lang["Connectives"][name].get("precedence", 0)
    elif category == "Function":
        return lang["Functions"][name].get("precedence", 0)
    elif category == "Predicate":
        pred_info = lang["Predicates"][name]
        return pred_info.get("precedence", 0) if pred_info["type"] == "infix" else -1
    elif category == "Quantifier":
        return lang["Quantifiers"][name].get("precedence", -2)
    else:
        return -1


def get_associativity(name, lang):
    category = get_category(name, lang)
    if category == "Connective":
        return lang["Connectives"][name].get("associativity", "left")
    elif category == "Function":
        return lang["Functions"][name].get("associativity", "left")
    elif category == "Predicate" and lang["Predicates"][name]["type"] == "infix":
        return lang["Predicates"][name].get("associativity", "left")
    else:
        return "left"


def get_arity(item, lang):
    if item in lang["Functions"]:
        return lang["Functions"][item]["arity"]
    if item in lang["Predicates"]:
        return lang["Predicates"][item]["arity"]
    if item in lang["Connectives"]:
        return lang["Connectives"][item]["arity"]
    return None


def get_type(item, lang):
    if item in lang["Functions"]:
        return lang["Functions"][item]["type"]
    if item in lang["Predicates"]:
        return lang["Predicates"][item]["type"]
    if item in lang["Connectives"]:
        return lang["Connectives"][item]["type"]
    return None


def get_elements_type(node, lang, processed=None):
    if processed is None:
        processed = set()
    for children in node.children:
        get_elements_type(children, lang, processed)
    if node.name not in processed:
        if node.name in lang["Functions"]:
            print(f"{node.name} is a function.")
        elif node.name in lang["Predicates"]:
            print(f"{node.name} is a predicate.")
        elif node.name in ['∀', '∃']:
            print(f"{node.name} is a quantifier.")
        elif node.name in ['∧', '∨', '⇒', '⇔', '¬']:
            print(f"{node.name} is a connective.")
        elif node.name in lang["Constants"] or node.name.isnumeric():
            print(f"{node.name} is a constant.")
        elif is_variable(node.name):
            print(f"{node.name} is a variable.")
        else:
            print(f"{node.name} is not yet defined.")
        processed.add(node.name)


def expression_type(node, lang):
    if node.name in ['∧', '∨', '⇒', '⇔', '¬'] or node.name in lang["Predicates"]:
        return "The expression is a formula."
    if node.name in lang["Functions"] or node.name in lang["Constants"] or is_variable(node.name) or node.name.isnumeric():
        return "The expression is a term."
    if node.name in ['∀', '∃']:
        return "The expression is a quantifier."
    return "The expression is unknown."


def tree_to_formula(node):
    if not node.children:
        return str(node.name)
    children = [tree_to_formula(child) for child in node.children]
    if node.name == "□□":
        return "".join(children)
    logical_connectives = {"∧", "∨", "⇒", "⇔"}
    negation = "¬"
    quantifiers = {"∀", "∃"}

    if node.name in quantifiers:
        bound_variable = children[0]
        formula = children[1]
        return f"{node.name}{bound_variable}{formula}"
    elif node.name == negation:
        return f"({negation}{children[0]})"
    elif node.name in logical_connectives:
        return f"({children[0]} {node.name} {children[1]})"
    elif get_type(node.name, language) == "prefix":
        return f"{node.name}({', '.join(children)})" if len(children) > 1 else f"{node.name}{children[0]}"
    elif get_type(node.name, language) == "infix":
        return f"({children[0]} {node.name} {children[1]})"
    elif get_type(node.name, language) == "postfix":
        return f"({children[0]}{node.name})"
    else:
        return f"{node.name}({', '.join(children)})" if children else str(node.name)


def correct_precedence(node, lang):
    def is_infix(name):
        category = get_category(name, lang)
        if category == "Connective":
            return lang["Connectives"][name]["type"] == "infix"
        elif category == "Function":
            return lang["Functions"][name]["type"] == "infix"
        elif category == "Predicate":
            return lang["Predicates"][name]["type"] == "infix"
        return False

    def restructure(node):
        for child in node.children:
            restructure(child)

        node_category = get_category(node.name, lang)
        if node_category is None:
            return node

        if (is_infix(node.name) or node.name in lang["Quantifiers"]) and len(node.children) == 2:
            left, right = node.children
            left_precedence = get_precedence(left.name, lang)
            right_precedence = get_precedence(right.name, lang)
            node_precedence = get_precedence(node.name, lang)

            if (get_category(node.name, lang) == get_category(left.name, lang) and
                    node_precedence > left_precedence and get_type(left.name, lang) in ["prefix"] and len(left.children) == 1):
                if left.in_parenthesis:
                    return node

                rotated_node = Node(
                    left.name,
                    children=[Node(node.name, children=[left.children[0], right])],
                    in_parenthesis=node.in_parenthesis
                )
                if node.parent:
                    node.parent.children = [rotated_node if child == node else child for child in node.parent.children]
                else:
                    node = rotated_node
                restructure(rotated_node)
                return node

            if (
                    ( get_category(node.name, lang) == get_category(right.name, lang) or
                     (get_category(node.name, lang) in ["Quantifier"] and get_category(right.name, lang) in ["Connective"]) )
                    and
                    ( node_precedence > right_precedence or (node_precedence == right_precedence and get_associativity(node.name, lang) == "left") )
            ):
                if right.in_parenthesis:
                    return node

                new_left = duplicate_node(left)
                new_right = duplicate_node(right.children[0])

                if is_infix(right.name):
                    rotated_node = Node(
                        right.name,
                        children=[
                            Node(node.name, children=[new_left, new_right]),
                            *right.children[1:]
                        ],
                        in_parenthesis=node.in_parenthesis
                    )
                    if node.parent:
                        node.parent.children = [rotated_node if child == node else child for child in node.parent.children]
                    else:
                        node = rotated_node
                    restructure(rotated_node)
                    return node

                elif not is_infix(right.name) and len(right.children) == 1 and right.name not in lang["Connectives"]:
                    rotated_node = Node(
                        right.name,
                        children=[
                            Node(node.name, children=[new_left, new_right])
                        ],
                        in_parenthesis=node.in_parenthesis
                    )
                    if node.parent:
                        node.parent.children = [rotated_node if child == node else child for child in node.parent.children]
                    else:
                        node = rotated_node
                    restructure(rotated_node)
                    return node

        elif not is_infix(node.name) and len(node.children) == 1:
            child = node.children[0]
            node_precedence = get_precedence(node.name, lang)
            child_precedence = get_precedence(child.name, lang)

            if not is_infix(child.name) and len(child.children) == 1 and node_precedence > child_precedence:
                node.name, child.name = (child.name, node.name)

            return node

        return node

    return restructure(node)


class FirstOrderPredicateLogicParser:
    def __init__(self, expression, lang, need_print=True):
        self.proposition = expression.replace(" ", "")
        self.index = 0
        self.length = len(self.proposition)
        self.connectives = lang["Connectives"]
        self.predicates = sorted(lang["Predicates"], key=lambda x: len(x), reverse=True)
        self.functions = sorted(lang["Functions"], key=lambda x: len(x), reverse=True)
        self.constants = lang["Constants"]
        self.error = ""
        self.error_index = -1
        self.print_info = ""
        self.need_print = need_print


    def current_chr(self):
        return self.proposition[self.index] if self.index < self.length else None


    def reset(self, index, print_info, error_message, error_index):
        if self.index > self.error_index:
            self.error_index = error_index
            self.error = error_message
        self.index = index
        self.print_info = print_info


    def print_error(self):
        print(self.error, end="")
        print(self.proposition)
        print(" "*(self.error_index-1),"^")


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
        if char.islower() and char not in self.constants and char not in self.functions:
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


    def parse_invisible_multiplication(self):
        if "□□" in self.functions:
            node = self.function_first() or self.parse_constant() or self.parse_variable()
            if node is None:
                return
            node = self.handle_postfix_function(node)
            if self.index >= self.length or self.current_chr() in ['(', ')', ',', '∧', '∨', '⇒', '⇔']:
                return node
            index = self.index
            func = self.get_function()
            self.index = index
            if func and get_type(func, language) == "infix":
                return node
            index = self.index
            pred = self.get_predicate()
            self.index = index
            if pred:
                return node
            child = self.parse_invisible_multiplication()
            if child is None:
                return
            else:
                child = self.handle_postfix_function(child)
                node = Node("□□", children=[node, child])
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                return node
        else:
            self.reset(self.index, self.print_info, f"The invisible multiplication function is not defined in the language.\n", self.index)
            return



    def parse_function(self):
        return self.function_chain() or self.function_first()


    def get_function(self):
        for func in self.functions:
            length = len(func)
            if length == 1:
                break
            if func == self.proposition[self.index:self.index+length]:
                self.index += length - 1
                return func
        return self.current_chr() if self.current_chr() in self.functions else None


    def handle_postfix_function(self, node):
        while self.index < self.length:
            index = self.index
            func = self.get_function()
            if func and get_type(func, language) == "postfix":
                self.print_info += f"\tFound function {func}\n"
                node = Node(func, children=[node])
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                self.index += 1
            else:
                self.index = index
                break
        return node


    def function_first(self):
        prev_print = self.print_info
        start = self.index
        func = self.get_function()
        self.index += 1
        if func in self.functions:
            self.print_info += f"\tFound function: {func}\n"
            if get_type(func, language) != "prefix":
                self.reset(start, prev_print,f"Function {func} should be a prefix function to work with this syntax but is {get_type(func, language)}.\n", self.index)
                return
            arity = get_arity(func, language)
            if arity == 1:
                misplaced_func = self.get_function()
                if misplaced_func and get_type(misplaced_func, language) == "postfix":
                    self.reset(start, prev_print,f"Unexpected postfix function {misplaced_func} after prefix function {func}.\n", self.index)
                    return
                index = self.index
                child = self.parse_invisible_multiplication() or self.function_first() or self.handle_function_parenthesis()
                if not child:
                    self.reset(start, prev_print, f"Invalid argument for function {func}, at index {index}.\n", index)
                    return
                child = self.handle_postfix_function(child)
                if child.height == 0 and child.in_parenthesis:
                    self.reset(start, prev_print, f"Expression with one element should not be in parenthesis, at index {index}.\n", index)
                    return
                node = Node(func, children=[child])
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                node.in_parenthesis = False
                return node
            node = Node(func)
            if self.current_chr() == '(':
                self.index += 1
                children = []
                for i in range(arity):
                    if self.current_chr() == ')':
                        self.reset(start, prev_print, f"Unexpected closing parenthesis at index {self.index}. Expected {arity} arguments.\n", self.index)
                        return
                    child = self.parse_function() or self.parse_invisible_multiplication()
                    if not child:
                        self.reset(start, prev_print, f"Invalid argument for function {func}, at index {self.index}.\n", self.index)
                        return
                    child = self.handle_postfix_function(child)
                    children.append(child)
                    if i < arity - 1:
                        if self.current_chr() == ',':
                            self.index += 1
                        else:
                            self.reset(start, prev_print, f"Expected comma between arguments of function {func}, at index {self.index}.\n", self.index)
                            return
                node.children = children
                if self.current_chr() == ')':
                    self.index += 1
                else:
                    self.reset(start, prev_print, f"Expected closing parenthesis after arguments of function {func}, at index {self.index}.\n", self.index)
                    return
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                node.in_parenthesis = True
                return node
            else:
                self.reset(start, prev_print, f"Expected opening parenthesis at index {self.index} to receive {arity} arguments for function {func}.\n", self.index)
                return
        else:
            self.index = start
        return None


    def handle_function_parenthesis(self):
        prev_print = self.print_info
        start = self.index
        if self.current_chr() == '(':
            self.index += 1
        else:
            self.reset(start, prev_print, f"Expected opening parenthesis at index {self.index}.\n", self.index)
            return
        node = self.function_chain()
        if not node:
            self.reset(start, prev_print, f"Invalid function in the parenthesis at index {self.index}.\n", self.index)
            return
        if self.current_chr() != ')':
            self.reset(start, prev_print, f"Expected closing parenthesis at index {self.index}.\n", self.index)
            return
        self.index += 1
        node = self.handle_postfix_function(node)
        node.in_parenthesis = True
        return node


    def function_chain(self):
        def create_node(comp):
            while len(comp) > 1:
                rgt = comp.pop()
                fnc = comp.pop()
                lft = comp.pop()
                n = Node(fnc, children=[lft, rgt])
                comp.append(n)
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(n, 2)
            return comp[0] if comp else None

        prev_print = self.print_info
        start = self.index

        node = self.handle_function_parenthesis() or self.function_first() or self.parse_variable() or self.parse_constant()
        if not node:
            self.reset(start, prev_print, f"No valid term at index {start}.\n", start)
            return None

        node = self.handle_postfix_function(node)
        components = [node]

        while self.index < self.length:
            index = self.index

            if self.current_chr() in [')', ',', '∧', '∨', '⇒', '⇔']:
                break

            pred = self.get_predicate()
            if pred:
                node = create_node(components)
                self.print_info += f"\tFound predicate: {pred}\n"
                arity = get_arity(pred, language)
                if arity != 2:
                    self.reset(start, prev_print,f"The arity for predicate {pred} should be 2 to work with this syntax, but is {arity}\n", self.index)
                    return
                predicate_type = get_type(pred, language)
                if predicate_type != "infix":
                    self.reset(start, prev_print,f"Expected infix predicate but found {predicate_type} predicate {pred}, at index {self.index}\n", self.index)
                    return
                self.index += 1
                child = self.parse_function()
                if not child:
                    self.reset(start, prev_print, f"Invalid argument for predicate {pred}, at index {self.index}.\n", self.index)
                    return
                if child.name in self.predicates or node.name in self.predicates:
                    self.reset(start, prev_print, f"Predicate {pred} cannot have another predicate as argument.\n",
                               self.proposition.index(child.name) if child.name in self.predicates else self.proposition.index(node.name))
                    return
                node = Node(pred, children=[node, child])
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                return node

            func = self.get_function()
            func_type = get_type(func, language)
            if func_type == "infix":
                arity = get_arity(func, language)
                if arity != 2:
                    self.reset(start, prev_print,f"The arity for function {func} should be 2 to work with this syntax, but is {arity}\n", self.index)
                    return
                self.print_info += f"\tFound infix function: {func}\n"
                components.append(func)
                self.index += 1
            elif func_type == "prefix":
                self.print_info += f"\tFound prefix function: {func}\n"
                if "□□" in self.functions:
                    components.append("□□")
                else:
                    self.reset(start, prev_print,f"The invisible multiplication function is not defined in the language.\n", self.index)
                    return
                self.index = index

            if not func:
                if "□□" in self.functions:
                    components.append("□□")
                else:
                    self.reset(start, prev_print, f"The invisible multiplication function is not defined in the language.\n",self.index)
                    return

            index = self.index
            if self.current_chr() == '(':
                child = self.handle_function_parenthesis()
            else:
                child = self.function_first() or self.parse_variable() or self.parse_constant()

            if not child:
                self.reset(start, prev_print, f"No valid found at index {index}.\n", index)
                return None

            child = self.handle_postfix_function(child)
            components.append(child)

        return create_node(components)


    def get_predicate(self):
        for func in self.predicates:
            length = len(func)
            if length == 1:
                break
            if func == self.proposition[self.index:self.index+length]:
                self.index += length - 1
                return func
        return self.current_chr() if self.current_chr() in self.predicates else None


    def parse_predicate(self):
        return self.predicate_first() or self.predicate_inside() or self.predicate_last()


    def predicate_first(self):
        prev_print = self.print_info
        start = self.index
        pred = self.get_predicate()
        self.index += 1
        if pred in self.predicates:
            self.print_info += f"\tFound predicate: {pred}\n"
            if get_type(pred, language) != "prefix":
                self.reset(start, prev_print,f"Predicate {pred} should be a prefix predicate to work with this syntax but is {get_type(pred, language)}.\n", self.index)
            arity = get_arity(pred, language)
            node = Node(pred)
            if self.current_chr() == '(':
                self.index += 1
                children = []
                for i in range(arity):
                    if self.current_chr() == ')':
                        self.reset(start, prev_print, f"Unexpected closing parenthesis, at index {self.index}. Expected {arity} arguments.\n", self.index)
                        return
                    child = self.parse_function() or self.parse_variable() or self.parse_constant()
                    if not child:
                        self.reset(start, prev_print, f"Invalid argument for predicate {pred}, at index {self.index}.\n", self.index)
                        return
                    children.append(child)
                    if i < arity - 1:
                        if self.current_chr() == ',':
                            self.index += 1
                        else:
                            self.reset(start, prev_print, f"Expected comma between arguments of predicate {pred}, at index {self.index}.\n", self.index)
                            return
                node.children = children
                if self.current_chr() == ')':
                    self.index += 1
                else:
                    self.reset(start, prev_print, f"Expected closing parenthesis after arguments of predicate {pred}, at index {self.index}.\n", self.index)
                    return
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                # node.in_parenthesis = True
                return node
            else:
                self.reset(start, prev_print, f"Expected opening parenthesis at index {self.index} to receive {arity} arguments for function {pred}.\n", self.index)
                return
        else:
            self.index = start
        return None


    def predicate_inside(self):
        prev_print = self.print_info
        start = self.index

        node = self.parse_function()
        if node and node.name in self.predicates:
            # node.in_parenthesis = True
            return node
        else:
            self.index = start

        expect_closing = False
        if self.current_chr() == '(':
            expect_closing = True
            self.index += 1
        child1 = self.parse_function() or self.parse_variable() or self.parse_constant()
        if child1 and child1.name in self.predicates:
            if expect_closing:
                if self.current_chr() == ')':
                    self.index += 1
                else:
                    self.reset(start, prev_print,f"Expected closing parenthesis after the second argument of predicate {child1.name}, at index {self.index}.\n", self.index)
                    return
            node = child1
        else:
            if not child1:
                self.reset(start, prev_print, f"No valid term found, at index: {self.index}.\n", self.index)
                return
            pred = self.get_predicate()
            self.index += 1
            if pred not in self.predicates:
                self.reset(start, prev_print, f"Expected predicate but found {pred}, at index {self.index}.\n", self.index)
                return
            self.print_info += f"\tFound predicate: {pred}\n"
            if get_arity(pred, language) != 2:
                self.reset(start, prev_print, f"{pred} should have arity 2 to work with this syntax, index {self.index}.\n", self.index)
                return
            predicate_type = get_type(pred, language)
            if predicate_type != "infix":
                self.reset(start, prev_print,f"Expected infix predicate but found {predicate_type} predicate {pred}, at index {self.index}\n", self.index)
                return
            child2 = self.parse_variable() or self.parse_constant() or self.parse_function()
            if not child2:
                self.reset(start, prev_print, f"Invalid argument for predicate {pred}, at index {self.index}.\n", self.index)
                return
            if expect_closing:
                if self.current_chr() == ')':
                    self.index += 1
                else:
                    self.reset(start, prev_print, f"Expected closing parenthesis after the second argument of predicate {pred}, at index {self.index}.\n", self.index)
                    return
            node = Node(pred, children=[child1, child2])
        self.print_info += "\tCurrent subtree representation:\n"
        self.print_info += get_printed_tree(node, 2)
        # node.in_parenthesis = True
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
                    self.reset(start, prev_print, f"Invalid argument at index {self.index}.\n", self.index)
                    return
                children.append(child)
                if self.current_chr() == ')':
                    break
                if self.current_chr() == ',':
                    self.index += 1
                else:
                    self.reset(start, prev_print, f"Expected comma between arguments, at index: {self.index}.\n", self.index)
                    return
            self.index += 1
            pred = self.get_predicate()
            if self.index < self.length:
                self.index += 1
            if pred not in self.predicates:
                self.reset(start, prev_print, f"Expected predicate but found {pred}, at index {self.index}.\n", self.index)
                return
            self.print_info += f"\tFound predicate: {pred}\n"
            arity = get_arity(pred, language)
            if arity != len(children):
                self.reset(start, prev_print, f"{pred} has arity {arity} but received {len(children)} arguments, at index {self.index}.\n", self.index)
                return
            predicate_type = get_type(pred, language)
            if predicate_type != "postfix":
                self.reset(start, prev_print,f"Expected postfix predicate but found {predicate_type} predicate {pred}, at index {self.index}\n", self.index)
                return
            node = Node(pred, children=children)
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            return node
        else:
            child = self.parse_function() or self.parse_variable() or self.parse_constant()
            if not child:
                self.reset(start, prev_print, f"No valid term found, at index: {self.index}.\n", self.index)
                return
            pred = self.get_predicate()
            self.index += 1
            if pred not in self.predicates:
                self.reset(start, prev_print, f"Expected predicate but found {pred}, at index {self.index}.\n", self.index)
                return
            arity = get_arity(pred, language)
            if arity != 1:
                self.reset(start, prev_print, f"{pred} has arity {arity} but it is required to be 1 to work with this syntax, at index {self.index}.\n", self.index)
                return
            predicate_type = get_type(pred, language)
            if predicate_type != "postfix":
                self.reset(start, prev_print,f"Expected postfix predicate but found {predicate_type} predicate {pred}, at index {self.index}\n", self.index)
                return
            node = Node(pred, children=[child])
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            # node.in_parenthesis = True
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
                self.reset(start, prev_print, f"No valid variable found for quantifier {char}, at index {self.index}.\n", self.index)
                return
            right = self.connective_chain() or self.parse_quantifier() or self.parse_predicate()
            if not right:
                self.reset(start, prev_print, f"Invalid formula or predicate found for quantifier {char}, at index {self.index}.\n", self.index)
                return
            node = Node(char, children=[left, right])
            self.print_info += "\tCurrent subtree representation:\n"
            self.print_info += get_printed_tree(node, 2)
            return node
        return None


    def handle_connective_parenthesis(self):
        prev_print = self.print_info
        start = self.index
        if self.current_chr() == '(':
            self.index += 1
        else:
            self.reset(start, prev_print, f"Expected opening parenthesis at index {self.index}.\n", self.index)
            return
        node = self.connective_chain()
        if not node:
            self.reset(start, prev_print, f"Invalid function in the parenthesis at index {self.index}.\n", self.index)
            return
        if self.current_chr() != ')':
            self.reset(start, prev_print, f"Expected closing parenthesis at index {self.index}.\n", self.index)
            return
        self.index += 1
        node.in_parenthesis = True
        return node


    def parse_unary(self):
        char = self.current_chr()
        if char == "¬":
            self.index += 1
            child = self.parse_unary() or self.parse_predicate() or self.connective_chain() or self.parse_quantifier()
            if child:
                node = Node(char, children=[child])
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(node, 2)
                return node


    def connective_chain(self):
        def create_node(comp):
            while len(comp) > 1:
                rgt = comp.pop()
                fnc = comp.pop()
                lft = comp.pop()
                n = Node(fnc, children=[lft, rgt])
                comp.append(n)
                self.print_info += "\tCurrent subtree representation:\n"
                self.print_info += get_printed_tree(n, 2)
            return comp[0] if comp else None

        prev_print = self.print_info
        start = self.index

        node = self.handle_connective_parenthesis() or self.parse_unary() or self.parse_predicate() or self.parse_quantifier()
        if not node:
            self.reset(start, prev_print, f"No valid term at index {start}.\n", start)
            return None
        components = [node]

        while self.index < self.length:
            if self.current_chr() in [')'] or not self.index < self.length:
                break

            connective = self.current_chr()
            if connective not in self.connectives:
                self.reset(start, prev_print, f"Expected connective but found {connective}, at index {self.index}.\n", start)
                return None
            if get_arity(connective, language) != 2:
                self.reset(start, prev_print, f"Expected connective with arity 2 but found {connective}, at index {self.index}.\n", start)
                return None
            components.append(connective)
            self.index += 1

            child = self.handle_connective_parenthesis() or self.parse_unary() or self.parse_predicate() or self.parse_quantifier()
            if not child:
                self.reset(start, prev_print, f"No valid formula found after {connective}, at index {self.index}.\n", start)
                return None
            components.append(child)

        return create_node(components)




    def parse_expression(self):
        return (
                self.connective_chain()
                or self.parse_quantifier()
                or self.parse_function()
                or self.parse_predicate()
                or self.parse_invisible_multiplication()
                or self.parse_constant()
                or self.parse_variable()
        )


    def parse(self):
        print(f"Parsing the following string: {self.proposition}") if self.need_print else None
        if not self.proposition:
            raise Exception("Input is empty string.")
        rt = self.parse_expression()
        if rt and self.index == self.length:
            rt = correct_precedence(rt, language)
            if self.need_print:
                print(self.print_info, end="")
                print("The final tree representation:")
                print_tree(rt,1)
                print(f"The proposition {self.proposition} is a expression of first order predicate logic over the specified language.")
            return rt
        else:
            self.print_error()
            raise SyntaxError("Invalid formula.")


propositions = [
    "(≤(1, y) ⇔ (a, ((2 + a)+a^(e/3)*9z+8r))≤)",
    "( f(func(x,y), y) Predicate y)",
    "(a Predicate y",
    "a ≤ y ",
    "((f(x, y), y)≤ ⇔ a P y)",
    "a + b",
    "(8 * (x - 5) + f(x,y)) + (7 + f(x,y)) + (7 + f(x,y))",
    "(((8 * x - 5 + f(x,y)) + (7 + f(x,y)), a)P ⇔ P((8 * x - 5 + f(x,y)) + (7 + f(x,y)), a))",
    "2+5-f(x,y) Predicate a",
    "(8 * (x - 5)) Predicate x",
    "(2+5-f(x,y))",
    "((8 * x - 5) ≥ 7 ⇔ 3 - 5 * x > 8 * z)",
    "(¬(x − y < x^2 + y * √z))",
    "(¬(x - y < x^2 + y * √z))",
    "∃z((5 + 1) * y = 4/5*x/y^2)",
    "(5 + 1) * y + 4/5*x/y^2",
    "∀x(x + 1 > 2)",
    "4",
    "(8*x - 5) + 7 ≥ (3 − 5*x ⇔ y > 8*z)",
    "((¬(x - y < x^2 + y * √z))∧∃z(5 + 1) * y = 5*x/y^2)",
    "∀x(x + 1)/(x^2 + 5) > (x^3 + 5*x + 11)/(1+(x - 8)/(x^4 - 1))",
    "(¬P(x, y)⇔∀x∃y∀z((P(y, z)∨Q(x, y, z))⇒(R(x, z, y)∨(¬P(x, z)))))",
    # "∀x∃y∀z((P(y, z)∨Q(x, y, z))⇒(R(x, z, y)∨(¬P(x, z))))",
    # "P(y, z)∨∀x¬∃y∀zP(y, z)∨Q(x, y, z)⇒¬R(x, z, y)∨¬P(x, z)",
    # "xPyPz",
    # "f(8x, 8x)",
    # "8x * 9z",
    # "( 8x * 9z ≥ 1 ⇒ (((2 + a) + a^e / (3 + 4) * 9z+8r) > (8x * − −9z)+8r))",
    # "2P3*f(2, +(2,3))",
    # "(xdx+99)*((9+2z+2)/8^8x)",
    # "((2 + a) + a^e / (3 + 4) * 9z+8r)",
    # "((2+a)+a^(e/3)*9z+8r)",
    # "√(√3*f(x,y)*a√3*√f(x,y) * √xy √ y)",
    # "8x9z+10y",
    # "8x9zg10y",
    # "8x9z+g10y",
    # "8x9zf10y",
    # "((2+3)isEven ⇒ 8x * 9z ≥ 1)",
    # "P((2+5-f(x,y)), a)",
    # "(a!!b!f(((xdx+99)*((9+2z+2)/8^8x))!,123xyz!y)!q+99)!!!",
    # "(a!!b!f( √(√3*f(x,y)*a√3*√f(x,y)h(x,y,z) * (√(x!)y!)!!!√y!) , ((2 + a) + a^e / (3 + 4) * 9z+8r) ))!!!",
    # "(√(x!)y!)!!!√y!",
    # "(√(x!)y!)!!!√(x+y)!",
    # "(√(x!)y!)!!!√x+y!",
    # "(x+y)√y",
    # "(x+y)f(x,y)",
    # "(x+y)(x+y)!",
    # "1+2^2^2+3+4/(5+5)+6+7+8+9",
    # "1+2^2^2+3+4/(5+5)+6-7+8-9",
    # "123xyz(45er)a",
    # "√!√y!)",
    # "f(x,y)",
    # "−(x+y)f(x,y)",
    # "x+yz",
    # "(x!)isEven",
    # "99x^2",
    # "f(99 , x^2)",
    # "99x + xyz^3 /3 + f(x,y)",
    # "(    ( (func(x mid y,y*r^x mid y))isEven ⇒ 99x > xyz^3 /3 + f(x,y) ) ∧ Predicate(√x!,y)    )",
    # "P(x,y) ∧ P(y, z) ⇒ ¬P(z, x) ∧ P(z,x1) ∧ ¬¬¬¬P(z,x2) ⇔ P(z,x3) ∧ ¬¬P(z,x4) ",
]

language = {
    "Functions": {
        "□□": {"arity": 2, "type": "infix", "precedence": 4, "associativity": "left"},
        "f": {"arity": 2, "type": "prefix", "precedence": 1, "associativity": "right"},
        "mid": {"arity": 2, "type": "infix", "precedence": 3, "associativity": "left"},
        "func": {"arity": 2, "type": "prefix"},
        "g": {"arity": 1, "type": "prefix"},
        "h": {"arity": 3, "type": "prefix"},
        "+": {"arity": 2, "type": "infix", "precedence": 1},
        "-": {"arity": 2, "type": "infix", "precedence": 1},
        "−": {"arity": 1, "type": "prefix", "precedence": 9},
        "*": {"arity": 2, "type": "infix", "precedence": 2},
        "/": {"arity": 2, "type": "infix", "precedence": 2},
        "^": {"arity": 2, "type": "infix", "precedence": 5, "associativity": "right"},
        "√": {"arity": 1, "type": "prefix", "precedence": 6},
        "!": {"arity": 1, "type": "postfix", "precedence": 7},
    },
    "Predicates": {
        "P": {"arity": 2, "type": "prefix"},
        "Predicate": {"arity": 2, "type": "prefix"},
        "Q": {"arity": 3, "type": "prefix"},
        "R": {"arity": 3, "type": "prefix"},
        "isEven": {"arity": 1, "type": "postfix"},
        "Last": {"arity": 1, "type": "postfix"},
        "≥": {"arity": 2, "type": "infix"},
        "≤": {"arity": 2, "type": "infix"},
        ">": {"arity": 2, "type": "infix"},
        "<": {"arity": 2, "type": "infix"},
        "=": {"arity": 2, "type": "infix"},
    },
    "Connectives": {
        "∧": {"arity": 2, "type": "infix", "precedence": 3, "associativity": "left"},
        "∨": {"arity": 2, "type": "infix", "precedence": 3, "associativity": "left"},
        "⇒": {"arity": 2, "type": "infix", "precedence": 2},
        "⇔": {"arity": 2, "type": "infix", "precedence": 1},
        "¬": {"arity": 1, "type": "prefix", "precedence": 4},
    },
    "Quantifiers": {
        "∀": {"arity": 2, "type": "prefix", "precedence": 0},
        "∃": {"arity": 2, "type": "prefix", "precedence": 0},
    },
    "Constants": {"a", "b", "c"},
}
language = format_language(language)
replacements = [
    "θ = {x ← x + 5, y ← 2x + 3, z ← y + u}",
    "σ = {x ← 3x + 3, z ← u + v, v ← x + 2y}",
    "λ = {y ← x + v, u ← 3y, v ← 4z}",
]
# replacements = format_replacements(replacements, language)
# for key, value in replacements["θ"].items():
#     print_tree(key)
#     print_tree(value)

def replace_node(node, replacement):
    for repl in replacement:
        if repl in node.children:
            print(1)


for proposition in propositions:
    try:
        parser = FirstOrderPredicateLogicParser(proposition, language)
        root = parser.parse()
        print(expression_type(root, language))

        get_elements_type(root, language)
        print("Proposition formed from tree:")
        print(tree_to_formula(root))

        # replace_node(root, replacements["θ"])

    except Exception as e:
        print(e)
    print(end="\n\n")
