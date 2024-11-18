import json
from itertools import product
from anytree import NodeMixin, RenderTree
from simplify import *
from shunting_yard import *


class Node(NodeMixin):  # Add Node feature
    def __init__(self, name, parent=None, children=None):
        self.name = name
        self.parent = parent
        if children:
            self.children = children


def print_tree(root, indentation = 0):
    indent = '\t'*indentation
    for pre, _, node in RenderTree(root):
        print(indent + f"{pre}{node.name}")


def convert_from_relaxed(prop, is_strong=False, need_print=True):
    if not is_strong:
        converter = ShuntingYardConverter(prop, need_print=need_print)
        prop = converter.convert()
    return prop


def is_chr(char):
    return char.isalpha() and char.isupper()


def get_variables(node):
    return {node.name} if node.name[0].isupper() and all(c.isalnum() for c in node.name) or node.name in ['⊤', '⊥'] else {var for child in node.children for var in get_variables(child)}


def get_node_expression(node):
    if node.is_leaf:
        return node.name
    elif node.name == "¬":
        return f"(¬{get_node_expression(node.children[0])})"
    elif node.name in ["∧", "∨"]:
        child_expressions = [get_node_expression(child) for child in node.children]
        return f"({f' {node.name} '.join(child_expressions)})"
    elif node.name in ["⇒", "⇔"]:
        left_expr = get_node_expression(node.children[0])
        right_expr = get_node_expression(node.children[1])
        return f"({left_expr} {node.name} {right_expr})"
    return node.name


def get_all_nodes(node):
    nodes = [n for n in get_variables(node)]
    def traverse(n):
        for child in n.children:
            traverse(child)
        if not n.is_leaf:
            expression = get_node_expression(n)
            if expression not in nodes:
                nodes.append(expression)
    traverse(node)
    return nodes


def evaluate_expression(tree_formula, expression, assignment, intermediary=None):
    if expression == "⊤":
        return True
    if expression == "⊥":
        return False
    if expression in assignment:
        return assignment[expression]
    sub_expr_node = next((n for n in tree_formula.descendants if get_node_expression(n) == expression), tree_formula)
    return evaluate_truth_table(sub_expr_node, assignment, intermediary)


def generate_truth_table(tree_formula, variables=None):

    if variables is None:
        variables = sorted(get_variables(tree_formula))
    truth_values = list(product([False, True], repeat=len(variables)))
    table = []
    headers = get_all_nodes(tree_formula)

    for values in truth_values:
        assignment = dict(zip(variables, values))
        if "⊤" in assignment and not assignment["⊤"]:
            continue
        if "⊥" in assignment and assignment["⊥"]:
            continue
        row = {var: assignment[var] for var in variables}
        intermediary_results = {}
        for formula in headers:
            result = evaluate_expression(tree_formula, formula, assignment, intermediary_results)
            row[formula] = result
        table.append(row)

    unique_table = []
    seen = set()
    for row in table:
        row_tuple = tuple(row.items())
        if row_tuple not in seen:
            seen.add(row_tuple)
            unique_table.append(row)
    return unique_table


def print_truth_table(tree_formula, table=None):
    if table is None:
        table = generate_truth_table(tree_formula)
    headers = get_all_nodes(tree_formula)

    col_widths = {header: len(header) + 2 for header in headers}
    truth_table = ""
    header = " | ".join(header.center(col_widths[header]) for header in headers) + '\n'
    header_line = "-" * len(header)
    truth_table += header_line + '\n'
    truth_table += header
    truth_table += header_line + '\n'
    for row in table:
        truth_table += " | ".join(("T" if row[col] else "F").center(col_widths[col]) for col in headers) + '\n'
    truth_table += header_line
    print(truth_table)


def evaluate_truth_table(node, values, intermediary=None):
    if intermediary is None:
        intermediary = {}
    required_vars = get_variables(node)
    missing_vars = required_vars - values.keys()
    if missing_vars:
        raise Exception(f"Missing truth value for {missing_vars}")

    if node in intermediary:
        return intermediary[node]

    if node.name == "⊤":
        result = True
    elif node.name == "⊥":
        result = False
    elif node.name == "¬":
        result = not evaluate_truth_table(node.children[0], values, intermediary)
    elif node.name == "∧":
        result = all(evaluate_truth_table(child, values, intermediary) for child in node.children)
    elif node.name == "∨":
        result = any(evaluate_truth_table(child, values, intermediary) for child in node.children)
    elif node.name == "⇒":
        left_result = evaluate_truth_table(node.children[0], values, intermediary)
        right_result = evaluate_truth_table(node.children[1], values, intermediary)
        result = not left_result or right_result
    elif node.name == "⇔":
        left_result = evaluate_truth_table(node.children[0], values, intermediary)
        right_result = evaluate_truth_table(node.children[1], values, intermediary)
        result = left_result == right_result
    else:
        result = values[node.name]

    intermediary[node] = result
    return result


def compare_truth_tables(left, right):
    variables = sorted(get_variables(left).union(get_variables(right)))
    left_table = generate_truth_table(left, variables=variables)
    right_table = generate_truth_table(right, variables=variables)
    left_headers = get_all_nodes(left)
    right_headers = get_all_nodes(right)

    equivalent = True
    for left_row, right_row in zip(left_table, right_table):
        left_result = left_row[left_headers[-1]]
        right_result = right_row[right_headers[-1]]

        assignments = {var: left_row[var] for var in variables}
        print(f"Assignments: {assignments} | Left side result: {left_result}, Right side result: {right_result}")

        if left_result != right_result:
            equivalent = False
            print(f"Results differ: Left side result: {left_result}, Right side result: {right_result}")
            break

    if equivalent:
        print("The formulas on both sides of '∼' are equivalent.")
    return equivalent


def check_validity(node):
    truth_table = []
    variables = sorted(get_variables(node))
    truth_values = list(product([False, True], repeat=len(variables)))
    for values in truth_values:
        assignment = dict(zip(variables, values))
        result = evaluate_truth_table(node, assignment)
        truth_table.append(result)
    is_satisfiable = any(result for result in truth_table)
    is_unsatisfiable = all(not result for result in truth_table)
    is_valid = all(result for result in truth_table)
    if is_valid:
        return "The formula is valid and satisfiable."
    elif is_unsatisfiable:
        return "The formula is unsatisfiable and invalid."
    elif is_satisfiable:
        return "The formula is satisfiable but invalid."


def duplicate_node(node):
    new_node = Node(node.name)
    for child in node.children:
        duplicated_child = duplicate_node(child)
        duplicated_child.parent = new_node
    return new_node


def merge_nodes(node):
    if not node.children:
        return node

    merged_children = []
    for child in node.children:
        merged_child = merge_nodes(child)
        if merged_child.name == node.name:
            merged_children.extend(merged_child.children)
        else:
            merged_children.append(merged_child)

    merged_node = Node(node.name)
    merged_node.children = tuple(merged_children)
    return merged_node


def transform_to_nnf(node):
    if node.name == "¬":
        child = node.children[0]

        if child.name == "¬":
            return transform_to_nnf(child.children[0])

        elif child.name == "∧":
            new_node = Node("∨", parent=node.parent)
            for grandchild in child.children:
                negated_child = Node("¬", parent=new_node)
                negated_child.children = [transform_to_nnf(grandchild)]
            return transform_to_nnf(new_node)

        elif child.name == "∨":
            new_node = Node("∧", parent=node.parent)
            for grandchild in child.children:
                negated_child = Node("¬", parent=new_node)
                negated_child.children = [transform_to_nnf(grandchild)]
            return transform_to_nnf(new_node)

        elif child.name == "⇒":
            left, right = child.children
            new_node = Node("∧", parent=node.parent)
            negated_right = Node("¬", parent=new_node, children=[transform_to_nnf(duplicate_node(right))])
            new_node.children = [transform_to_nnf(duplicate_node(left)), negated_right]
            return transform_to_nnf(new_node)

        elif child.name == "⇔":
            left, right = child.children
            left_neg = Node("¬", parent=node.parent, children=[transform_to_nnf(duplicate_node(left))])
            right_neg = Node("¬", parent=node.parent, children=[transform_to_nnf(duplicate_node(right))])
            new_node = Node("∨", parent=node.parent)
            new_node.children = [
                Node("∧", parent=node.parent, children=[transform_to_nnf(duplicate_node(left)), right_neg]),
                Node("∧", parent=node.parent, children=[left_neg, transform_to_nnf(duplicate_node(right))]),
            ]
            return transform_to_nnf(new_node)

        else:
            return duplicate_node(node)

    elif node.name == "⇒":
        left, right = node.children
        new_node = Node("∨", parent=node.parent)
        negated_left = Node("¬", parent=new_node, children=[transform_to_nnf(duplicate_node(left))])
        new_node.children = [negated_left, transform_to_nnf(duplicate_node(right))]
        return transform_to_nnf(new_node)

    elif node.name == "⇔":
        left, right = node.children
        left_impl = Node("⇒", parent=node.parent, children=[duplicate_node(left), duplicate_node(right)])
        right_impl = Node("⇒", parent=node.parent, children=[duplicate_node(right), duplicate_node(left)])
        new_node = Node("∧", parent=node.parent, children=[left_impl, right_impl])
        return transform_to_nnf(new_node)

    elif node.name in ["∧", "∨"]:
        node.children = [transform_to_nnf(child) for child in node.children]

    return Node(node.name, parent=node.parent, children=node.children)


def transform_to_normal_form(node, conversion_type):
    if conversion_type == "nnf":
        return transform_to_nnf(node)

    elif conversion_type in ["dnf", "cnf"]:
        node = transform_to_nnf(node)
        expression = get_node_expression(node)
        expression = transform_formula(expression, conversion_type)
        expression = convert_from_relaxed(expression, need_print=False)

        prs = Parser(expression, need_print=False)
        rt = prs.parse()
        s_rt = simplify_tree(rt)

        return s_rt
    else:
        print("Please input a correct conversion type")


def simplify_tree(node):
    """
    Simplify a tree in CNF or DNF form, addressing tautologies, contradictions,
    and logical redundancies while ensuring robustness against None nodes.
    """
    if node is None:
        return None  # Early exit if node is None

    # Recursively simplify children
    children_to_remove = []
    for child in node.children[:]:  # Use a copy of the list to allow safe modification
        simplified_child = simplify_tree(child)
        if simplified_child is None:  # If child simplifies to None, mark for removal
            children_to_remove.append(child)

    # Remove any None children
    for child in children_to_remove:
        node.children.remove(child)

    # Handle specific tautology and contradiction cases
    if node.name == "∨":
        literals = set()
        negations = set()
        for child in node.children:
            if child.name == "¬" and child.children:
                negations.add(child.children[0].name)
            elif child.name:
                literals.add(child.name)

        # Tautology (P ∨ ¬P)
        if literals & negations:
            node.name = "⊤"
            node.children = []
            return node

    elif node.name == "∧":
        literals = set()
        negations = set()
        for child in node.children:
            if child.name == "¬" and child.children:
                negations.add(child.children[0].name)
            elif child.name:
                literals.add(child.name)

        # Contradiction (P ∧ ¬P)
        if literals & negations:
            node.name = "⊥"
            node.children = []
            return node

    # Handle negations of tautologies and contradictions
    if node.name == "¬" and node.children:
        child = node.children[0]
        if child.name == "⊤":
            node.name = "⊥"
            node.children = []
        elif child.name == "⊥":
            node.name = "⊤"
            node.children = []

    # Simplify conjunctions
    elif node.name == "∧":
        new_children = []
        for child in node.children:
            if child.name == "⊤":  # Ignore tautology
                continue
            elif child.name == "⊥":  # Contradiction propagates
                node.name = "⊥"
                node.children = []
                return node
            else:
                new_children.append(child)
        node.children = deduplicate_children(new_children)
        if len(node.children) == 1:
            replace_with_child(node)

    # Simplify disjunctions
    elif node.name == "∨":
        new_children = []
        for child in node.children:
            if child.name == "⊥":  # Ignore contradiction
                continue
            elif child.name == "⊤":  # Tautology propagates
                node.name = "⊤"
                node.children = []
                return node
            else:
                new_children.append(child)
        node.children = deduplicate_children(new_children)
        if len(node.children) == 1:
            replace_with_child(node)

    return node


def deduplicate_children(children):
    """
    Remove duplicate children nodes based on their structure.
    """
    seen = set()
    unique_children = []
    for child in children:
        repr_str = render_node(child)
        if repr_str not in seen:
            seen.add(repr_str)
            unique_children.append(child)
    return unique_children


def render_node(node):
    """
    Render a node to a string representation for deduplication.
    """
    return f"{node.name}({','.join(sorted(render_node(child) for child in node.children))})" if node.children else node.name


def replace_with_child(node):
    """
    Replace a node with its single child in the parent's children list.
    """
    if node.parent:
        parent = node.parent
        index = parent.children.index(node)
        parent.children = parent.children[:index] + list(node.children) + parent.children[index + 1:]
    else:
        # If root node, promote the single child to root
        if node.children:
            node.name = node.children[0].name
            node.children = node.children[0].children




class Parser:
    def __init__(self, proposition, is_strong=False, need_print=True):
        self.proposition = proposition.replace(" ", "").replace("→", "⇒")
        self.index = 0
        self.length = len(self.proposition)
        self.operation_count = 0
        self.root = None
        self.is_equivalence = True if "∼" in self.proposition else False
        self.is_consequence = True if "⊨" in self.proposition else False
        self.is_strong = is_strong
        self.need_print = need_print


    def current_chr(self):
        return self.proposition[self.index] if self.index < self.length else None


    def parse_atomic(self):
        start_index = self.index
        char = self.current_chr()

        if char in ['⊤', '⊥']:
            self.index += 1
            print(f"\t{char} is {'a tautology' if char == '⊤' else 'a contradiction'}, at index: {start_index}") if self.need_print else None
            node = Node(char)
            print("\tCurrent subtree representation:") if self.need_print else None
            print_tree(node, 2) if self.need_print else None
            return node
        if char and is_chr(char):
            atomic_proposition = char
            self.index += 1

            while self.index < self.length and self.proposition[self.index].isdigit():
                atomic_proposition += self.proposition[self.index]
                self.index += 1

            print(f"\t{atomic_proposition} is an atomic {'subformula' if self.operation_count else 'formula'}, index: {start_index}") if self.need_print else None
            node = Node(atomic_proposition)
            print("\tCurrent subtree representation:") if self.need_print else None
            print_tree(node, 2) if self.need_print else None
            return node
        return None


    def parse_unary(self):
        if self.current_chr() == "(" and self.proposition[self.index + 1] == "¬":
            self.operation_count += 1
            self.index += 1
            print(f"\tDetected unary connective: ¬, at index: {self.index}.") if self.need_print else None
            self.index += 1

            sub_node = self.parse_expression()
            if not sub_node:
                raise Exception(f"Error: Expected an expression following ¬, at index: {self.index}.")
            if self.current_chr() != ")":
                raise Exception(f"Error: Expected closing parenthesis after unary expression, at index: {self.index}.")
            self.index += 1
            node = Node("¬", children=[sub_node])
            print("\tCurrent subtree representation:") if self.need_print else None
            print_tree(node, 2) if self.need_print else None
            return node
        return None


    def parse_binary(self):
        if self.current_chr() == "(":
            self.operation_count += 1
            self.index += 1

            left_node = self.parse_expression()
            if left_node:
                if self.current_chr() in ['∧', '∨', '⇒', '⇔']:
                    connective = self.current_chr()
                else:
                    raise Exception(f"Error: Expected connective, at index: {self.index}, but found {self.current_chr()}.")
                children = [left_node]
                while connective in ['∧', '∨']:
                    print(f"\tDetected binary connective: {connective}, at index: {self.index}.") if self.need_print else None
                    self.index += 1
                    next_node = self.parse_expression()
                    if next_node:
                        children.append(next_node)
                    else:
                        raise Exception(f"Error: Invalid expression after {connective} connective, at index: {self.index}.")
                    if self.current_chr() == ")":
                        break
                binary_node = Node(connective, children=children)
                if connective in ['⇒', '⇔']:
                    print(f"\tDetected binary connective: {connective}, at index: {self.index}.") if self.need_print else None
                    self.index += 1
                    right_node = self.parse_expression()
                    if right_node:
                        binary_node = Node(connective, children=[left_node, right_node])
                    else:
                        raise Exception(f"Error: Invalid expression after {connective} connective, at index: {self.index}.")
                if self.current_chr() == ")":
                    self.index += 1
                    print("\tCurrent subtree representation:") if self.need_print else None
                    print_tree(binary_node, 2) if self.need_print else None
                    return binary_node
                else:
                    if is_chr(self.current_chr()):
                        raise Exception(f"Error: Expecting an connective, at index: {self.index}, but found {self.current_chr()}.")
                    else:
                        raise Exception(f"Error: Missing closing parenthesis for {connective} operation, at index: {self.index}.")
        return None


    def parse_expression(self):
        return self.parse_atomic() or self.parse_unary() or self.parse_binary()


    def parse_proposition(self):
        if not self.proposition:
            raise Exception("Error: Empty proposition")
        self.root = self.parse_expression()
        if self.root and self.index == self.length:
            print("The string is a well formed formula.") if self.need_print else None
            return self.root
        elif self.current_chr() in ['∧', '∨', '⇒', '⇔']:
            raise Exception(f"Error: Binary operator '{self.current_chr()}' not enclosed in parentheses.")
        elif self.current_chr() == ")" or self.current_chr() is None:
            raise Exception("Error: Unbalanced parentheses detected.")
        elif self.current_chr() == "¬" and self.index < self.length - 1:
            raise Exception("Error: '¬' operator must be enclosed in parentheses.")
        else:
            raise Exception("Error: Invalid structure.")


    def parse(self):
        print(f"Starting parsing for: '{self.proposition}'") if self.need_print else None
        if "∼" in self.proposition:
            self.is_equivalence = True
            parts = self.proposition.split("∼", 1)
            left_prop, right_prop = (convert_from_relaxed(parts[0].strip(), is_strong=self.is_strong, need_print=self.need_print),
                                     convert_from_relaxed(parts[1].strip(), is_strong=self.is_strong, need_print=self.need_print))

            print(f"Parsing the string on the left of the '∼': '{left_prop}'") if self.need_print else None
            left_parser = Parser(left_prop)
            left_root = left_parser.parse_proposition()
            print("Left expression tree:") if self.need_print else None
            print_tree(left_root, 1) if self.need_print else None
            print(check_validity(left_root)) if self.need_print else None

            print(f"Parsing the string on the right of the '∼': '{right_prop}'") if self.need_print else None
            right_parser = Parser(right_prop)
            right_root = right_parser.parse_proposition()
            print("Right expression tree:") if self.need_print else None
            print_tree(right_root, 1) if self.need_print else None
            print(check_validity(right_root)) if self.need_print else None

            self.root = Node("∼", children=[left_root, right_root])
            return self.root
        elif "⊨" in self.proposition:
            print("We identified that we have a possible consequence as a string.") if self.need_print else None
            self.check_consequence(self.proposition)
        else:
            self.proposition = convert_from_relaxed(self.proposition, is_strong=self.is_strong, need_print=self.need_print)
            self.length = len(self.proposition)
            return self.parse_proposition()


    def check_consequence(self, string):
        parts = string.split("⊨")
        self.root = Node("⊨", children=[])
        left_lst = [convert_from_relaxed(s, is_strong=self.is_strong, need_print=self.need_print) for s in parts[0].split(",")]
        left_prop = "(" + '∧'.join(f'{op}' for op in left_lst) + ")" if len(
            parts[0].split(",")) > 1 else convert_from_relaxed(parts[0], is_strong=self.is_strong, need_print=self.need_print)
        right_lst = [convert_from_relaxed(s, is_strong=self.is_strong, need_print=self.need_print) for s in parts[1].split(",")]
        right_prop = "(" + '∧'.join(f'{op}' for op in right_lst) + ")" if len(
            parts[1].split(",")) > 1 else convert_from_relaxed(parts[1], is_strong=self.is_strong, need_print=self.need_print)
        prop = f"({left_prop}⇒{right_prop})"
        print(f"The proposition should be equivalent to: {prop}") if self.need_print else None
        print("Checking if it is true for all possible interpretations:") if self.need_print else None

        prs = Parser(prop, is_strong=True)
        node = prs.parse()
        print_truth_table(node)
        truth_table = generate_truth_table(node)
        prop_header = get_all_nodes(node)[-1]

        all_true = True
        for idx, row in enumerate(truth_table):
            if not row[prop_header]:
                all_true = False
                print(f"Failed case at row {idx + 1}:") if self.need_print else None
                print(f"Interpretation: {row}") if self.need_print else None
                break

        if all_true:
            print(f"The proposition is true for all possible interpretations; therefore, "
                  f"{', '.join(str(elem) for elem in right_lst)} is a logical consequence of "
                  f"{', '.join(str(elem) for elem in left_lst)}.") if self.need_print else None
        else:
            print(f"The proposition is NOT true for all possible interpretations; therefore, "
                  f"{', '.join(str(elem) for elem in right_lst)} is NOT a logical consequence of "
                  f"{', '.join(str(elem) for elem in left_lst)}.") if self.need_print else None




try:
    with open("propositions.json", "r", encoding="utf-8") as file:
        input_file = json.load(file)
    print("Data loaded successfully:", end="\n\n")
    for element in input_file:
        try:
            proposition = element["proposition"]
            parser = Parser(proposition)
            try:
                root = parser.parse()
                if parser.is_equivalence:
                    print("Now we check if the formulas are equivalent by comparing the truth tables.")
                    print(f"The truth table for {get_node_expression((root.children[0]))} is:")
                    print_truth_table(root.children[0])
                    print(f"The truth table for {get_node_expression((root.children[1]))} is:")
                    print_truth_table(root.children[1])
                    compare_truth_tables(root.children[0], root.children[1])
                elif not parser.is_consequence:
                    print("The tree representation of the proposition is:")
                    print_tree(root, 1)

                    print("This is the nnf tree formula of the proposition:")
                    nnf_root = transform_to_normal_form(duplicate_node(root), "nnf")
                    print_tree(nnf_root, 1)

                    print("This is the cnf tree formula of the proposition:")
                    cnf_root = transform_to_normal_form(duplicate_node(root), "cnf")
                    print_tree(cnf_root, 1)

                    print("This is the dnf tree formula of the proposition:")
                    cnf_root = transform_to_normal_form(duplicate_node(root), "dnf")
                    print_tree(cnf_root, 1)

                    try:
                        interpretations = element.get("interpretations", None)
                        if interpretations is None:
                            print(f"There are no specific interpretations for '{proposition}'")
                        elif len(interpretations) == 0:
                            print(f"There should be specific interpretations for '{proposition}', but found none.")
                        else:
                            print("Testing the inserted interpretations:")
                            for inter in interpretations:
                                try:
                                    evaluation = evaluate_expression(root, get_node_expression(root), inter)
                                    print(f"\tThe truth value of the proposition with {inter} is {evaluation}")
                                except Exception as e:
                                    print(f"\tError during evaluation with interpretation {inter}: {e}")
                    except TypeError:
                        print(f"Unexpected type for interpretations in '{proposition}'. Expected a list of dictionaries.")
            except Exception as e:
                print(f"{e}\nError")
            print(end="\n\n")
        except KeyError:
            print("Proposition not found. Please ensure each element has a 'proposition' key.")
except FileNotFoundError:
    print("File not found. Ensure 'propositions.json' is in the correct directory.")
except json.JSONDecodeError:
    print("Failed to decode JSON. Ensure the JSON syntax is correct.")
except Exception as e:
    print("An error occurred:", e)