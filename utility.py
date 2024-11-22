from anytree import NodeMixin, RenderTree
from itertools import product


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


def get_printed_tree(root, indentation=0):
    tree = ""
    indent = '\t' * indentation
    for pre, _, node in RenderTree(root):
        tree += indent + f"{pre}{node.name}\n"
    return tree


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

    print(f"Comparing {get_node_expression(left)} and {get_node_expression(right)}:")

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


def is_valid(node, truth_table=None):
    if truth_table is None:
        truth_table = generate_truth_table(node)

    prop_header = get_all_nodes(node)[-1]
    for idx, row in enumerate(truth_table):
        if not row[prop_header]:
            print(f"Failed case at row {idx + 1}:")
            print(f"Interpretation: {row}")
            return False
    return True


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


def flatten_connectives(node):
    if node is None:
        return None

    for child in node.children[:]:
        flatten_connectives(child)

    if node.name in {"∨", "∧"}:
        new_children = []
        for child in node.children:
            if child.name == node.name:
                new_children.extend(child.children)
            else:
                new_children.append(child)
        node.children = deduplicate_children(new_children)

    return node


def duplicate_node(node):
    new_node = Node(node.name)
    for child in node.children:
        duplicated_child = duplicate_node(child)
        duplicated_child.parent = new_node
    return new_node


def deduplicate_children(children):
    seen = set()
    unique_children = []
    for child in children:
        repr_str = get_node_expression(child)
        if repr_str not in seen:
            seen.add(repr_str)
            unique_children.append(child)
    return unique_children