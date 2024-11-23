import itertools
from utility import *


def transform_to_nnf(node, indent):
    if node.name == "¬":
        child = node.children[0]

        if child.name == "¬":
            print(f"{"\t"*(indent-1)}Transformed this node:")
            print_tree(node, indent)
            print(f"{"\t"*(indent-1)}Into its equivalent tree representation:")
            print_tree(child.children[0], indent)
            return transform_to_nnf(child.children[0], indent+1)

        elif child.name == "∧":
            print(f"{"\t"*(indent-1)}Transformed this node:")
            print_tree(node, indent)
            new_node = Node("∨", parent=node.parent)
            for grandchild in child.children:
                negated_child = Node("¬", parent=new_node)
                negated_child.children = [transform_to_nnf(grandchild, indent)]
            print(f"{"\t"*(indent-1)}Into its equivalent tree representation:")
            print_tree(new_node, indent)
            return transform_to_nnf(new_node, indent+1)

        elif child.name == "∨":
            print(f"{"\t"*(indent-1)}Transformed this node:")
            print_tree(node, indent)
            new_node = Node("∧", parent=node.parent)
            for grandchild in child.children:
                negated_child = Node("¬", parent=new_node)
                negated_child.children = [transform_to_nnf(grandchild, indent)]
            print(f"{"\t"*(indent-1)}Into its equivalent tree representation:")
            print_tree(new_node, indent)
            return transform_to_nnf(new_node, indent+1)

        elif child.name == "⇒":
            print(f"{"\t"*(indent-1)}Transformed this node:")
            print_tree(node, indent)
            left, right = child.children
            new_node = Node("∧", parent=node.parent)
            negated_right = Node("¬", parent=new_node, children=[transform_to_nnf(duplicate_node(right), indent)])
            new_node.children = [transform_to_nnf(duplicate_node(left), indent), negated_right]
            print(f"{"\t"*(indent-1)}Into its equivalent tree representation:")
            print_tree(new_node, indent)
            return transform_to_nnf(new_node, indent+1)

        elif child.name == "⇔":
            print(f"{"\t"*(indent-1)}Transformed this node:")
            print_tree(node, indent)
            left, right = child.children
            left_neg = Node("¬", parent=node.parent, children=[transform_to_nnf(duplicate_node(left), indent)])
            right_neg = Node("¬", parent=node.parent, children=[transform_to_nnf(duplicate_node(right), indent)])
            new_node = Node("∨", parent=node.parent)
            new_node.children = [
                Node("∧", parent=node.parent, children=[transform_to_nnf(duplicate_node(left), indent), right_neg]),
                Node("∧", parent=node.parent, children=[left_neg, transform_to_nnf(duplicate_node(right), indent)]),
            ]
            print(f"{"\t"*(indent-1)}Into its equivalent tree representation:")
            print_tree(new_node, indent)
            return transform_to_nnf(new_node, indent+1)

        else:
            return duplicate_node(node)

    elif node.name == "⇒":
        print(f"{"\t"*(indent-1)}Transformed this node:")
        print_tree(node, indent)
        left, right = node.children
        new_node = Node("∨", parent=node.parent)
        negated_left = Node("¬", parent=new_node, children=[transform_to_nnf(duplicate_node(left), indent+1)])
        new_node.children = [duplicate_node(negated_left), transform_to_nnf(duplicate_node(right), indent+1)]
        print(f"{"\t"*(indent-1)}Into its equivalent tree representation:")
        print_tree(new_node, indent)
        return transform_to_nnf(new_node, indent+1)

    elif node.name == "⇔":
        print(f"{"\t"*(indent-1)}Transformed this node:")
        print_tree(node, indent)
        left, right = node.children
        left_impl = Node("⇒", parent=node.parent, children=[duplicate_node(left), duplicate_node(right)])
        right_impl = Node("⇒", parent=node.parent, children=[duplicate_node(right), duplicate_node(left)])
        new_node = Node("∧", parent=node.parent, children=[left_impl, right_impl])
        print(f"{"\t"*(indent-1)}Into its equivalent tree representation:")
        print_tree(new_node, indent)
        return transform_to_nnf(new_node, indent+1)

    elif node.name in ["∧", "∨"]:
        node.children = [transform_to_nnf(child, indent) for child in node.children]

    return Node(node.name, parent=node.parent, children=node.children)


def transform_to_normal_form(node, conversion_type):
    conversion_type = conversion_type.lower()
    if conversion_type == "nnf":
        print("Converting the tree formula to nnf.")
        node = transform_to_nnf(node, 2)
        print("This is the raw nnf formula; now simplifying it.")
        print_tree(node, 1)
        s_node = check_simplified_integrity(simplify_tree(duplicate_node(node)))
        if get_node_expression(s_node) == get_node_expression(node):
            print("No changes needed.")
            print(f"The nnf formula is: {get_node_expression(s_node)}")
        else:
            print("This is the final nnf.")
            print_tree(s_node, 1)
            print(f"With the formula: {get_node_expression(s_node)}")

        return s_node

    elif conversion_type in ["dnf", "cnf"]:
        node = transform_to_normal_form(node, "nnf")
        if conversion_type == "dnf":
            op_list = ["∧", "∨"]
        else:
            op_list = ["∨", "∧"]

        print(f"Started converting to {conversion_type}:")

        def convert(node):
            if node is None:
                return None
            if node.name == op_list[0]:
                if op_list[1] in [child.name for child in node.children]:
                    all_children = [[duplicate_node(grandchild) for grandchild in child.children] if len(child.children) > 1 else [duplicate_node(child)] for child in node.children]

                    distributed_children = list(itertools.product(*all_children))
                    node.name = op_list[1]
                    node.children = []
                    for children in distributed_children:
                        print(f"\tDistributed {op_list[0]} over {op_list[1]} and obtained:")
                        n = Node(op_list[0], children=[duplicate_node(child) for child in children])
                        print_tree(n,2)
                        s_n = simplify_tree(duplicate_node(n))
                        if get_node_expression(s_n) == get_node_expression(n):
                            print("\tWhich requires no further simplification.")
                        else:
                            print(f"\tWhich simplifies into:")
                            print_tree(s_n,2)
                        s_n.parent = node
                        print(f"\tThen append it to the simplified parent: {node.name}")
                        print_tree(simplify_tree(duplicate_node(node)), 2)

            for child in node.children[:]:
                convert(child)
            return node

        conv_node = simplify_tree(convert(duplicate_node(node)))

        if get_node_expression(conv_node) == get_node_expression(node):
            print("No changes needed.")
            print(f"The formula remains: {get_node_expression(conv_node)}")
        else:
            print(f"This is the {conversion_type} tree formula of the initial proposition:")
            print_tree(conv_node, 1)
            print(f"With the formula: {get_node_expression(conv_node)}")

        return conv_node
    else:
        print("Please input a correct conversion type")


def simplify_tree(node):
    if node is None:
        return None

    children_to_remove = []
    for child in node.children[:]:
        simplified_child = simplify_tree(child)
        if simplified_child is None:
            children_to_remove.append(child)

    for child in children_to_remove:
        node.children.remove(child)

    if node.name in {"∨", "∧"}:
        new_children = []
        for child in node.children:
            if child.name == node.name:
                new_children.extend(child.children)
            else:
                new_children.append(child)
        node.children = deduplicate_children(new_children)
        if len(node.children) == 1:
            node = node.children[0]

    if node.name == "∨":
        literals = set()
        negations = set()
        for child in node.children:
            if child.name == "¬" and child.children:
                negations.add(child.children[0].name)
            elif child.name:
                literals.add(child.name)

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

        if literals & negations:
            node.name = "⊥"
            node.children = []
            return node

    if node.name == "¬" and node.children:
        child = node.children[0]
        if child.name == "⊤":
            node.name = "⊥"
            node.children = []
        elif child.name == "⊥":
            node.name = "⊤"
            node.children = []

    elif node.name == "∧":
        new_children = []
        all_true = True
        for child in node.children:
            if child.name != "⊤":
                all_true = False
                break
        if all_true:
            node.name = "⊤"
            node.children = []
            return node
        for child in node.children:
            if child.name == "⊤":
                continue
            elif child.name == "⊥":
                node.name = "⊥"
                node.children = []
                return node
            else:
                new_children.append(child)
        node.children = deduplicate_children(new_children)
        if len(node.children) == 1:
            node = node.children[0]


    elif node.name == "∨":
        new_children = []
        all_false = True
        for child in node.children:
            if child.name != "⊥":
                all_false = False
                break
        if all_false:
            node.name = "⊥"
            node.children = []
            return node
        for child in node.children:
            if child.name == "⊥":
                continue
            elif child.name == "⊤":
                node.name = "⊤"
                node.children = []
                return node
            else:
                new_children.append(child)
        node.children = deduplicate_children(new_children)
        if len(node.children) == 1:
            node = node.children[0]

    return node


def check_simplified_integrity(node):
    if node is None:
        return
    else:
        if node.name in ["∧", "∨"] and len(node.children) == 1:
            node = node.children[0]
        node.children = [check_simplified_integrity(child) for child in node.children]
        return node