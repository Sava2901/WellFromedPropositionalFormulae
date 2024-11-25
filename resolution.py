import re
from normal_form import transform_to_normal_form
from utility import *
from wff import relaxed_to_strong


def clausal_to_strong(inp, tree=True):
    if type(inp) == str:
        clauses = create_clause_list(inp)
    elif type(inp) == list:
        clauses = inp
    else:
        return

    if len(clauses) == 0:
        return Node("⊤") if tree else "⊤"

    for i, clause in enumerate(clauses):
        if clause == {''}:
            clauses[i] = {"⊥"}

    if tree:
        return Node("∧", children=[( Node("¬", children=[Node(sorted(clause)[0][1:])])
                                     if sorted(clause)[0][0] == "¬" else Node(sorted(clause)[0]) )
                                   if len(clause) == 1 else Node("∨", children=[Node(literal[0], children=[Node(literal[1:])])
                                if literal[0] == "¬" else Node(literal) for literal in clause]) for clause in clauses])
    else:
        return " ∧ ".join([f"({' ∨ '.join(clause)})" if len(clause) > 1 else f"{' ∨ '.join(clause)}" for clause in clauses])


def strong_to_clausal(inp):
    if type(inp) == str:
        node = relaxed_to_strong(inp)
    elif type(inp) == Node:
        node = inp
    else:
        return
    node = transform_to_normal_form(node, "cnf")

    return f"{{{", ".join(f"{{{", ".join(get_node_expression(grandchild) for grandchild in child.children)}}}" 
                          if len(child.children) > 1 else f"{{{get_node_expression(child).strip("()")}}}" for child in node.children)}}}"


def negate_literal(literal):
    if literal:
        return literal[1:] if literal[0] == "¬" else f"¬{literal}"


def create_clause_list(string):
    return [{literal for literal in clause.strip("{}").split(",")} for clause in re.findall(r"{[^{}]*}", string.replace(" ", ""))]


def resolve(clause1, clause2):
    for literal in clause1:
        negation = negate_literal(literal)
        if negation in clause2:
            resolvent = (clause1 - {literal}) | (clause2 - {negation})
            return resolvent if resolvent else {}
    return None


def resolution(clauses, dp=True):
    if clauses == {""}:
        return True
    elif {""} in clauses:
        return False
    new = set()
    while True:
        if dp:
            clauses = one_literal_elimination(clauses)
            clauses = pure_literal_elimination(clauses)
        pairs = [(clauses[i], clauses[j]) for i in range(len(clauses)) for j in range(i + 1, len(clauses))]
        for clause1, clause2 in pairs:
            resolvent = resolve(clause1, clause2)
            if resolvent is not None:
                if not resolvent:
                    return False
                new.add(frozenset(resolvent))
        if new.issubset(set(map(frozenset, clauses))):
            return True
        clauses.extend(list(map(set, new)))


def one_literal_elimination(clauses):
    for clause in clauses[:]:
        if len(clause) == 1:
            literal = next(iter(clause))
            negation = negate_literal(literal)
            for c in clauses[:]:
                clauses.remove(c) if literal in c else None
                c.remove(negation) if negation in c else None

    return clauses


def pure_literal_elimination(clauses):
    all_literals = {lit for clause in clauses for lit in clause}
    pure_literals = {lit for lit in all_literals if negate_literal(lit) not in all_literals}

    for clause in clauses[:]:
        if clause & pure_literals:
            clauses.remove(clause)

    return clauses


def find_satisfying_interpretation(clauses):
    if clauses == {""}:
        return True
    elif {""} in clauses:
        return False

    def dpll(clauses, assignment):
        clauses = [clause for clause in clauses if not any(lit in assignment and assignment[lit] for lit in clause)]

        if any(len(clause) == 0 for clause in clauses):
            return None

        if not clauses:
            return {lit if not lit.startswith("¬") else lit[1:]: not lit.startswith("¬") for lit in assignment}

        unassigned = sorted({lit for clause in clauses for lit in clause if lit not in assignment and negate_literal(lit) not in assignment})
        if not unassigned:
            return None

        literal = unassigned[0]

        assignment[literal] = True
        result = dpll(clauses, assignment)
        if result is not None:
            return result

        del assignment[literal]
        assignment[negate_literal(literal)] = True
        result = dpll(clauses, assignment)
        if result is not None:
            return result

        del assignment[negate_literal(literal)]
        return None

    clauses = [frozenset(clause) for clause in clauses]
    interpretation = dpll(clauses, {})

    if not interpretation:
        raise Exception("Unsatisfiable proposition has no satisfying truth valuation.\n")

    return interpretation

try:
    formula = "{{F1, ¬F2}, {F1, F3}, {}, {¬F1, F2}, {F2, ¬F3}, {¬F1, ¬F3}}"

    # print(create_clause_list(formula))

    # print_tree(clausal_to_strong(formula))

    print(get_printed_truth_table(clausal_to_strong(formula)))
    print(resolution(create_clause_list(formula)))
    print(find_satisfying_interpretation(create_clause_list(formula)))

except Exception as e:
    print(e)
