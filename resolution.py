# def dpll(cnf: List[Set[str]], assignment: dict = {}) -> bool:
#     """
#     DPLL algorithm for SAT solving.
#     """
#     # If all clauses are satisfied
#     if all(any(literal in assignment and assignment[literal] for literal in clause) for clause in cnf):
#         return True
#
#     # If any clause is unsatisfied
#     if any(all(literal in assignment and not assignment[literal] for literal in clause) for clause in cnf):
#         return False
#
#     # Choose an unassigned literal
#     unassigned = {literal for clause in cnf for literal in clause if literal not in assignment}
#     if not unassigned:
#         return False
#     literal = next(iter(unassigned))
#
#     # Recur with literal set to True and False
#     assignment_copy = assignment.copy()
#     assignment_copy[literal] = True
#     if dpll(cnf, assignment_copy):
#         return True
#     assignment_copy[literal] = False
#     return dpll(cnf, assignment_copy)


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
            clauses[i] = "⊥"

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
    """
    Finds a satisfying interpretation for the given formula in CNF.

    :param clauses: List of sets representing the CNF formula (clausal form).
    :return: A dictionary mapping literals to True or False if satisfiable; None otherwise.
    """

    def dpll(clauses, assignment):
        # Eliminate satisfied clauses
        clauses = [clause for clause in clauses if not any(lit in assignment and assignment[lit] for lit in clause)]

        print(clauses)

        if any(len(clause) == 0 for clause in clauses):
            return None

        # Check if all clauses are satisfied
        if not clauses:
            return assignment

        # Choose an unassigned literal (heuristic: first literal from first clause)
        unassigned = {lit for clause in clauses for lit in clause if
                      lit not in assignment and negate_literal(lit) not in assignment}
        print(unassigned)
        literal = next(iter(unassigned))
        print(literal)

        # Try assigning the literal to True
        assignment[literal] = True
        result = dpll(clauses, assignment)
        if result is not None:
            return result

        # Backtrack and try assigning the literal to False
        del assignment[literal]
        assignment[negate_literal(literal)] = True
        result = dpll(clauses, assignment)
        if result is not None:
            return result

        # Backtrack if neither works
        del assignment[negate_literal(literal)]
        return None

    # Start the DPLL process with an empty assignment
    return dpll(clauses, {})


formula = "{{F1, F2}, {¬F2}, {¬F1, F2, F3}}"

print_tree(clausal_to_strong(formula))

print(get_printed_truth_table(clausal_to_strong(formula)))

print(find_satisfying_interpretation(create_clause_list(formula)))

