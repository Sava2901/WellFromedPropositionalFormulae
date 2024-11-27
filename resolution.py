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

    if not clauses:
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
                          if len(child.children) > 1 else f"{{{get_node_expression(child)}}}" for child in node.children)}}}".replace("(", "").replace(")", "")


def negate_literal(literal):
    if literal:
        return literal[1:] if literal[0] == "¬" else f"¬{literal}"


def create_clause_list(inp):
    if type(inp) == Node:
        string = strong_to_clausal(inp)
    elif type(inp) == str:
        if "{" in inp:
            string = inp
        else:
            string = strong_to_clausal(inp)
    else:
        raise Exception("Input should be string or node.")
    return [] if string == "{}" else [{literal for literal in clause.strip("{}").split(",")} for clause in re.findall(r"{[^{}]*}", string.replace(" ", ""))]


def get_printed_clauses(clauses):
    return "{" + ", ".join(f"{{{', '.join(clause)}}}" for clause in clauses) + "}"


def resolve(clause1, clause2):
    for literal in clause1:
        negation = negate_literal(literal)
        if negation in clause2:
            resolvent = (clause1 - {literal}) | (clause2 - {negation})
            return resolvent
    return None


def resolution(clauses, dp=True):
    if not clauses:
        print("Received the empty set of clauses as an input. The proposition becomes a tautology, being always satisfiable.")
        return True
    elif {""} in clauses:
        print("Received a set of clauses that contains an empty set. The proposition becomes a contradiction, being always unsatisfiable.")
        return False
    print(f"Calculating the resolvents for the clauses: {get_printed_clauses(clauses)}.")
    while True:
        new = set()
        if dp:
            print("\tSimplify the clauses using Davis Putnam's method.")
            print("\tChecking for clause sets with one literal:")
            clauses = one_literal_elimination(clauses)
            if set() in clauses:
                print("Clause {} resulted from simplification, therefore the proposition is unsatisfiable.")
                return False
            elif not clauses:
                print("After the simplification the set of clauses is {}, therefore the proposition is satisfiable.")
                return True
            clauses = pure_literal_elimination(clauses)
            if set() in clauses:
                print("Clause {} resulted from simplification, therefore the proposition is unsatisfiable.")
                return False
            elif not clauses:
                print("After the simplification the set of clauses is {}, therefore the proposition is satisfiable.")
                return True
        pairs = [(clauses[i], clauses[j]) for i in range(len(clauses)) for j in range(i + 1, len(clauses))]
        for clause1, clause2 in pairs:
            resolvent = resolve(clause1, clause2)
            if resolvent is not None:
                print(f"\tFrom clauses {clause1} and {clause2} we obtained the resolvent: {f'{resolvent}' if resolvent else '{}'}"
                      f"{f", which is already in the set of clauses" if resolvent in clauses else ""}.")
                if any(negate_literal(lit) in resolvent for lit in resolvent):
                    print(f"\tSkipping resolvent {resolvent} as it contains a literal and its negation, being equivalent to a tautology.")
                    continue
                if not resolvent or resolvent == set():
                    print("Clause {} resulted as a resolvent, therefore the proposition is unsatisfiable.")
                    return False
                new.add(frozenset(resolvent)) if frozenset(resolvent) not in new else None
                if dp and len(resolvent) == 1:
                    all_clauses = clauses + list(map(set, new))
                    all_clauses = one_literal_elimination(all_clauses)
                    if set() in all_clauses:
                        print("Clause {} resulted from simplification, therefore the proposition is unsatisfiable.")
                        return False
                    return resolution(all_clauses)

        if new.issubset(set(map(frozenset, clauses))):
            print("No new clauses created, therefore the proposition is satisfiable.")
            return True
        clauses.extend(list(map(set, new)))


def one_literal_elimination(clauses):
    applied = False
    for clause in clauses[:]:
        if len(clause) == 1:
            applied = True
            print(f"\tFound a clause with only one literal: {clause}")
            literal = next(iter(clause))
            negation = negate_literal(literal)
            for c in clauses[:]:
                if literal in c:
                    print(f"\tEliminate clause {c}; it contains {literal}.")
                    clauses.remove(c)
                if negation in c:
                    print(f"\tEliminate the negation of the literal {literal} from the clause {c}.")
                    c.remove(negation)
                if set() in clauses:
                    return clauses
    print(f"\tThe set of clauses becomes: {get_printed_clauses(clauses)}") if applied else print("\tFound none, the set of clauses remains the same.")

    return clauses


def pure_literal_elimination(clauses):
    all_literals = {lit for clause in clauses for lit in clause}
    pure_literals = {lit for lit in all_literals if negate_literal(lit) not in all_literals}

    print(f"\tIdentified pure literals: {pure_literals}.\n\tFor each, eliminate the sets containing it.") \
        if pure_literals else print("\tThere are no pure literals in the clauses set.\n\tIt remains unchanged.")

    if pure_literals:
        for clause in clauses[:]:
            if clause & pure_literals:
                print(f"\tEliminated clause: {clause}.")
                clauses.remove(clause)

    return clauses


def find_satisfying_interpretation(clauses):
    if not clauses:
        return "Any interpretation is a satisfying truth valuation."
    elif {""} in clauses:
        return "Unsatisfiable proposition has no satisfying truth valuation."

    positive_literals = [lit for clause in clauses for lit in clause if lit[0] != "¬"]

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
        print("Unsatisfiable proposition has no satisfying truth valuation.")
        return None

    for lit in positive_literals:
        if lit not in interpretation:
            interpretation[lit] = False

    return f"A satisfying truth valuation is: {interpretation}"