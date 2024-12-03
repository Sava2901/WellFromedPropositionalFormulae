import json
from normal_form import *
from resolution import resolution, create_clause_list, find_satisfying_interpretation, clausal_to_strong, \
    strong_to_clausal, dpll
from wff import *
from utility import *


def default_case(prop):
    print(f"Started parsing the string: {prop}")
    if "⊨" in prop:
        print("Identified a possible consequence as a string.")
        parts = prop.replace(" ", "").split("⊨")
        left = parts[0].split(",")
        left_prop = "(" + "∧".join(f"({lft})" for lft in left) + ")" if len(left) > 1 else left[0]
        node = transform_to_normal_form(relaxed_to_strong(left_prop), "cnf")
        right_node = Node("¬", children=[relaxed_to_strong(parts[1])])
        right_prop = get_node_expression(right_node)
        print(f"To check if {parts[1]} is a logical consequence of {left_prop}, the proposition ({left_prop + "∧" + right_prop})) has to be unsatisfiable.")
        node.children = [*node.children, transform_to_normal_form(relaxed_to_strong(right_prop), "cnf")]
        satisf = dpll(create_clause_list(node))
        print(f"{parts[1]} is NOT a logical consequence of {left_prop}.") if satisf else print(f"{parts[1]} is a logical consequence of {left_prop}.")

    elif "∼" in prop:
        print("Identified a possible equivalence as a string.")
        parts = [relaxed_to_strong(p) for p in prop.split("∼")]
        for p in parts[1:]:
            if not compare_truth_tables(parts[0], p):
                print("The formulas are NOT equivalent.")
                break

    else:
        node = relaxed_to_strong(prop)
        print("The string is a wwf.\n")
        return node
    print(end="\n\n")


import re

def convert_instructions(instr):
    replacements = {
        ("well formed formula", "well-formed formula", "consequence", "equivalence"): "wff",
        ("truth table",): "truth_table",
        ("check validity", "check_satisfiability", "validity", "satisfiability"): "check_validity",
        ("negation normal form",): "nnf",
        ("conjunctive normal form",): "cnf",
        ("disjunctive normal form",): "dnf",
        ("resolution davis putnam", "davis putnam", "resolution dp", "dp"): "res_dp",
        ("resolution",): "res",
        ("satisfying truth valuation",): "stv",
        ("clause formula", "clausal formula", "clausal form"): "clausal_formula",
        ("formula",): "formula",
        ("davis putnam logemann loveland",):"dpll",
    }

    phrases_to_replacement = {phrase: replacement for phrases, replacement in replacements.items() for phrase in phrases}
    sorted_phrases = sorted(phrases_to_replacement.keys(), key=lambda x: -len(x))
    pattern = r'\b(?:' + '|'.join(map(re.escape, sorted_phrases)) + r')\b'

    def replacer(match):
        matched_phrase = match.group(0)
        return phrases_to_replacement[matched_phrase]

    instr = re.sub(pattern, replacer, instr)
    instr = [elem for elem in re.findall(r"\b[a-z_]+\b", instr) if elem in phrases_to_replacement.values()]
    instr = [elem for i, elem in enumerate(instr) if i == 0 or instr[i-1] != elem]

    return instr


def assert_function(node, fnc):
    return {
        "wff": lambda: default_case(get_node_expression(node)),
        "truth_table": lambda: get_printed_truth_table(node),
        "check_validity": lambda: check_validity(node),
        "nnf": lambda: transform_to_normal_form(node, "nnf"),
        "cnf": lambda: transform_to_normal_form(node, "cnf"),
        "dnf": lambda: transform_to_normal_form(node, "dnf"),
        "res_dp": lambda: resolution(create_clause_list(node), True),
        "res": lambda: resolution(create_clause_list(node), False),
        "dpll": lambda: dpll(create_clause_list(node)),
        "stv": lambda: find_satisfying_interpretation(create_clause_list(node)),
        "clausal_formula": lambda: strong_to_clausal(node),
        "formula": lambda: get_node_expression(node),
    }[fnc]


try:
    with open("propositions.json", "r", encoding="utf-8") as file:
        input_file = json.load(file)
    print("Data loaded successfully:", end="\n\n")
    for element in input_file:
        try:
            proposition = element["proposition"]
            if "instructions" not in element or element["instructions"] is None or element["instructions"] == "":
                print(f"Found no specific instructions for the proposition {proposition}. Running the default verifications.")
                default_case(proposition)
            else:
                instructions = convert_instructions(element["instructions"].lower())

                if "{" in proposition:
                    print(f"A tree structure has to be build from the set of clauses: {proposition}.")
                    root = clausal_to_strong(proposition)
                    print_tree(root,1)
                    root = transform_to_normal_form(root, "cnf")
                    print_tree(root,1)
                    print()
                else:
                    instructions.pop(0) if instructions[0] == "wff" else print("First it is required to check if the inputted string is a wff.")
                    root = default_case(proposition)

                if root is None and instructions:
                    raise Exception("Cannot receive more instructions for consequences or equivalences.")

                intermediate_results = {}

                for ins in instructions:
                    print(f"Current instruction: {ins}")
                    if ins in intermediate_results:
                        print("Already calculated this.")
                        print(intermediate_results[ins])
                    else:
                        res = assert_function(duplicate_node(root), ins)()
                        intermediate_results[ins] = res
                        if ins in ["wff", "nnf", "cnf", "dnf"]:
                            root = res
                            intermediate_results = {}
                        else:
                            print(res)
                    print(end="\n")
            print(end="\n\n")
        except Exception as e:
            print(f"Error: {e}")
        except KeyError:
            print("Proposition not found. Please ensure each element has a 'proposition' key.")
except FileNotFoundError:
    print("File not found. Ensure 'propositions.json' is in the correct directory.")
except json.JSONDecodeError:
    print("Failed to decode JSON. Ensure the JSON syntax is correct.")
except Exception as e:
    print("An error occurred:", e)