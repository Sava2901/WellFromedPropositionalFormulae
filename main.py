import json
from normal_form import *
from wff import *
from utility import *


def default_case(proposition):
    print(f"Started parsing the string: {proposition}")
    if "⊨" in proposition:
        print("Identified a possible consequence as a string.")
        parts = proposition.replace(" ", "").split("⊨")
        left = parts[0].split(",")
        left_prop = "(" + "∧".join(f"({lft})" for lft in left) + ")"
        prop = f"({left_prop}⇒{parts[1]})"
        print(f"The proposition should be equivalent to: {prop}")

        root = convert_from_relaxed(prop)

        print("Checking if it is true for all possible interpretations:")
        print_truth_table(root)

        if is_valid(root):
            print(f"The proposition is true for all possible interpretations; therefore, "
                    f"{parts[1]} is a logical consequence of {', '.join(str(elem) for elem in left)}.")
        else:
            print(f"The proposition is NOT true for all possible interpretations; therefore, "
                    f"{parts[1]} is NOT a logical consequence of {', '.join(str(elem) for elem in left)}.")

    elif "∼" in proposition:
        print("Identified a possible equivalence as a string.")
        parts = [convert_from_relaxed(prop) for prop in proposition.split("∼")]
        for prop in parts[1:]:
            if not compare_truth_tables(parts[0], prop):
                print("The formulas are NOT equivalent.")
                break

    else:
        root = convert_from_relaxed(proposition)
        print("The string is a wwf.")
        return root
    print(end="\n\n")


def convert_instructions(instr):
    replacements = {
        ("well formed formula", "well-formed formula", "consequence", "equivalence"): "wff",
        ("truth table",): "truth_table",
        ("check validity", "check_satisfiability", "validity", "satisfiability"): "check_validity",
        ("negation normal form",): "nnf",
        ("conjunctive normal form",): "cnf",
        ("disjunctive normal form",): "dnf",
    }

    for phrases, replacement in replacements.items():
        for phrase in phrases:
            if phrase in instr:
                instr = instr.replace(phrase, f" {replacement} ")

    instr = [elem for elem in re.findall(r"\b[a-z_]+\b", instr) if elem in replacements.values()]
    instr = [elem for i, elem in enumerate(instr) if instr[i-1] != elem]

    return instr


def assert_function(node, fnc):
    return {
        "wff": lambda: default_case(get_node_expression(node)),
        "truth_table": lambda: print_truth_table(node),
        "check_validity": lambda: check_validity(node),
        "nnf": lambda: transform_to_normal_form(node, "nnf"),
        "cnf": lambda: transform_to_normal_form(node, "cnf"),
        "dnf": lambda: transform_to_normal_form(node, "dnf"),
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

                print("First it is required to check if the inputted string is a wff.") if instructions[0] != "wff" else instructions.pop(0)
                root = default_case(proposition)

                if root is None and instructions:
                    raise Exception("cannot receive more instructions for consequences or equivalences.")

                intermediate_results = {}

                for ins in instructions:
                    print(f"Current instruction: {ins}")
                    if ins in intermediate_results:
                        print(intermediate_results[ins])
                    else:
                        res = assert_function(root, ins)()
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