import sympy as sp
import re

symbol_map = {
    '¬': '~',
    '∧': '&',
    '∨': '|',
    '⇒': '>>',
    '⇔': '==',
}
reverse_map = {v: k for k, v in symbol_map.items()}


def parse_formula(formula):
    for symbol, sympy_op in symbol_map.items():
        formula = formula.replace(symbol, sympy_op)
    return formula


def extract_variables(formula):
    return set(re.findall(r'\b[A-Z][0-9]*|⊤|⊥\b', formula))


def sympy_to_input_format(sympy_expr):
    sympy_str = str(sympy_expr)

    for sympy_op, symbol in reverse_map.items():
        sympy_str = sympy_str.replace(sympy_op, symbol)
    return sympy_str


def transform_formula(formula, conversion_type):
    try:
        parsed_formula = parse_formula(formula)

        variables = extract_variables(parsed_formula)
        sympy_symbols = {var: sp.symbols(var) for var in variables}

        for var, sympy_symbol in sympy_symbols.items():
            parsed_formula = parsed_formula.replace(var, f"sympy_symbols['{var}']")
        sympy_expr = eval(parsed_formula)

        simplified_expr = sp.simplify_logic(sympy_expr, form=conversion_type)

        if isinstance(simplified_expr, str):
            final_expression = simplified_expr
        else:
            final_expression = sympy_to_input_format(simplified_expr)

        return final_expression
    except Exception as e:
        return f"Error during transformation: {e}"

#
#
# input_formula = "(⊤⇒R)"
# output_formula = transform_formula(input_formula, "cnf")
#
#
# print(f"Input Formula: {input_formula}")
# print(f"Transformed Formula: {output_formula}")