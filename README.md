# Propositional Logic Parser

This project implements a parser for propositional logic formulas, capable of constructing a tree representation of the formulas, evaluating their truth values, and generating truth tables. It supports atomic propositions, unary connectives (negation), and binary connectives (conjunction, disjunction, implication, and equivalence).

## Features

- Parses well-formed propositional logic formulas.
- Constructs a tree structure to represent the parsed formula.
- Evaluates the truth values based on given interpretations.
- Generates truth tables for the formulas.
- Checks the validity and satisfiability of the formulas.

## Requirements

- Python 3.6 or higher
- `anytree` library for tree data structure management

To install the required library, use:

```bash
pip install anytree
```

## Usage

1. Create a JSON file named `propositions.json` containing your propositional logic formulas and their interpretations. The structure of the JSON file should be as follows:

    ```json
    [
        {
            "proposition": "((A ∧ B) ⇒ C)",
            "interpretations": [
                {"A": true, "B": false, "C": true},
                {"A": true, "B": true, "C": false}
            ]
        },
        ...
    ]
    ```
   or run the file provided in the repository


2. Run the parser:

    ```bash
    python your_script_name.py
    ```

3. The output will display:
    - The tree representation of each proposition.
    - The validity of the formula.
    - The truth values of the propositions for each interpretation.

## Example

For the proposition `((A ∧ B) ⇒ C)` with interpretations:

```json
{"A": true, "B": false, "C": true}
{"A": true, "B": true, "C": false}
```

The output will indicate the truth values of the formula under these interpretations, along with its validity.

## Error Handling

The parser includes error handling for:
- Empty propositions
- Unbalanced parentheses
- Invalid structures
- Missing truth values for variables

Errors will be reported with descriptive messages to aid debugging.

## Acknowledgments

- [anytree](https://github.com/c0fec0de/anytree) for providing a robust tree data structure.
