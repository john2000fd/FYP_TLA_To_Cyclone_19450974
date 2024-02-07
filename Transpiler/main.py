import tokenization
import ast

# Read TLA+ code from file or input
tla_code = """
EXTENDS Naturals

VARIABLE count

Init == (* Initial values *)
        /\ count = 0

Next == (* State transition function *)
        /\ count' = count + 1

Spec == Init /\ [][Next]_count

Invariant == (* Invariant property *)
             [](count >= 0)

Goal == (* System properties to check *)
        /\ count <= 10

CHECK Goal
"""

# Tokenize TLA+ code
tokens = tokenization.tokenize(tla_code)

# Construct AST from tokens
ast_tree = ast.construct_ast(tokens)

# Perform further processing on the AST as needed