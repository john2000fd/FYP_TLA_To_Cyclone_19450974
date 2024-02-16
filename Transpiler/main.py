import tokenization
import ast_for_tla
#import tla_to_cyclone

# Read TLA+ code from file or input
tla_code_1 = """

EXTENDS Naturals

GRAPH
  NODE node1
  NODE node2
  NODE node3

  EDGE node1 -> node2
  EDGE node2 -> node3

  LABEL "label1" ON node1 -> node2
  LABEL "label2" ON node2 -> node3

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

tla_code_2 = """
EXTENDS Naturals

GRAPH
  NODE a
  NODE b
  NODE c
  NODE d

  EDGE a -> b
  EDGE a -> c
  EDGE b -> d
  EDGE c -> d

VARIABLE visited

Init == (* Initial values *)
        /\ visited = {}

Next == (* State transition function *)
        /\ visited' = visited \cup {d}

Spec == Init /\ [][Next]_visited

Invariant == (* Invariant property *)
             visited # {}

Goal == (* System properties to check *)
        /\ Cardinality(visited) = 1

CHECK Goal
"""

# Tokenize TLA+ code
tokens = tokenization.tokenize_tla_code(tla_code_1)
tokens1 = tokenization.tokenize_tla_code(tla_code_2)

# Construct AST from tokens
ast_tree = ast_for_tla.construct_ast(tokens)
ast_tree_1 =ast_for_tla.construct_ast(tokens1)

# Translate AST to Cyclone code
#cyclone_code = tla_to_cyclone.translate_ast(ast_tree)

# Perform further processing on the AST as needed