import re
import ply.lex as lex
import ply.yacc as yacc

# Define regular expressions for token types that we will use 
TOKEN_REGEX = [
    (r'\bEXTENDS\b\s+(\w+)', 'EXTENDS'),
    (r'\bVARIABLE\b.*(?:\n|$)', 'VARIABLE'),
    (r'\bInit\b.*(?:\n|$)', 'INIT'),
    (r'\bNext\b.*(?:\n|$)', 'NEXT'),
    (r'\bInvariant\b.*(?:\n|$)', 'INVARIANT'),
    (r'\bGoal\b.*(?:\n|$)', 'GOAL'),
    (r'\bGraph\b.*(?:\n|$)', 'GRAPH'),  
    (r'\bNode\b.*(?:\n|$)', 'NODE'),    
    (r'\bEdge\b.*(?:\n|$)', 'EDGE'),    
    (r'\bLabel\b.*(?:\n|$)', 'LABEL'),  
    (r'"[^"]+"\s+ON\s+\w+\s*->\s*\w+', 'GRAPH_EDGE_LABEL'),  # Updated regex for LABEL
    (r'//.*(?:\n|$)', 'COMMENT'),
    (r'\btrue\b|\bfalse\b', 'BOOLEAN_LITERAL'),
    (r'\b(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)\b', 'NUMBER_LITERAL'),  # Floating point number
    (r'\b[0-9]+\b', 'INTEGER_LITERAL'),  # Integer number
    (r'\b(?:[A-Za-z_][A-Za-z0-9_]*)\b', 'IDENTIFIER'),  # Identifier
    (r'==', 'EQUALS'),
    (r'/\\', 'AND'),
    (r'->', 'ARROW'),
    (r'\*', 'ASTERISK'),
    (r'\(', 'LPAREN'),
    (r'\)', 'RPAREN'),
    (r';', 'SEMICOLON'),
    (r'\s+', None),  # Ignore whitespace
]

# Define a function to tokenize input code
def tokenize_tla_code(code):
    tokens = []
    code_pos = 0
    
    while code_pos < len(code):
        match = None
        
        for token_regex, token_type in TOKEN_REGEX:
            regex = re.compile(token_regex, re.DOTALL)
            match = regex.match(code, code_pos)
            if match:
                if token_type:
                    print(f"This is the token being made: {token_type}")
                    tokens.append((token_type, match.group(0)))
                break
        
        if not match:
            raise SyntaxError(f"Invalid token at position {code_pos}: {code[code_pos:code_pos+10]}")
        
        code_pos = match.end()
    
    return tokens

# Example TLA+ code
tla_code = """

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

# Tokenize the TLA+ code
tokens = tokenize_tla_code(tla_code)
#for token in tokens:
    #print("This is the output: " , token)