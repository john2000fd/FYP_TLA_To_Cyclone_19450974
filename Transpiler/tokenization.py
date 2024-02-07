import re

# Define regular expressions for token types
TOKEN_REGEX = [
    (r'\bEXTENDS\b.*(?:\n|$)', 'EXTENDS'),
    (r'\bVARIABLE\b.*(?:\n|$)', 'VARIABLE'),
    (r'\bInit\b.*(?:\n|$)', 'INIT'),
    (r'\bNext\b.*(?:\n|$)', 'NEXT'),
    (r'\bInvariant\b.*(?:\n|$)', 'INVARIANT'),
    (r'\bGoal\b.*(?:\n|$)', 'GOAL'),
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
def tokenize(code):
    tokens = []
    code_pos = 0
    
    while code_pos < len(code):
        match = None
        
        for token_regex, token_type in TOKEN_REGEX:
            regex = re.compile(token_regex, re.DOTALL)
            match = regex.match(code, code_pos)
            if match:
                if token_type:
                    tokens.append((token_type, match.group(0)))
                break
        
        if not match:
            raise SyntaxError(f"Invalid token at position {code_pos}: {code[code_pos:code_pos+10]}")
        
        code_pos = match.end()
    
    return tokens

# Example TLA+ code
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

# Tokenize the TLA+ code
tokens = tokenize(tla_code)
for token in tokens:
    print("This is the output: " , token)