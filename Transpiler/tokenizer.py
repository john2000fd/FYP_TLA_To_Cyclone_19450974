import re
import ply.lex as lex
import ply.yacc as yacc


# Define token classes
tokens = (
    'EXTENDS',
    'GRAPH',
    'NODE',
    'EDGE',
    'VARIABLE',
    'INIT',
    'NEXT',
    'SPEC',
    'INVARIANT',
    'GOAL',
    'CHECK',
    'IDENTIFIER',
    'NUMBER_LITERAL',
    'STRING_LITERAL',
    'ARROW',
    'SEMICOLON',
    'LEFT_PAREN',
    'RIGHT_PAREN',
    'LEFT_BRACE',
    'RIGHT_BRACE',
    'COMMENT',
    'EQUALS',
    'STAR',
    'BACK_SLASH',
    'FORWARD_SLASH',
    'LESS_THAN',
    'GREATER_THAN',
    'LEFT_SQR_BRACKET',
    'RIGHT_SQR_BRACKET',
    'SINGLE_QUOTE',
    'PLUS',
    'MINUS',

)

# Define tokenization rules, prefix "t_" before the string name indicates that it is a token
t_EXTENDS = r'EXTENDS'
t_GRAPH = r'GRAPH'
t_NODE = r'NODE'
t_EDGE = r'EDGE'
t_VARIABLE = r'VARIABLE'
t_INIT = r'Init'
t_NEXT = r'Next'
t_SPEC = r'Spec'
t_INVARIANT = r'Invariant'
t_GOAL = r'Goal'
t_CHECK = r'CHECK'
t_ARROW = r'->'
t_SEMICOLON = r';'
t_LEFT_PAREN = r'\('
t_RIGHT_PAREN = r'\)'
t_LEFT_BRACE = r'\{'
t_RIGHT_BRACE = r'\}'
t_EQUALS = r'\='
t_STAR = r'\*'
t_BACK_SLASH = r'\\'
t_FORWARD_SLASH = r'\/'
t_LESS_THAN = r'\<'
t_GREATER_THAN = r'\>'
t_LEFT_SQR_BRACKET = r'\['
t_RIGHT_SQR_BRACKET = r'\]'
t_SINGLE_QUOTE = r'\''
t_PLUS = r'\+'
t_MINUS = r'\-'

# Define identifiers as the default token
def t_IDENTIFIER(t):
    r'[A-Za-z_][A-Za-z0-9_]*'
    t.type = 'IDENTIFIER'
    return t

# Define a rule for numbers
def t_NUMBER_LITERAL(t):
    r'\b(?:[0-9]+(?:\.[0-9]*)?|\.[0-9]+)\b'
    t.value = float(t.value) if '.' in t.value else int(t.value)
    return t

# Define a rule for strings
def t_STRING_LITERAL(t):
    r'"([^"\\]|\\.)*"'
    t.value = t.value[1:-1]  # Remove the quotes
    return t

#skip whitespace
t_ignore = ' \t'

# Define how to track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

# Define a rule for comments
def t_COMMENT(t):
    r'//.*'
    pass


# Define error handling rule
def t_error(t):
    print(f"Illegal character '{t.value[0]}'")
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()

tla_code = """
EXTENDS Naturals;

GRAPH
  NODE a
  NODE b
  EDGE a -> b;
  
VARIABLE count;

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

# Test the lexer
lexer.input(tla_code)

# Print tokens
for token in lexer:
    print(token)