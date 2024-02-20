import re
import ply.lex as lex
import ply.yacc as yacc


# Define token classes for our tokenizer
tokens = (
    'EXTENDS',
    'MODULE_WRAPPER',
    'MODULE',
    'MODULE_NAME',
    'GRAPH',
    'NODE',
    'EDGE',
    'VARIABLE',
    'VARIABLE_NAME',
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
    'DIVIDE',
    'END_OF_FILE',

)


# Define reserved words dictionary  
reserved = {
    'EXTENDS': 'EXTENDS',
    'MODULE': 'MODULE',
    'MODULE_NAME': 'MODULE_NAME',
    'GRAPH': 'GRAPH',
    'NODE': 'NODE',
    'EDGE': 'EDGE',
    'VARIABLE': 'VARIABLE',
    'VARIABLE_NAME': 'VARIABLE_NAME',
    'Init': 'INIT',
    'Next': 'NEXT',
    'Spec': 'SPEC',
    'Invariant': 'INVARIANT',
    'Goal': 'GOAL',
    'CHECK': 'CHECK',
}


# Define tokenization rules, prefix "t_" before the string name indicates that it is a token
t_ARROW = r'->'
t_MODULE_WRAPPER = r'\----'
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
t_DIVIDE = r'div'
t_END_OF_FILE = r'\================================'



def t_MODULE_NAME(t):
    r'\b[A-Z][a-z]+(?:[A-Z][a-z]+)+\b'
    t.type = reserved.get(t.value, 'MODULE_NAME')
    return t


# Define identifiers as the default token
def t_IDENTIFIER(t):
    r'[A-Za-z_][A-Za-z0-9_]*'
    if re.match(r'[a-z][a-zA-Z0-9_]*', t.value):  # Check if it matches the pattern for variable names
        t.type = reserved.get(t.value, 'VARIABLE_NAME')
    else:
        t.type = reserved.get(t.value, 'IDENTIFIER')  # Check for reserved words
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
---- MODULE ComplexGraphBasedSpec ----

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

================================
"""

# Test the lexer
lexer.input(tla_code)

# Print tokens
for token in lexer:
    print(token)