import re
import ply.lex as lex



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
    'CONSTANTS',
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
    #'COMMENT',
    'EQUAL',
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
    'COMMA',
    'DIVIDE',
    'UNDERSCORE',
    'AND',
    'OR',
    'COLON',
    'MODULUS',
    'EQUALS',

    #'END_OF_FILE',

)


# Define reserved words dictionary  
reserved = {
    'EXTENDS': 'EXTENDS',
    'MODULE': 'MODULE',
    'MODULE_NAME': 'MODULE_NAME',
    #'COMMENT': 'COMMENT',
    'GRAPH': 'GRAPH',
    'NODE': 'NODE',
    'EDGE': 'EDGE',
    'VARIABLE': 'VARIABLE',
    'VARIABLE_NAME': 'VARIABLE_NAME',
    'CONSTANTS' : 'CONSTANTS',
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
t_EQUAL = r'\='
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
t_COMMA = r'\,'
t_UNDERSCORE = r'\_'
t_AND = r'/\\'  # Correct way to handle AND (logical conjunction)
t_OR = r'\\/'   # Correct way to handle OR (logical disjunction)
t_COLON = r'\:'
t_MODULUS = r'\%'
t_EQUALS = r'\=='

#t_END_OF_FILE = r'\================================'
#t_COMMENT =  r'\([^)]*\)'






# Define identifiers as the default token, this handles part of the code such as module name, variable name etc
def t_IDENTIFIER(t):
    r'[A-Za-z_][A-Za-z0-9_]*'
    t.type = reserved.get(t.value, 'IDENTIFIER')  # Default to IDENTIFIER, could be a module name or variable name etc
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

# we can skip comments as they are not needed for tokeniziation
def t_MULTILINE_COMMENT(t):
    r'\(\*([^*]*)\*\)'
    pass


def t_SINGLELINE_COMMENT_SPACE(t): 
    r'\\[*]\s.*'
    pass
    

def t_SINGLINE_COMMENT_NO_SPACE(t):
    r'\\[*].*'
    pass

def t_END_OF_FILE(t):   # we also don't need the end of file for our tokenization
    r'\================================'
    pass

    
# Define error handling rule
def t_error(t):
    print(f"Illegal character '{t.value[0]}'")
    t.tokenizer.skip(1)

# Build the lexer
tokenizer = lex.lex()

tla_code = """
---- MODULE Modulo4GraphCounter ----

EXTENDS Integers

(* State variables *)
VARIABLES counter, currentEdge

(* Set of nodes and static edges in the graph *)
CONSTANTS Nodes, Edges

(* Initial state: counter starts at 0, and no edge is selected initially *)
Init == 
    /\ counter = 0
    /\ currentEdge = NULL

(* Transition function for the counter, cycling through 0 to 3 *)
IncrementCounter == 
    counter' = (counter + 1) % 4

(* Update the current edge based on the counter value.
   Assuming Edges are ordered in some fashion for selection. *)
UpdateCurrentEdge == 
    LET edgeSelection == CHOOSE e \in Edges: TRUE IN
    /\ currentEdge' = edgeSelection

(* Combined next state relation *)
Next == 
    /\ IncrementCounter
    /\ UpdateCurrentEdge

(* Specification combines initial state and state transitions *)
Spec == Init /\ [][Next]_<<counter, currentEdge>>

(* Invariant to ensure the counter cycles correctly *)
Invariant == counter >= 0 /\ counter < 4

================================
"""

# Test the lexer
tokenizer.input(tla_code)

# Print tokens
for token in tokenizer:
    print(token)
    print()