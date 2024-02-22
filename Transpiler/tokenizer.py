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
    'COMMA',
    'DIVIDE',
    'UNDERSCORE',
    'END_OF_FILE',

)


# Define reserved words dictionary  
reserved = {
    'EXTENDS': 'EXTENDS',
    'MODULE': 'MODULE',
    'MODULE_NAME': 'MODULE_NAME',
    'COMMENT': 'COMMENT',
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
t_COMMA = r'\,'
t_UNDERSCORE = r'\_'
#t_END_OF_FILE = r'\================================'
#t_COMMENT =  r'\([^)]*\)'



#def t_MODULE_NAME_SINGLE(t):  #regex to identify a module name that is a single word beginning with a capital letter
    #r'\b[A-Z][a-z]+\b'

    #if re.match( r'\b[A-Z][a-z]+\b', t.value):
       #t.type = reserved.get(t.value, 'MODULE_NAME')   
        
    #return t


#def t_MODULE_NAME_MULTIPLE(t):    #regex to identify a module name that has multiple words beginning with a capital letter
    #r'\b[A-Z][a-z]+(?:[A-Z][a-z]+)+\b'

    #if re.match(r'\b[A-Z][a-z]+(?:[A-Z][a-z]+)+\b', t.value):
        #t.type = reserved.get(t.value, 'MODULE_NAME')   

    #return t    


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
tokenizer= lex.lex()

tla_code = """
---- MODULE ComplexHello ----

EXTENDS Naturals

(* Graph structure represented as constants for transpilation purposes *)
CONSTANTS Nodes, Edges

(* State variable *)
VARIABLE count

(* Definitions to simulate graph concepts, assuming they are handled by your transpiler *)
IsEdge(u, v) == <<u, v>> \in Edges \/ <<v, u>> \in Edges

(* Initial state *)
Init == 
    /\ count = 0
    /\ Nodes = {"a", "b"}    \* Graph nodes
    /\ Edges = {<<"a", "b">>}    \* Graph edges, indicating a directed edge from 'a' to 'b'

(* State transition *)
Next == 
    /\ count' = count + 1

(* Specification combines initial state and state transitions *)
Spec == Init /\ [][Next]_count

(* Invariant to ensure 'count' remains non-negative *)
Invariant == count >= 0

(* Property to limit 'count' to 10, demonstrating goal definition *)
PropertyGoal == count <= 10

================================
"""

# Test the lexer
tokenizer.input(tla_code)

# Print tokens
for token in tokenizer:
    print(token)
    print()