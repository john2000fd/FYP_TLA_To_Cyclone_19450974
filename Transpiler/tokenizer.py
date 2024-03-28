#This is our lexical analyser file, the first component of the transpiler
#This file uses the PLY Lex module to create a lexer that generatres a stream of tokens based on the defined grammar rules below


import ply.lex as lex    #import the lex module which facilitates PLY lexer capabilities for the file 



# Define token names for our tokenizer, this will give names to tokenization rules that match certain patterns
#Code developed with help from PLY Lex Yacc documentation:  https://www.dabeaz.com/ply/ply.html#ply_nn4
tokens = (
    'EXTENDS',
    'MODULE_WRAPPER',
    'MODULE',
    'GRAPH',
    'NODE',
    'EDGE',
    'VARIABLES',
    'VARIABLE_NAME',
    'CONSTANTS',
    'INIT',
    'SPEC',
    'INVARIANT',
    'GOAL',
    'CHECK',
    'ATTRIBUTE',
    'NUMBER_LITERAL',
    'STRING_LITERAL',
    'ARROW',
    'SEMICOLON',
    'LEFT_PAREN',
    'RIGHT_PAREN',
    'LEFT_BRACE',
    'RIGHT_BRACE',
    'EQUALS_EQUALITY',
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
    'EQUALS_DEFINITIONS',
    'GREATER_OR_EQ',
    'LESS_OR_EQ',
    'UNCHANGED',
    'NOT_EQUALS',
    'DOT',
    'EXCLAMATION_MARK',
    'AT',
    'ASSUME',
    'IN_A_SET',
    'Nat',
    'IF',
    'THEN',
    'ELSE',
    'NEXT_VALUE_OF_ATTRIBUTE',
    'EXCEPT',
    'ATTRIBUTE_MAY_CHANGE',
    'EVENTUALLY',
    'ENABLED',
    'EQUIVALENCE_OPERATOR',
    'TerminationHypothesis',
    'LoopInvariant',
    'WEAK_FAIRNESS',
    'THEOREM',
    'IMPLIES',
    'EventuallyTerminates',
    
    

)


# Define reserved words dictionary, this dictionary checks a matched ATTRIBUTE token against this list
# to determine if it should be classified under a specific reserved keyword or as a general ATTRIBUTE.

reserved = {   #Code developed with guidance from PLY Lex Yacc documentation:  https://www.dabeaz.com/ply/ply.html#ply_nn4
    'EXTENDS': 'EXTENDS',
    'MODULE': 'MODULE',
    'GRAPH': 'GRAPH',
    'NODE': 'NODE',
    'EDGE': 'EDGE',
    'VARIABLES': 'VARIABLES',
    'VARIABLE_NAME': 'VARIABLE_NAME',
    'CONSTANTS' : 'CONSTANTS',
    'Init': 'INIT',
    'Spec': 'SPEC',
    'GOAL': 'GOAL',
    'CHECK': 'CHECK',
    'UNCHANGED': 'UNCHANGED',
    'ASSUME' : 'ASSUME',
    'Nat' : 'Nat',
    'IF' : 'IF',
    'THEN' : 'THEN',
    'ELSE' : 'ELSE',
    'EXCEPT' : 'EXCEPT',
    'ENABLED' : 'ENABLED',
    'TerminationHypothesis' : 'TerminationHypothesis',
    'LoopInvariant' : 'LoopInvariant',
    'THEOREM' : 'THEOREM',
    'EventuallyTerminates' : 'EventuallyTerminates',
}


# Define tokenization rules, prefix "t_" before the string name indicates that it is a token
#Each of these functions is responsible for matching a specific pattern in the input text that corresponds to a particular token.
t_ARROW = r'->'
t_MODULE_WRAPPER = r'\----------------------------'
t_SEMICOLON = r';'
t_LEFT_PAREN = r'\('
t_RIGHT_PAREN = r'\)'
t_LEFT_BRACE = r'\{'
t_RIGHT_BRACE = r'\}'
t_STAR = r'\*'
t_OR = r'\\/'   
t_BACK_SLASH = r'\\'
t_FORWARD_SLASH = r'\/'
t_EVENTUALLY = r'\<>'
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
t_AND = r'/\\'  
t_COLON = r'\:'
t_MODULUS = r'\%'
t_EQUALS_DEFINITIONS = r'\=='
t_EQUALS_EQUALITY = r'\='
t_GREATER_OR_EQ = r'\>='
t_LESS_OR_EQ = r'\<='
t_NOT_EQUALS = r'\#'
t_DOT = r'\.'
t_EXCLAMATION_MARK = r'\!'
t_AT = r'\@'
t_IN_A_SET = r'\\in'
t_EQUIVALENCE_OPERATOR = r'\<=>'
t_IMPLIES = r'\=>'



#These are specific token rules, these handle code that needs more processing then just a regex string as they would not be identified otherwise
def t_WEAK_FAIRNESS(t):     
    r'WF'
    return t

def t_ATTRIBUTE_MAY_CHANGE(t):
    r'\_[A-Za-z_][A-Za-z0-9_]*'   # Regex that identifies code like '_can' that notates execution of the system at every step where that attribute may change
    return t

def t_NEXT_VALUE_OF_ATTRIBUTE(t):
    r'[A-Za-z_][A-Za-z0-9_]*\''  # Same regex as the ATTRIBUTE regex, except we want to catch the (') at the end of an attribute that denotes its next value
    return t


# Define 'Attribute' as the default token, this handles part of the code such as module name, variable name etc
def t_ATTRIBUTE(t):
    r'[A-Za-z_][A-Za-z0-9_]*'
    t.type = reserved.get(t.value, 'ATTRIBUTE')
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
    r'\============================================================================='
    pass

    
# error handling rule, 
def t_error(t):
    print(f"Illegal character!!!")
    t.tokenizer.skip(1)    #Skip 

# Build the lexer from the PLY Lex module
tokenizer = lex.lex()



#Example TLA Code, same as in main.py 
tla_code = """                           
---------------------------- MODULE CoffeeCan ----------------------------


EXTENDS Naturals

CONSTANTS MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLES can

\* The set of all possible cans
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

\* Possible values the can variable can take on
TypeInvariant == can \in Can

\* Initialize can so it contains between 1 and MaxBeanCount beans
Init == can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Number of beans currently in the can
BeanCount == can.black + can.white

\* Pick two black beans; throw both away, put one black bean in
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Pick two white beans; throw both away, put one black bean in
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Pick one bean of each color; put white back, throw away black
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Termination action to avoid triggering deadlock detection
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

\* Next-state relation: what actions can be taken
Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

\* Action formula: every step decreases the number of beans in the can
MonotonicDecrease == [][BeanCount' < BeanCount]_can

\* Liveness property: we eventually end up with one bean left
EventuallyTerminates == <>(ENABLED Termination)

\* Loop invariant: every step preserves white bean count mod 2
LoopInvariant == [][can.white % 2 = 0 <=> can'.white % 2 = 0]_can

\* Hypothesis: If we start out with an even number of white beans, we end up
\* with a single black bean. Otherwise, we end up with a single white bean.
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

\* Start out in a state defined by the Init operator and every step is one
\* defined by the Next operator. Assume weak fairness so the system can't
\* stutter indefinitely: we eventually take some beans out of the can.
Spec ==
    /\ Init
    /\ [][Next]_can
    /\ WF_can(Next)

\* What we want to show: that if our system follows the rules set out by the
\* Spec operator, then all our properties and assumptions will be satisfied.
THEOREM Spec =>
    /\ TypeInvariant
    /\ MonotonicDecrease
    /\ EventuallyTerminates
    /\ LoopInvariant
    /\ TerminationHypothesis

=============================================================================
"""

# input out TLA code into the Lexer
tokenizer.input(tla_code)

# Print stream of created tokens to the command line
for token in tokenizer:
    print(token)
    print()