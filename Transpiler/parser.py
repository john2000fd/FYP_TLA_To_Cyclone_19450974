import ply.yacc as yacc
from tokenizer import tokens

# Define precedence and associativity
precedence = (
    ('left', 'PLUS', 'MINUS'),
    ('left', 'TIMES', 'DIVIDE'),
    ('right', 'UMINUS'),
)

# Grammar rules

def p_module(p):
    '''module : MODULE IDENTIFIER SEMICOLON body'''
    # Code to handle module declaration

def p_body(p):
    '''body : statements'''
    # Code to handle module body

def p_statements(p):
    '''statements : statements statement
                  | statement'''
    # Code to handle multiple statements

def p_statement(p):
    '''
    statement : assignment_statement
              | expression_statement
              | graph_statement
              | node_statement
              | edge_statement
              | variable_statement
    '''
    # Code to handle different types of statements

def p_assignment_statement(p):
    '''
    assignment_statement : IDENTIFIER EQUALS expression SEMICOLON
    '''
    # Code to handle assignment statements

def p_expression_statement(p):
    '''
    expression_statement : expression SEMICOLON
    '''
    # Code to handle expression statements

def p_graph_statement(p):
    '''
    graph_statement : GRAPH IDENTIFIER SEMICOLON
    '''
    # Code to handle graph statements

def p_node_statement(p):
    '''
    node_statement : NODE IDENTIFIER SEMICOLON
    '''
    # Code to handle node statements

def p_edge_statement(p):
    '''
    edge_statement : EDGE IDENTIFIER ARROW IDENTIFIER SEMICOLON
    '''
    # Code to handle edge statements

def p_variable_statement(p):
    '''
    variable_statement : VARIABLE IDENTIFIER SEMICOLON
    '''
    # Code to handle variable statements

def p_expression(p):
    '''expression : expression PLUS expression
                  | expression MINUS expression
                  | expression TIMES expression
                  | expression DIVIDE expression
                  | MINUS expression %prec UMINUS
                  | LPAREN expression RPAREN
                  | identifier
                  | NUMBER'''
    # Code to handle expressions

def p_identifier(p):
    '''identifier : IDENTIFIER'''
    # Code to handle identifiers

# Error rule for syntax errors
def p_error(p):
    print("Syntax error in input!")

# Build the parser
parser = yacc.yacc()

# Test the parser with some input
data = '''
MODULE MyModule;
VARIABLE x;
x = 10 + 20;
GRAPH G;
NODE n;
EDGE n -> n;
'''
result = parser.parse(data)
print(result)