import ply.yacc as yacc
from tokenizer import tokens

def p_statement(p):
    '''
    statement : assignment_statement
              | expression_statement
              | graph_statement
              | node_statement
              | edge_statement
              | variable_statement
    '''
    p[0] = p[1]

def p_assignment_statement(p):
    '''
    assignment_statement : IDENTIFIER EQUALS expression SEMICOLON
    '''
    p[0] = ('assignment', p[1], p[3])

def p_expression_statement(p):
    '''
    expression_statement : expression SEMICOLON
    '''
    p[0] = ('expression', p[1])

def p_graph_statement(p):
    '''
    graph_statement : GRAPH IDENTIFIER SEMICOLON
    '''
    p[0] = ('graph', p[2])

def p_node_statement(p):
    '''
    node_statement : NODE IDENTIFIER SEMICOLON
    '''
    p[0] = ('node', p[2])

def p_edge_statement(p):
    '''
    edge_statement : EDGE IDENTIFIER ARROW IDENTIFIER SEMICOLON
    '''
    p[0] = ('edge', p[2], p[4])

def p_variable_statement(p):
    '''
    variable_statement : VARIABLE IDENTIFIER SEMICOLON
    '''
    p[0] = ('variable', p[2])

def p_error(p):
    print("Syntax error in input!")

parser = yacc.yacc()

# Test parsing
data = '''
GRAPH G;
NODE a;
NODE b;
EDGE a -> b;
VARIABLE count;
'''
result = parser.parse(data)
print(result)