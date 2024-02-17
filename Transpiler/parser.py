import ply.yacc as yacc

# Define parser rules
def p_statement(p):
    '''
    statement : IDENTIFIER '=' expression ';'
    '''
    # Perform assignment action
    p[0] = ('assignment', p[1], p[3])

def p_expression(p):
    '''
    expression : expression '+' term
               | expression '-' term
               | term
    '''
    if len(p) == 2:
        p[0] = p[1]
    elif p[2] == '+':
        # Perform addition action
        p[0] = ('addition', p[1], p[3])
    elif p[2] == '-':
        # Perform subtraction action
        p[0] = ('subtraction', p[1], p[3])

def p_term(p):
    '''
    term : term '*' factor
         | term '/' factor
         | factor
    '''
    if len(p) == 2:
        p[0] = p[1]
    elif p[2] == '*':
        # Perform multiplication action
        p[0] = ('multiplication', p[1], p[3])
    elif p[2] == '/':
        # Perform division action
        p[0] = ('division', p[1], p[3])

def p_factor(p):
    '''
    factor : NUMBER
           | IDENTIFIER
           | '(' expression ')'
    '''
    if len(p) == 2:
        if isinstance(p[1], int):
            # Number literal
            p[0] = ('number', p[1])
        else:
            # Identifier
            p[0] = ('identifier', p[1])
    elif p[1] == '(':
        # Parenthesized expression
        p[0] = p[2]

# Error rule for syntax errors
def p_error(p):
    print("Syntax error:", p)

# Build the parser
parser = yacc.yacc()