import ply.yacc as yacc
from tokenizer import tokens
from tokenizer import tla_code
# Placeholder for storing parsed module information
parsed_data = {}

# Parsing rule for a module
def p_module(p):
    'module : MODULE_WRAPPER MODULE IDENTIFIER MODULE_WRAPPER body'
    parsed_data['module_name'] = p[3]
    parsed_data['body'] = p[5]

# Parsing rule for the body of the module, which could include various statements
def p_body(p):
    '''body : body statement
            | statement'''
    if len(p) == 3:
        p[0] = p[1] + [p[2]]
    else:
        p[0] = [p[1]]

# Parsing rule for different types of statements (simplified for demonstration)
def p_statement(p):
    '''statement : constants_declaration
                 | variable_declaration
                 | init_statement
                 | next_statement'''
    p[0] = p[1]

def p_constants_declaration(p):
    'constants_declaration : CONSTANTS IDENTIFIER COMMA IDENTIFIER'
    p[0] = ('constants', p[2], p[4])

def p_variable_declaration(p):
    'variable_declaration : VARIABLE IDENTIFIER'
    p[0] = ('variable', p[2])

def p_init_statement(p):
    'init_statement : INIT EQUALS expression'
    p[0] = ('init', p[3])

def p_next_statement(p):
    'next_statement : NEXT EQUALS expression'
    p[0] = ('next', p[3])

# Simplified rule for expression, to be expanded
def p_expression(p):
    '''expression : IDENTIFIER
                  | NUMBER_LITERAL'''
    p[0] = p[1]

# Error handling rule for syntax errors
def p_error(p):
    if p:
        print(f"Syntax error at '{p.value}'")
    else:
        print("Syntax error at EOF")

# Build the parser
parser = yacc.yacc()


result = parser.parse(tla_code)
print(result)
print(parsed_data)