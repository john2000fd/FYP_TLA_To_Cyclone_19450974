import ply.yacc as yacc
from tokenizer import tokens
from tokenizer import tla_code


# Placeholder for storing parsed module information
parsed_data = {}


class ASTNode:     #AST classes 
    pass

class ModuleNode(ASTNode):
    def __init__(self, name, extends, declarations):
        self.name = name
        self.extends = extends
        self.declarations = declarations


class ExtendsNode(ASTNode):
    def __init__(self, extended_module):
        self.extended_module = extended_module

class ConstantsNode(ASTNode):
    def __init__(self, constants):
        self.constants = constants  # List of constant names

class VariablesNode(ASTNode):
    def __init__(self, variables):
        self.variables = variables  # List of variable names

class AssignmentNode(ASTNode):
    def __init__(self, left, right):
        self.left = left
        self.right = right

class BinaryOperationNode(ASTNode):
    def __init__(self, left, operator, right):
        self.left = left
        self.operator = operator
        self.right = right

class IdentifierNode(ASTNode):
    def __init__(self, name):
        self.name = name

class LiteralNode(ASTNode):
    def __init__(self, value):
        self.value = value



# Parsing the module with optional extends and body (declarations, assignments, etc.)
def p_module(p):
    '''module : MODULE_WRAPPER MODULE IDENTIFIER MODULE_WRAPPER extends declarations
              | MODULE_WRAPPER MODULE IDENTIFIER MODULE_WRAPPER declarations'''
    if len(p) == 7:
        p[0] = ModuleNode(name=p[3], extends=p[5], declarations=p[6])
    else:
        p[0] = ModuleNode(name=p[3], extends=None, declarations=p[5])


def p_extends(p):
    '''extends : EXTENDS IDENTIFIER
               | empty'''
    p[0] = ExtendsNode(extended_module=p[2]) if p[1] else None

def p_body(p):
    '''body : declarations
            | empty'''
    p[0] = p[1]


# Define rules for `statement`, `variable_declaration`, `constants_declaration`, etc.

def p_statement(p):
    '''statement : constants_declaration
                 | variables_declaration
                 | assignment_statement
                 | empty'''
    p[0] = p[1]


def p_declarations(p):
    '''declarations : declarations declaration
                    | declaration'''
    if len(p) == 3:
        p[1].append(p[2])
        p[0] = p[1]
    else:
        p[0] = [p[1]]


def p_declaration(p):
    '''declaration : constants_declaration
                   | variables_declaration
                   | assignment_statement'''
    p[0] = p[1]

def p_constants_declaration(p):
    'constants_declaration : CONSTANTS IDENTIFIER_LIST'
    p[0] = ConstantsNode(p[2])


def p_variables_declaration(p):
    'variables_declaration : VARIABLE IDENTIFIER_LIST'
    p[0] = VariablesNode(p[2])


def p_identifier_list(p):
    """
    IDENTIFIER_LIST : IDENTIFIER_LIST COMMA IDENTIFIER
                    | IDENTIFIER
    """
    if len(p) == 4:
        p[0] = p[1] + [p[3]]
    else:
        p[0] = [p[1]]        


def p_assignment_statement(p):
    'assignment_statement : IDENTIFIER EQUALS expression'
    p[0] = AssignmentNode(IdentifierNode(p[1]), p[3])


def p_expression(p):
    '''expression : expression PLUS expression
                  | expression MINUS expression
                  | IDENTIFIER
                  | NUMBER_LITERAL'''
    if len(p) == 4:
        p[0] = BinaryOperationNode(p[1], p[2], p[3])
    else:
        p[0] = IdentifierNode(p[1]) if p.slice[1].type == "IDENTIFIER" else LiteralNode(p[1])


def p_empty(p):
    'empty :'
    pass

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