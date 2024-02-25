import ply.yacc as yacc
from tokenizer import tokens
from tokenizer import tla_code


# Placeholder for storing parsed module information
parsed_data = {}

precedence = (
    ('left', 'PLUS', 'MINUS'),
    ('left', 'STAR', 'DIVIDE'),
    ('nonassoc', 'LEFT_PAREN', 'RIGHT_PAREN'),  # Ensure proper grouping
)

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


class InitNode(ASTNode):
    def __init__(self, conditions):
        self.conditions = conditions  # List of conditions in the initial state


class NextNode(ASTNode):
    def __init__(self, transitions):
        self.transitions = transitions  # List of state transitions

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


class GraphNode(ASTNode):
    def __init__(self, identifier, body):
        self.identifier = identifier  # The name of the graph
        self.body = body  # List of graph statements (node and edge declarations)

    def __repr__(self):
        return f"Graph({self.identifier}, {self.body})"

class NodeDeclaration(ASTNode):
    def __init__(self, identifier):
        self.identifier = identifier  # The name of the node

    def __repr__(self):
        return f"Node({self.identifier})"

class EdgeDeclaration(ASTNode):
    def __init__(self, from_node, to_node):
        self.from_node = from_node  # Identifier of the starting node
        self.to_node = to_node  # Identifier of the ending node

    def __repr__(self):
        return f"Edge({self.from_node} -> {self.to_node})"

class InvariantNode(ASTNode):
    def __init__(self, expression):
        self.expression = expression  # The expression defining the invariant

    def __repr__(self):
        return f"Invariant({self.expression})"

class PropertyGoalNode(ASTNode):
    def __init__(self, expression):
        self.expression = expression  # The expression defining the property goal

    def __repr__(self):
        return f"PropertyGoal({self.expression})"


class SpecNode(ASTNode):
    def __init__(self, init, next, invariant=None, property_goal=None):
        self.init = init  # Initial state node
        self.next = next  # Next state node
        self.invariant = invariant  # Optional invariant node
        self.property_goal = property_goal  # Optional property goal node


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


# Define rules for `statement`, `variable_declaration`, `constants_declaration`, etc.

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
 


def p_graph_declaration(p):
    'graph_declaration : GRAPH IDENTIFIER graph_body'
    p[0] = GraphNode(p[2], p[3])


def p_graph_body(p):
    '''graph_body : graph_body graph_statement
                  | graph_statement'''
    if len(p) == 3:
        p[1].append(p[2])
        p[0] = p[1]
    else:
        p[0] = [p[1]]


def p_graph_statement(p):
    '''graph_statement : node_declaration
                       | edge_declaration'''
    p[0] = p[1]


def p_node_declaration(p):
    'node_declaration : NODE IDENTIFIER'
    p[0] = NodeDeclaration(p[2])


def p_edge_declaration(p):
    'edge_declaration : EDGE IDENTIFIER ARROW IDENTIFIER'
    p[0] = EdgeDeclaration(p[2], p[4])


def p_invariant_declaration(p):
    'invariant_declaration : INVARIANT expression'
    p[0] = InvariantNode(p[2])


def p_property_goal_declaration(p):
    'property_goal_declaration : GOAL expression'
    p[0] = PropertyGoalNode(p[2])


def p_assignment_statement(p):
    'assignment_statement : IDENTIFIER EQUALS expression'
    p[0] = AssignmentNode(IdentifierNode(p[1]), p[3])


def p_expression(p):
    '''expression : expression PLUS expression
                  | expression MINUS expression
                  | expression STAR expression
                  | expression DIVIDE expression
                  | IDENTIFIER
                  | NUMBER_LITERAL
                  | STRING_LITERAL'''
    if len(p) == 4:
        p[0] = BinaryOperationNode(p[1], p[2], p[3])
    elif p.slice[1].type == "IDENTIFIER":
        p[0] = IdentifierNode(p[1])
    else:
        p[0] = LiteralNode(p[1])


def p_expression_binary_operation(p):
    '''expression : expression PLUS expression
                  | expression MINUS expression
                  | expression STAR expression
                  | expression DIVIDE expression'''
    p[0] = BinaryOperationNode(left=p[1], operator=p[2], right=p[3])

def p_expression_group(p):
    'expression : LEFT_PAREN expression RIGHT_PAREN'
    p[0] = p[2]  # No new node needed, just use the expression's node


def p_expression_identifier(p):
    'expression : IDENTIFIER'
    p[0] = IdentifierNode(name=p[1])

def p_expression_literal(p):
    '''expression : NUMBER_LITERAL
                  | STRING_LITERAL'''
    p[0] = LiteralNode(value=p[1])


def p_variables_declaration_list(p):
    'variables_declaration : VARIABLE IDENTIFIER_LIST'
    p[0] = VariablesNode(variables=p[2])

def p_constants_declaration_list(p):
    'constants_declaration : CONSTANTS IDENTIFIER_LIST'
    p[0] = ConstantsNode(constants=p[2])

def p_identifier_list(p):
    '''IDENTIFIER_LIST : IDENTIFIER_LIST COMMA IDENTIFIER
                       | IDENTIFIER'''
    if len(p) == 4:
        p[1].append(p[3])
        p[0] = p[1]
    else:
        p[0] = [p[1]]


def p_init_declaration(p):
    'init_declaration : INIT EQUALS expression'
    p[0] = InitNode(p[3])



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