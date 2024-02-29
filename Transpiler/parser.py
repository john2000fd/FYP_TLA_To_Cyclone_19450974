import ply.yacc as yacc
from tokenizer import tokens
from tokenizer import tla_code


# Placeholder for storing parsed module information
parsed_data = {}

#This precedence table determines the precedence of operators in the parser, this will contain the number of shift/reduce conflicts 
precedence = (
    ('left', 'OR'),  # Logical OR
    ('left', 'AND'),  # Logical AND
    ('nonassoc', 'EQUALS_ASSIGNMENT', 'NOT_EQUALS'),  # Equality and inequality
    ('nonassoc', 'LESS_THAN', 'LESS_OR_EQ', 'GREATER_THAN', 'GREATER_OR_EQ'),  # Relational operators
    ('left', 'PLUS', 'MINUS'),  # Addition and subtraction
    ('left', 'STAR', 'DIVIDE', 'MODULUS'),  # Multiplication, division, modulo
    #('right', 'EXP'),  # Exponentiation
    #('right', 'UMINUS'),  # Unary minus operator
    ('nonassoc', 'LEFT_PAREN', 'RIGHT_PAREN'),  # Parentheses for grouping
)







#FUNCTIONS FOR PARSING

# Parsing the module with optional extends and body (declarations, assignments, etc.)
def p_module(p):
    '''module : MODULE_WRAPPER MODULE attribute MODULE_WRAPPER extends statements
              | MODULE_WRAPPER MODULE attribute MODULE_WRAPPER statements'''
    if len(p) == 7:
        p[0] = ModuleNode(name=p[3], extends=p[5], declarations=p[6])
    else:
        p[0] = ModuleNode(name=p[3], extends=None, declarations=p[5])


def p_attribute(p):
    'attribute : ATTRIBUTE'
    p[0] = p[1]  


def p_extends(p):
    '''extends : EXTENDS names'''
    p[0] = p[1]     

    

def p_names(p):
    '''names : names COMMA attribute
             | attribute'''
    if len(p) == 4:
        p[0] = p[1] + [p[3]]
    else:
        p[0] = [p[1]]


#This section deals with the parsing of various declarations, this includes keywords, variables, constants etc

def p_statements(p):
    '''statements : statements statement
                    | statement'''
    if len(p) == 3:
        p[1].append(p[2])
        p[0] = p[1]
    else:
        p[0] = [p[1]]


   
# Define rules for `statement`, `variable_declaration`, `constants_declaration`, etc.


def p_statement(p):
    '''statement :   constants_statement
                   | variables_statement
                   | assignment_statement
                   | assume_statement'''
    p[0] = p[1]


def p_constants_statement(p):
    '''constants_statement : CONSTANTS names'''
    p[0] = ConstantsNode(constants=p[2])


def p_variables_statement(p):
    '''variables_statement : VARIABLES names'''
    p[0] = VariablesNode(variables=p[2])


def p_assume_statement(p):
    '''assume_statement: ASSUME expression AND expression'''
    p[0] = AssumeNode(p[2], p[4])



def p_expression(p):                                      #this section of code was made with help from ChatGPT language model
    '''expression : expression PLUS expression
                  | expression MINUS expression
                  | expression STAR expression
                  | expression DIVIDE expression
                  | set_membership
                  | comparison
                  | attribute
                  | NUMBER_LITERAL
                  | STRING_LITERAL'''
    
    if len(p) == 4:
        # Handles binary operations
        p[0] = BinaryOperationNode(p[1], p[2], p[3])
    elif p.slice[1].type == "ATTRIBUTE":
        # Handles identifiers
        p[0] = IdentifierNode(p[1])
    else:
        # Handles literals (numbers and strings)
        p[0] = LiteralNode(p[1])


def p_comparison(p):
    '''comparison : attribute comparison_rule number_literal
                  | attribute comparison_rule attribute'''
    p[0] = ComparisonNode(p[1], p[2], p[3])
    
def p_comparison_rule(p):
    '''comparison :   GREATER_OR_EQ
                    | LESS_OR_EQ
                    | GREATER_THAN                         
                    | LESS_THAN '''
    p[0] = p[1]
    
def p_set_membership(p):
    '''set_membership : attribute IN_A_SET Nat '''
    p[0] = p[1]














'''
def p_graph_declaration(p):
    'graph_declaration : GRAPH ATTRIBUTE graph_body'
    p[0] = GraphNode(p[2], p[3])
'''

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
    '''node_declaration : NODE ATTRIBUTE'''
    p[0] = NodeDeclaration(p[2])


def p_edge_declaration(p):
    '''edge_declaration : EDGE ATTRIBUTE ARROW ATTRIBUTE'''
    p[0] = EdgeDeclaration(p[2], p[4])


def p_invariant_declaration(p):
    '''invariant_declaration : INVARIANT expression'''
    p[0] = InvariantNode(p[2])


def p_property_goal_declaration(p):
    '''property_goal_declaration : GOAL expression'''
    p[0] = PropertyGoalNode(p[2])


def p_assignment_statement(p):
    'assignment_statement : ATTRIBUTE EQUALS_ASSIGNMENT expression'
    p[0] = AssignmentNode(IdentifierNode(p[1]), p[3])






#Grouping expressions
def p_expression_group(p):
    'expression : LEFT_PAREN expression RIGHT_PAREN'
    p[0] = p[2]  # Grouped expression, no node needed







def p_init_declaration(p):
    'init_declaration : INIT EQUALS_DEFINITIONS expression'
    p[0] = InitNode(p[3])



def p_empty(p):
    'empty :'
    pass

# Error handling rule for syntax errors
def p_error(p):
    if p:
        print(f"Syntax error at token '{p.type}', value: '{p.value}', line: {p.lineno}, position: {p.lexpos}")
    else:
        print("Syntax error at EOF")




#THESE ARE OUR NODES FOR THE ABSTRACT SYNTAX TREE
class ASTNode:     #AST classes 
    pass

class ModuleNode(ASTNode):
    def __init__(self, name, extends, declarations):
        self.name = name
        self.extends = extends
        self.declarations = declarations


class ExtendsNode(ASTNode):
    def __init__(self, extended_modules):
        self.extended_modules = extended_modules


class ConstantsNode(ASTNode):
    def __init__(self, constants):
        self.constants = constants  # List of constant names

class VariablesNode(ASTNode):
    def __init__(self, variables):
        self.variables = variables  # List of variable names


class AssumeNode(ASTNode):
    def __init__(self, expression_1, expression_2):
       self.expression_1 = expression_1
       self.expression_2 = expression_2
       


class ComparisonNode(ASTNode):
    def __init__(self, left, operator, right):
        self.left = left
        self.operator = operator
        self.right = right


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




# Build the parser
parser = yacc.yacc()


result = parser.parse(tla_code)
print(result)
print(parsed_data)