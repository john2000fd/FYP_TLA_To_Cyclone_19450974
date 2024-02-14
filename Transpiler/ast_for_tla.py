import re


class ModuleNode:
    def __init__(self, name, extends=None, variables=None, init=None, next=None, invariant=None, goal=None, graph_nodes=None, graph_edges=None, graph_edge_labels=None):
        self.name = name
        self.extends = extends
        self.variables = variables or []
        self.init = init
        self.next = next or []
        self.invariant = invariant
        self.goal = goal
        self.graph_nodes = graph_nodes or []
        self.graph_edges = graph_edges or []
        self.graph_edge_labels = graph_edge_labels or [] 

class VariableDeclarationNode:
    def __init__(self, name, type):
        self.name = name
        self.type = type

class InitNode:
    def __init__(self, expressions):
        self.expressions = expressions

class NextNode:
    def __init__(self, expressions):
        self.expressions = expressions

class InvariantNode:
    def __init__(self, expression):
        self.expression = expression

class GoalNode:
    def __init__(self, expression):
        self.expression = expression

class ExpressionNode:
    pass

class BinaryExpressionNode(ExpressionNode):
    def __init__(self, left, operator, right):
        self.left = left
        self.operator = operator
        self.right = right

class UnaryExpressionNode(ExpressionNode):
    def __init__(self, operator, operand):
        self.operator = operator
        self.operand = operand

class FunctionCallNode(ExpressionNode):
    def __init__(self, function_name, arguments):
        self.function_name = function_name
        self.arguments = arguments

class IdentifierNode(ExpressionNode):
    def __init__(self, name):
        self.name = name

class LiteralNode(ExpressionNode):
    def __init__(self, value):
        self.value = value

class TupleNode(ExpressionNode):
    def __init__(self, elements):
        self.elements = elements

class SetNode(ExpressionNode):
    def __init__(self, elements):
        self.elements = elements

class RecordNode(ExpressionNode):
    def __init__(self, fields):
        self.fields = fields

class IfNode(ExpressionNode):
    def __init__(self, condition, true_branch, false_branch):
        self.condition = condition
        self.true_branch = true_branch
        self.false_branch = false_branch

class LetNode(ExpressionNode):
    def __init__(self, bindings, body):
        self.bindings = bindings
        self.body = body

class CaseNode(ExpressionNode):
    def __init__(self, expression, cases, other):
        self.expression = expression
        self.cases = cases
        self.other = other

class FunctionNode(ExpressionNode):
    def __init__(self, parameters, body):
        self.parameters = parameters
        self.body = body

class QuantifierNode(ExpressionNode):
    def __init__(self, quantifier, variables, condition):
        self.quantifier = quantifier
        self.variables = variables
        self.condition = condition

class OperatorNode(ExpressionNode):
    def __init__(self, value):
        self.value = value


class GraphAttributeNode:
    def __init__(self, name, value):
        self.name = name
        self.value = value


class GraphNode:
    def __init__(self, name):
        self.name = name
        self.attributes = attributes or []


class GraphEdge:
    def __init__(self, source, target):
        self.source = source
        self.target = target
        self.attributes = attributes or []


class GraphConstraintNode:
    def __init__(self, condition):
        self.condition = condition        


class GraphEdgeLabel:
    def __init__(self, label, edge):
        self.label = label
        self.edge = edge                

class Operator:
    # Define constants for different operator types
    AND = '/\\'
    ARROW = '->'
    EQUALS = '=='
    ASTERISK = '*'
    LPAREN = '('
    RPAREN = ')'
    SEMICOLON = ';'        

def parse_literal(literal_value):
    # Parse the literal value based on its type
    if literal_value == 'true' or literal_value == 'false':
        return True if literal_value == 'true' else False
    elif '.' in literal_value:
        return float(literal_value)
    else:
        return int(literal_value)

def parse_expression(expression_str):               #TO-DO##########################
    
     # Remove leading and trailing whitespace
    expression_str = expression_str.strip()

    # Check if the expression is an identifier
    if re.match(r'^[A-Za-z_][A-Za-z0-9_]*$', expression_str):
        return IdentifierNode(name=expression_str)

    # Check if the expression is a literal (integer, float, boolean)
    if re.match(r'^[0-9]+(?:\.[0-9]*)?$', expression_str):
        return LiteralNode(value=int(expression_str))
    elif re.match(r'^[0-9]*\.[0-9]+$', expression_str):
        return LiteralNode(value=float(expression_str))
    elif expression_str in ['true', 'false']:
        return LiteralNode(value=(expression_str == 'true'))

    # Check if the expression is a binary expression
    for operator in ['+', '-', '*', '/', '==', '<', '>', '>=', '<=']:
        left, operator, right = expression_str.partition(operator)
        if operator:
            return BinaryExpressionNode(
                left=parse_expression(left),
                operator=operator.strip(),
                right=parse_expression(right)
            )

    # If none of the above, raise an error
    raise ValueError(f"Unable to parse expression: {expression_str}")

def construct_ast(tokens):
    # Initialize variables to store information during parsing
    current_module = None
    current_variables = None
    current_init = None
    current_next = []
    current_invariant = None
    current_goal = None
    current_graph_nodes = []
    current_graph_edges = []
    current_graph_edge_labels = []
    
    # Define lists to store nodes
    modules = []
    variables = []
    init = []
    next_nodes = []
    invariants = []
    goals = []

    # Iterate over tokens
    for token_type, token_value in tokens:
        #print(f"Token Type: {token_type}, Token Value: {token_value}")
        if token_type == 'EXTENDS':
            print("Creating ModuleNode with name:", token_value.strip())                 #print statements are added to see construction process
            # Create a ModuleNode
            current_module = ModuleNode(name=token_value.strip())
        elif token_type == 'VARIABLE':
            # Create VariableDeclarationNodes
            print("Creating VariableDeclarationNodes with names:", [name.strip() for name in token_value.split(',')])
            current_variables = [VariableDeclarationNode(name.strip(), None) for name in token_value.split(',')]
        elif token_type == 'INIT':
            # Create an InitNode
            print("Creating InitNode") 
            current_init = InitNode(expressions=[])
        elif token_type == 'NEXT':
            # Create a NextNode
            print("Creating Nextnode")
            current_next.append(NextNode(expressions=[]))
        elif token_type == 'INVARIANT':
            # Create an InvariantNode
            print("Creating InvariantNode")
            current_invariant = InvariantNode(expression=None)
        elif token_type == 'GOAL':
            # Create a GoalNode
            print("Creating GoalNode")
            current_goal = GoalNode(expression=None)
        elif token_type == 'COMMENT':
            # Skip comments
            print("Skipping comment")
            continue
        elif token_type == 'GRAPH_NODE':
            # Create a GraphNode
            print("Creating GraphNode with name:", token_value.strip())
            graph_node = GraphNode(name=token_value.strip())
            current_graph_nodes.append(graph_node)
        elif token_type == 'GRAPH_EDGE':
            # Create a GraphEdge
            source, target = token_value.split('->')
            print("Creating GraphEdge from", source.strip(), "to", target.strip())
            graph_edge = GraphEdge(source=source.strip(), target=target.strip())
            current_graph_edges.append(graph_edge)
        elif token_type == 'GRAPH_EDGE_LABEL':
            # Create a GraphEdgeLabel
            label, edge = token_value.split(' ON ')
            edge = edge.split('->')
            print("Creating GraphEdgeLabel with label:", label.strip(), "on edge from", edge[0].strip(), "to", edge[1].strip())
            graph_edge_label = GraphEdgeLabel(label=label.strip(), edge=GraphEdge(source=edge[0].strip(), target=edge[1].strip()))
            current_graph_edge_labels.append(graph_edge_label)
        elif token_type == 'MODULE_END':
            # End of module, combine nodes into ModuleNode
            print("End of module, combining nodes into ModuleNode")
            if current_module:
                current_module.variables = current_variables
                current_module.init = current_init
                current_module.next = current_next
                current_module.invariant = current_invariant
                current_module.goal = current_goal
                current_module.graph_nodes = current_graph_nodes
                current_module.graph_edges = current_graph_edges
                current_module.graph_edge_labels = current_graph_edge_labels
                modules.append(current_module)
                # Reset variables for the next module
                current_module = None
                current_variables = None
                current_init = None
                current_next = []
                current_invariant = None
                current_goal = None
                current_graph_nodes = []
                current_graph_edges = []
                current_graph_edge_labels = []

    # Return constructed AST
    return modules