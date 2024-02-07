class ModuleNode:
    def __init__(self, name, extends=None, variables=None, init=None, next=None, invariant=None, goal=None):
        self.name = name
        self.extends = extends
        self.variables = variables or []
        self.init = init
        self.next = next or []
        self.invariant = invariant
        self.goal = goal

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