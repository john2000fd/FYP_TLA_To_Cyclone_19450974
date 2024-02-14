import unittest
import ast_for_tla
from ast_for_tla import ModuleNode, VariableDeclarationNode, InitNode, NextNode, InvariantNode, GoalNode, \
    BinaryExpressionNode, UnaryExpressionNode, IdentifierNode, LiteralNode, GraphNode, GraphEdge, \
    GraphEdgeLabel, GraphAttributeNode, GraphConstraintNode, FunctionCallNode, TupleNode, SetNode, \
    RecordNode, IfNode, LetNode, CaseNode, FunctionNode, QuantifierNode, OperatorNode, Operator,\
    construct_ast
import tokenization
import tokenize


class TestASTIntegration(unittest.TestCase):
    def test_graph_based_specification(self):
        tla_code = """
        EXTENDS Naturals

        GRAPH
          NODE node1
          NODE node2
          NODE node3

          EDGE node1 -> node2
          EDGE node2 -> node3

          LABEL "label1" ON node1 -> node2
          LABEL "label2" ON node2 -> node3

        VARIABLE count

        Init == (* Initial values *)
                /\ count = 0

        Next == (* State transition function *)
                /\ count' = count + 1

        Spec == Init /\ [][Next]_count

        Invariant == (* Invariant property *)
                     [](count >= 0)

        Goal == (* System properties to check *)
                /\ count <= 10

        CHECK Goal
        """

        expected_ast_structure = [
            ModuleNode(
                name='Naturals',
                extends=None,
                variables=[VariableDeclarationNode(name='count', type=None)],
                init=InitNode(expressions=[BinaryExpressionNode(left=IdentifierNode(name='count'), operator='==', right=LiteralNode(value=0))])),
            NextNode(expressions=[BinaryExpressionNode(left=IdentifierNode(name='count'), operator='==', right=BinaryExpressionNode(left=IdentifierNode(name='count'), operator='+', right=LiteralNode(value=1)))]),
            InvariantNode(expression=UnaryExpressionNode(operator='[]', operand=BinaryExpressionNode(left=IdentifierNode(name='count'), operator='>=', right=LiteralNode(value=0)))),
            GoalNode(expression=BinaryExpressionNode(left=IdentifierNode(name='count'), operator='<=', right=LiteralNode(value=10)))
        ]

        # Tokenize the TLA+ code
        tokens = tokenize.tokenize(tla_code)

        # Ensure that tokens is a list of tokens
        self.assertIsInstance(tokens, list)

        # Parse TLA+ code only if tokens is a list
        if isinstance(tokens, list):
            # Parse TLA+ code
            ast = ast_for_tla.construct_ast(tokens)

        # Assert the expected structure matches the generated AST
        self.assertEqual(ast, expected_ast_structure)

if __name__ == '__main__':
    unittest.main()