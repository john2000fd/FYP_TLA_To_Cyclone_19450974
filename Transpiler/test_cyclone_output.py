import unittest
from translator import *

 
# This is the Unit Testing program that we are using to test the output of the translator.py file


# We have to create testing versions of our AST nodes to run unit tests on them.  


class TestingModuleNode:
    def __init__(self, name, statements):
        self.name = name
        self.statements = statements

class TestingSetDefinitionNode:
    def __init__(self, attribute, set_info):
        self.attribute = attribute
        self.set_info = set_info

class TestingSetIndividualInfoNode:
    def __init__(self, attribute, scope, start_value):
        self.attribute = attribute
        self.scope = scope
        self.scope = start_value


class Unit_TestCycloneTranslator(unittest.TestCase):
    def test_visit_ModuleNode(self):
        node = TestingModuleNode("TestModule", [])
        translator = CycloneTranslator()
        result = translator.visit(node)
        expected_output = "graph TestModule {}\n"  # Adjust based on expected output
        self.assertEqual(result, expected_output)

    def test_visit_SetDefinitionNode(self):
        # Assuming SetIndividualInfoNode and other necessary mocks are defined
        node = TestingSetDefinitionNode("TestRecord", [TestingSetIndividualInfoNode("testAttribute", "testScope", "test_stat_value")])
        translator = CycloneTranslator()
        result = translator.visit(node)
        expected_output = "record TestRecord{\n    int testAttribute where testAttribute >= testScope;\n    };"  # Adjust based on expected output
        self.assertEqual(result, expected_output)