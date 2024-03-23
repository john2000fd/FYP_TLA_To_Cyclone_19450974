"""
   This is the Unit Testing file that we are using to test the output of our translator.
   this test works by inputting information into each method in the translator.py file
   and then comparing the generated output with the expected output of the Cyclone Translator class
   you run this using this command: python -m unittest test_cyclone_output

"""




import unittest    #Importing necessary modules for the testing process
from translator import *
from tla_parser import *

 
class Unit_TestCycloneTranslator(unittest.TestCase):       #This is our unit testing class that handles testing each method
    def test_visit_ModuleNode(self):   #This tests our overall ModuleNode
        tested_node = ModuleNode("TestModule", extends = None, statements = [])
        cyclone_translator = CycloneTranslator()
        result = cyclone_translator.visit(tested_node)
        expected_output = "graph TestModule {\n\n}"  #This is our expected output we test against the generated output
        self.assertEqual(result, expected_output)  #we assertEqual the result vs the expected_result to see if they are the same, if so the test is passed

    def test_visit_SetDefinitionNode(self):
        scope_node_testing_1 = SetScopeNode("3", "4")       #We need two scope_node_testing variables so we can check if the SetDefinitionNode can properly handle two different scopes and testing datya
        scope_node_testing_2 = SetScopeNode("4", "6")
        testing_data_1 = SetIndividualInfoNode("green", scope_node_testing_1)
        testing_data_2 = SetIndividualInfoNode("yellow", scope_node_testing_2)
        
        tested_node = SetDefinitionNode("TestSetDefinition", equals = None, set_info=[testing_data_1, testing_data_2])
        translator = CycloneTranslator()
        result = translator.visit(tested_node)
        expected_output = "    record TestSetDefinition{\n        int green where green >= 3;\n        int yellow where yellow >= 4;\n    };" 
        self.assertEqual(result, expected_output)


    def test_visit_FunctionDeclarationNode_1_singular_except(self):   #This method only handles the visit_FunctionDeclarationNode_1 instances with one Except Clause
        except_clause = ExceptClauseNode(attribute_1 = "Test", exclamation_mark = "!", dot = ".", attribute_2 = 'black', at = "@",  operator = '-', number = "1")  # Simplified for demonstration
        except_section = ExceptSectionNode(AND = None, next_value_attribute = None, equals = None, except_node=except_clause)

        tested_node = FunctionDeclarationNode_1("TestName", "=", "/\\", function_conditions = [], AND_1 = "And", function_conditions_1 = [], except_section = except_section)
        translator = CycloneTranslator()
        result = translator.visit(tested_node)
        expected_output = "    abstract start state Pick {}\n\n\n    normal state TestName {\n\n        Can.black--;\n    }"
        self.assertEqual(result, expected_output)




    def test_visit_FunctionDeclarationNode_1_multiple_except(self):   #While this method handles the  visit_FunctionDeclarationNode_1 instances with multiple except clauses
        except_clause = MultipleExceptClauseNode(attribute_1 = "Test", exclamation_mark_1 = "!", dot_1 = ".", attribute_2 = 'black', at_1 = "@",  operator_1 = '+', number_1 = "1", exclamation_mark_2 = "!", dot_2 = ".", attribute_3 = "test", at_2 = "@", operator_2 = "-", number_2 = "1")
        except_section = ExceptSectionNode(AND = None, next_value_attribute = None, equals = None, except_node=except_clause)
        
        tested_node = FunctionDeclarationNode_1("TestName", "=", "/\\", function_conditions = [], AND_1 = "And", function_conditions_1 = [], except_section = except_section)
        translator = CycloneTranslator()
        result = translator.visit(tested_node)
        expected_output = "    abstract start state Pick {}\n\n\n    normal state TestName {\n\n        Can.black++;\n        Can.white-=1;\n    }"
        self.assertEqual(result, expected_output)