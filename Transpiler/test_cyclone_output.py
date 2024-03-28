


   #This is the Unit Testing file that we are using to test the output of our translator.
  #this test works by inputting information into each method in the translator.py file,
  #and then comparing the generated output with the expected output of the Cyclone Translator class.
   #you run this using this command: python -m unittest test_cyclone_output



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
        testing_data_1 = SetIndividualInfoNode("green", scope_node_testing_1)  #nested node, so we have to pass the testing info back up the ast tree
        testing_data_2 = SetIndividualInfoNode("yellow", scope_node_testing_2)
        
        tested_node = SetDefinitionNode("TestSetDefinition", equals = None, set_info=[testing_data_1, testing_data_2])    #we then pass the info that was passed up the ast tree to the node to be tested on 
        translator = CycloneTranslator()
        result = translator.visit(tested_node)
        expected_output = "    record TestSetDefinition{\n        int green where green >= 3;\n        int yellow where yellow >= 4;\n    };" 
        self.assertEqual(result, expected_output)


    def test_visit_FunctionDeclarationNode_1_singular_except(self):   #This method only handles the visit_FunctionDeclarationNode_1 instances with one Except Clause
        except_clause = ExceptClauseNode(attribute_1 = "Test", exclamation_mark = "!", dot = ".", attribute_2 = 'black', at = "@",  operator = '-', number = "1")  
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




    def test_visit_FunctionDeclarationNode_2(self):
        except_clause = ExceptClauseNode(attribute_1 = "Test", exclamation_mark = "!", dot = ".", attribute_2 = 'black', at = "@",  operator = '-', number = "1")  
        except_section = ExceptSectionNode(AND = None, next_value_attribute = None, equals = None, except_node=except_clause)

        tested_node = FunctionDeclarationNode_2("TestName", "=", "/\\", function_conditions = [], AND_1 = "/\\", function_conditions_1 = [], AND_2 = "/\\", function_conditions_2 = [], except_section = except_section)
        translator = CycloneTranslator()
        result = translator.visit(tested_node)
        expected_output = "    normal state TestName {\n\n        Can.black--;\n    }\n\n    abstract final state T{}"
        self.assertEqual(result, expected_output)



    def test_visit_NextStateRelationNode(self):
        next_state_statement_1 = NextStateNode("Green")
        next_state_statement_2 = NextStateNode("Red")
        next_state_statement_3 = NextStateNode("Blue")

        tested_node_1 = NextStateRelationNode(attribute = "hello", equals = "==", OR_1 = "\/", next_state_info_1 = next_state_statement_1, OR_2 = "\/", next_state_info_2 = next_state_statement_2, OR_3 = "\/", next_state_info_3 = next_state_statement_3, OR_4 = "\/", next_state_info_4 = next_state_statement_3)
        
        translator = CycloneTranslator()
        result_1 = translator.visit(tested_node_1)

        expected_output_1 = "    trans { Pick -> Green }\n    trans { Green ->  T where Can.white+Can.black==1;}\n    trans { Green -> Pick }\n\n    trans { Pick -> Red }\n    trans { Red ->  T where Can.white+Can.black==1;}\n    trans { Red -> Pick }\n\n    trans { Pick -> Blue }\n    trans { Blue ->  T where Can.white+Can.black==1;}\n    trans { Blue -> Pick }\n"    
    
        self.assertEqual(result_1, expected_output_1)



    def test_visit_TerminationHypothesisNode(self):
        attribute_dot_access_value = AttributeDotAccessNode(attribute_before_dot = "Can", attribute_after_dot = "test")    #passing the test data back up the ast tree
        conditional_if_node_value = Conditional_IF_Node(dot_access = attribute_dot_access_value, MODULUS = "%", NUMBER_LITERAL_1 = "test_value", equals = "=", NUMBER_LITERAL_2 = "test_value_2")
        conditional_statement_info_value = ConditionalStatementInfoNode(IF = "test", conditional_statement_if = conditional_if_node_value, THEN = "test", conditional_statement_then = "test", ELSE = "test", conditional_statement_else = "test")

        tested_node = TerminationHypothesisNode(operator = "test_operator", statement = conditional_statement_info_value)
        translator = CycloneTranslator()
        result = translator.visit(tested_node)
        expected_result = "      goal { \n        assert  !(((initial(Can.test) % 2 == 0) => (Can.black == 1)) ||\n                ((initial(Can.test) % 2 != 0) =>  (Can.white==1)));\n\n        check for 4\n    }\n  // Skipping irrelevant node: str\n  // Skipping irrelevant node: str"
        self.assertEqual(result, expected_result)
