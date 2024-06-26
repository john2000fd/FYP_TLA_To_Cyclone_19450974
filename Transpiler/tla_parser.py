



#This is our PLY Yacc parser, This parser uses LR-parsing, LR parsing is a bottom up technique that tries to recognize the right-hand-side of various grammar rules. 
#Whenever a valid right-hand-side is found in the input
#the appropriate action code is triggered and the right side grammar symbols are replaced by the grammar symbol on the left-hand-side.

#An AST is generated using the functions in the second half of this file

#importing necessary modules and values from the tokenizer
import ply.yacc as yacc
from tokenizer import tokens
from tokenizer import tla_code









#This precedence table determines the precedence of operators in the parser, this will contain the number of shift/reduce conflicts encountered during parsing
#ordered from lowest to highest precedence
  
precedence = (
    ('left', 'EQUIVALENCE_OPERATOR'),
    ('left', 'AND'),  # Logical AND
    ('nonassoc', 'EQUALS_DEFINITIONS', 'NOT_EQUALS'),  # Equality and inequality
    ('nonassoc', 'LESS_THAN', 'LESS_OR_EQ', 'GREATER_THAN', 'GREATER_OR_EQ'),  # Relational operators
    ('left', 'PLUS', 'MINUS'),  # Addition and subtraction
    ('left', 'STAR', 'DIVIDE', 'MODULUS'),  # Multiplication, division, modulo
    ('nonassoc', 'LEFT_PAREN', 'RIGHT_PAREN'),  # Parentheses for grouping
)



#FUNCTIONS FOR PARSING SECTION

#Each parsing function recognizes specific TLA syntax, such as module declarations
#When a particular syntax pattern is recognized, these functions construct an instance of an AST node representing that syntax.
#The nodes are designed to capture essential details of the language constructs, such as names, attributes, expressions, and relationships to other parts of the code.


# Parsing the module start with optional extends and body 
#The parsing function code was developed with guidance from PLY Lex Yacc documentation:  https://www.dabeaz.com/ply/ply.html#ply_nn4
def p_module(p):
    '''module : MODULE_WRAPPER MODULE attribute MODULE_WRAPPER extends statements
              | MODULE_WRAPPER MODULE attribute MODULE_WRAPPER statements'''
    if len(p) == 7:
        p[0] = ModuleNode(p[3], extends=p[5], statements=p[6])
    else:
        p[0] = ModuleNode(name=p[3], extends=None, statements=p[5])

#function for handling attribute tokens
def p_attribute(p):
    '''attribute : ATTRIBUTE'''
    p[0] = p[1]  

#function that handles dot accesss constructs, such as test.test
def p_dot_access(p):
    '''dot_access : attribute DOT attribute
                  | NEXT_VALUE_OF_ATTRIBUTE DOT attribute'''
    p[0] = AttributeDotAccessNode(p[1], p[3])

#function for handling the extends declaration in TLA for modules such as Naturals etc
def p_extends(p):
    '''extends : EXTENDS names'''
    p[0] = p[1]     

    
#this function uses recursion to recursively append the end of a previously matched list by a newly matched element each time until there are no further elements to match.
def p_names(p):
    '''names : names COMMA attribute
             | attribute'''
    if len(p) == 4:
        p[0] = p[1] + [p[3]]                                    
         
    else:
        p[0] = [p[1]]
       
        

#This section deals with the parsing of various statements, this includes keywords, variables, constants etc.

def p_statements(p):
    '''statements : statements statement
                    | statement'''
    if len(p) == 3:             #recursion to recursively append the end of a previously matched list by a newly matched element each time until there are no further elements to match.
        p[1].append(p[2])
        p[0] = p[1]
    else:
        p[0] = [p[1]]


   
# Define rules for various statements, this function handles the path that the functions will take to build AST nodes by passing it through a specific path based on the tokens values

#code was developed with guidance from PLY Lex Yacc documentation:  https://www.dabeaz.com/ply/ply.html#ply_nn4
def p_statement(p):
    '''statement :   constants_statement
                   | variables_statement
                   | assume_statement
                   | type_invariant
                   | set_definition
                   | bean_value_count
                   | function_declaration
                   | termination_statement
                   | next_state_relation
                   | action_formula_definition
                   | liveness_property
                   | loop_invariant
                   | termination_hypothesis
                   | spec_definition
                   | theorem_definition
                   | init'''
    p[0] = p[1]

#function to handle constant declarations, passes info to a new constantsnode in the AST
def p_constants_statement(p):
    '''constants_statement : CONSTANTS names'''
    p[0] = ConstantsNode(constants=p[2])

#function to handle variable declarations, passes info to a new variablesnode in the AST
def p_variables_statement(p):
    '''variables_statement : VARIABLES names'''
    p[0] = VariablesNode(variables=p[2])

#function to handle assume statements, passes info to a new assumenode in the AST
def p_assume_statement(p):
    '''assume_statement : ASSUME attribute IN_A_SET Nat AND attribute GREATER_OR_EQ NUMBER_LITERAL'''
    p[0] = AssumeNode(p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8])


#function to handle various different types of expressions in TLA,
#this section handles the path that the functions will take to build AST nodes by passing it through a specific path based on the tokens values
def p_expression(p):                                      #this section of code was made with help from ChatGPT 4 language model https://chat.openai.com/?model=text-davinci-002-render-sha
                                                          #Prompt: 'Can you provide guidance on handling the expression tokens in my parser?'
    '''expression : expression PLUS expression
                  | expression MINUS expression
                  | expression STAR expression
                  | expression DIVIDE expression
                  | set_membership
                  | comparison
                  | attribute
                  | type_invariant_expression
                  | NUMBER_LITERAL
                  | STRING_LITERAL'''
    
    
    p[0] = NumberNode(p[1])

#function to handle the type invariant expression of the TLA file, creates a TypeInvariantExpressionNode
def p_type_invariant_expression(p):
    '''type_invariant_expression : attribute IN_A_SET attribute'''
    p[0] = TypeInvariantExpressionNode(p[1], p[2], p[3])

#function to handle comparison operations in TLA, creates a ComparisonNode
def p_comparison(p):
    '''comparison : attribute comparison_rule NUMBER_LITERAL
                  | attribute comparison_rule attribute'''
    p[0] = ComparisonNode(p[1], p[2], p[3])
    
#connected function to p_comparison, this determines the comparison operator used eg >
def p_comparison_rule(p):
    '''comparison_rule :   GREATER_OR_EQ
                    | LESS_OR_EQ
                    | GREATER_THAN                         
                    | LESS_THAN '''
    p[0] = p[1]

#function to handle set membership statements in TLA    
def p_set_membership(p):
    '''set_membership : attribute IN_A_SET Nat '''
    p[0] = p[1]

#function to determine what type of equality operator is being used, = or ==
def p_equals(p):
    '''equals : EQUALS_DEFINITIONS
              | EQUALS_EQUALITY'''
    p[0] = p[1]

#function to handle a set definition, creates a SetDefinitionNode, aspects such as equals and set_info are sent to other functions for processing
def p_set_definition(p):
    '''set_definition : attribute equals LEFT_SQR_BRACKET set_info RIGHT_SQR_BRACKET'''
    p[0] = SetDefinitionNode(p[1], p[2], p[4])




def p_set_info(p):
    '''set_info : set_info COMMA set_individual_info
                      | set_individual_info'''
    if len(p) == 4:
        p[0] = p[1] + [p[3]]
    else:
        p[0] = [p[1]]

def p_set_individual_info(p):
    '''set_individual_info : ATTRIBUTE COLON set_scope'''
    p[0] = SetIndividualInfoNode(p[1],p[3])


def p_set_scope(p):
    '''set_scope : NUMBER_LITERAL DOT DOT attribute'''
    p[0] = SetScopeNode(p[1], p[4])        


def p_type_invariant(p):
    '''type_invariant : attribute equals expression'''
    p[0] = TypeInvariantNode(p[1], p[2], p[3])


def p_init(p):
    '''init : INIT equals attribute IN_A_SET init_set_statement'''
    p[0] = InitNode(p[1], p[2], p[3], p[4], p[5])


def p_init_set_statement(p):
    '''init_set_statement : LEFT_BRACE attribute IN_A_SET attribute COLON order'''
    p[0] = InitSetStatementNode(p[2], p[3], p[4], p[5], p[6])


def p_order(p):
    '''order : dot_access PLUS dot_access IN_A_SET range_of_values'''
    p[0] = SetValueNode(p[1], p[2], p[3], p[4], p[5])


def p_range_of_values(p):
    '''range_of_values :  NUMBER_LITERAL DOT DOT attribute RIGHT_BRACE'''
    p[0] = InitSetRangeOfValuesNode(p[1], p[4])

#These two node represents the equation of two bean values eg c.black + c.white values  

def p_bean_value_count(p):
    '''bean_value_count : attribute equals bean_equation'''
    p[0] = BeanValueCountNode(p[1], p[3])



def p_bean_equation(p):
    '''bean_equation : dot_access PLUS dot_access'''          
    p[0] = AdditionResultNode(p[1], p[3])




#this section of code was made with help from ChatGPT 4 language model https://chat.openai.com/?model=text-davinci-002-render-sha
#Prompt: 'Function_declaration function seems to not be handling certain code, can you identify the reasons for this?'
#Rule handling all of our funcions in TLA, for example for this: picking two black beans, removing them, then replacing with one black bean

def p_function_declaration(p):
    '''function_declaration : attribute equals AND function_info AND function_info except_section
                            | attribute equals AND function_info AND function_info AND function_info except_section'''
    if len(p) == 8:
        p[0] = FunctionDeclarationNode_1(p[1], p[2], p[3], p[4], p[5], p[6], p[7])
    else:
        p[0] = FunctionDeclarationNode_2(p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9])    

#handles the high level info of the function

def p_function_info(p):
    '''function_info : attribute DOT attribute comparison_rule NUMBER_LITERAL
                     | attribute comparison_rule NUMBER_LITERAL'''
    if len(p) == 6:
        p[0] = FunctionInfoNode(attribute_1 = p[1], dot = p[2], attribute_2 = p[3], comparison_rule = p[4], number = p[5])
    else:
        p[0] = FunctionInfoNode(attribute_1 = p[1], dot = None, attribute_2 = None, comparison_rule = p[2], number = p[3])   


#this function handles the specific conditions in these functions
#recursion is used to call the function recursively to handle all conditions of a function sepersted by logical AND, OR
def p_function_conditions(p):
    '''function_conditions : function_condition
                           | function_conditions AND function_condition
                           | function_conditions OR function_condition'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = p[1] + [p[3]]
        

#function to handle different types of conditions that are a part of various functions.
def p_function_condition(p):
    '''function_condition : attribute comparison_rule NUMBER_LITERAL
                          | attribute equals NUMBER_LITERAL
                          | UNCHANGED attribute
                          | LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET attribute RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE
                          | WEAK_FAIRNESS ATTRIBUTE_MAY_CHANGE LEFT_PAREN attribute RIGHT_PAREN
                          | attribute
                          | INIT
                          | EventuallyTerminates
                          | LoopInvariant
                          | TerminationHypothesis
                          | attribute DOT attribute comparison_rule NUMBER_LITERAL'''
    if len(p) == 4:
        p[0] = FunctionConditionNoDotNode(p[1], p[2], p[3])
    elif len(p) == 3:
        p[0] = FunctionUNCHANGEDNode(p[1], p[2])
    elif len(p) == 2:
        p[0] = FunctionNameNode(p[1])
    elif len(p) == 5:
        p[0] = FunctionConditionDotNode(p[1], p[2], p[3], p[4], p[5])

    
#This function handles the except section of our transition function    
def p_except_section(p):     
    '''except_section : AND NEXT_VALUE_OF_ATTRIBUTE equals except_clause'''
    p[0] = ExceptSectionNode(p[1],p[2], p[3], p[4])

#This handles our except clause in the except section
def p_except_clause(p):      
    '''except_clause : LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET
                     | LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT PLUS NUMBER_LITERAL COMMA EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET'''
    if len(p) == 12:
        p[0] = ExceptClauseNode(p[2], p[4], p[5], p[6], p[8], p[9], p[10])
    else:
        p[0] = MultipleExceptClauseNode(p[2], p[4], p[5], p[6], p[8], p[9], p[10], p[12], p[13], p[14], p[16], p[17], p[18])    

    
#This function handles our termination section in the TLA file
def p_termination_statement(p):
    '''termination_statement : attribute equals AND termination_info AND termination_info'''
    p[0] = TerminationStatementNode(p[1], p[2], p[3], p[4], p[5], p[6])



def p_termination_info(p):
    '''termination_info : attribute equals NUMBER_LITERAL
                        | UNCHANGED attribute'''
    if len(p) == 4:
        p[0] = TerminationInfoNode_1(p[1], p[2], p[3])
    else:
        p[0] = TerminationInfoNode_2(p[1], p[2])
    



#This handles our next state relation section in the TLA file
def p_next_state_relation(p):
    '''next_state_relation : attribute equals OR next_state_info OR next_state_info OR next_state_info OR next_state_info'''
    p[0] = NextStateRelationNode(p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10])



def p_next_state_info(p):
    '''next_state_info : attribute'''
    p[0] = NextStateNode(p[1])


def p_action_formula_definition(p): 
    '''action_formula_definition : attribute equals action_formula'''
    p[0] = FormulaDefinitionNode(p[1], p[3])


def p_action_formula(p):
    '''action_formula : LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET formula_details RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE'''
    p[0] = ActionFormulaNode(p[1], p[2], p[3], p[4], p[5], p[6])



def p_formula_details(p):  
    '''formula_details : NEXT_VALUE_OF_ATTRIBUTE LESS_THAN attribute
                       | dot_access MODULUS expression equals NUMBER_LITERAL EQUIVALENCE_OPERATOR dot_access MODULUS expression equals NUMBER_LITERAL'''
    if len(p) == 4:
         p[0] = ActionFormulaDetailsNode(p[1], p[2], p[3])
    else:
         p[0] = InvariantFormulaDetailsNode(p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10], p[11])


#This function handles our liveness property statement in the TLA file
def p_liveness_property(p):
    '''liveness_property : EventuallyTerminates equals property_details'''
    p[0] = LivenessPropertyNode(p[1], p[3])



def p_property_details(p):
    '''property_details : EVENTUALLY LEFT_PAREN ENABLED attribute RIGHT_PAREN'''
    p[0] = PropertyDetailsNode(p[1], p[3], p[4])




#Function to handle our loop invariant values
def p_loop_invariant(p):
    '''loop_invariant : LoopInvariant equals action_formula'''
    p[0] = LoopInvariantNode(p[1], p[3])




#Function to handle the termination hypothesis section
def p_termination_hypothesis(p):
    '''termination_hypothesis : TerminationHypothesis equals conditional_statements'''
    p[0] = TerminationHypothesisNode(p[1], p[3])



def p_conditional_statements(p):
    '''conditional_statements : IF conditional_statement THEN conditional_statement ELSE conditional_statement'''
    p[0] = ConditionalStatementInfoNode(p[1], p[2], p[3], p[4], p[5], p[6])



def p_conditional_statement(p):
    '''conditional_statement : dot_access MODULUS NUMBER_LITERAL equals NUMBER_LITERAL
                             | EVENTUALLY LEFT_PAREN dot_access equals NUMBER_LITERAL AND dot_access equals NUMBER_LITERAL RIGHT_PAREN'''
    if len(p) == 6:
        p[0] = Conditional_IF_Node(p[1], p[2], p[3], p[4], p[5])
    elif len(p) == 11:
        p[0] = ConditionalStatementNode(p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10])






#These functions handle the Spec section of our TLA input file
        
def p_spec_definition(p):
    '''spec_definition : SPEC equals AND spec_info AND spec_info AND spec_info'''        
    p[0] = SpecDefinitionNode(p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8])



def p_spec_info(p):
    '''spec_info : LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET attribute RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE
                 | WEAK_FAIRNESS ATTRIBUTE_MAY_CHANGE LEFT_PAREN attribute RIGHT_PAREN
                 | INIT'''
    if len(p) == 7:
        p[0] = SpecInfoNode_1(p[1], p[2], p[3], p[4], p[5], p[6])
    elif len(p) == 6:
        p[0] = SpecInfoNode_2(p[1], p[2], p[3], p[4], p[5])
    else:
        p[0] = SpecInfoNode_3(p[1])




#These functions handle the Theorem section of our TLA input file
def p_theorem_definition(p):
    '''theorem_definition : THEOREM SPEC IMPLIES AND theorem_info AND theorem_info AND theorem_info AND theorem_info AND theorem_info'''
    p[0] = TheoremDefinitionNode(p[1], p[2], p[3], p[4], p[5], p[6], p[7], p[8], p[9], p[10], p[11], p[12], p[13])


def p_theorem_info(p):
    '''theorem_info : EventuallyTerminates
                    | attribute
                    | LoopInvariant
                    | TerminationHypothesis'''
    p[0] = TheoremInfoNode(p[1])




#Function to handle the grouping of expressions
def p_expression_group(p):
    'expression : LEFT_PAREN expression RIGHT_PAREN' 
    p[0] = p[2]  



# Error handling for syntax errors
def p_error(p):    #error handling code developed with help from ChatGPT 4 language model https://chat.openai.com/?model=text-davinci-002-render-sha
    if p:          #prompt: 'Error function is not working as intended, can you provide guidance on how to improve its capabilities?'
        print(f"Syntax error at token '{p.type}', value: '{p.value}', line: {p.lineno}, position: {p.lexpos}")
        #Prints the tokens leading up to the error to give error context for parsing adjustment
        context = max(0, p.lexpos - 50)  
        print(tla_code[context:p.lexpos + 10])  
    else:
        print("Syntax error at EOF")











#This section of the code is where the AST nodes are created and filled with the relevant info from the lex tokens that have been parsed by the nodes parsing rule
        
#The AST nodes generated e.g. ModuleNode, encapsulate the hierarchical structure of the source code, making it easier to traverse and analyse the code in the translator.


#each class has a __str__ function that outputs the nodes info. This is how the interconnceted AST is visualized in the command line for the user
#All of these classes have a similar structure
class ASTNode:     #AST classes 
    pass

class ModuleNode(ASTNode):                          #Code developed with guidance from PLY Lex Yacc documentation:  https://www.dabeaz.com/ply/ply.html#ply_nn4
    def __init__(self, name, extends, statements):
        #setting the relevent values to be the values saved in the node
        self.name = name
        self.extends = extends
        self.statements = statements
    
    #__str__ function that prints out the nodes info using F strings, this allows the insertions of variables into the strings makeup
    def __str__(self):
        extends_string = f", extends={self.extends}" if self.extends else ""
        statements_str = ', '.join(str(statement) for statement in self.statements)
        return f"ModuleNode(name={self.name}{extends_string}, declarations=[{statements_str}])"

    


class AttributeNode(ASTNode):
    def __init__(self, attribute_name):
        self.attribute_name = attribute_name
        
    def __str__(self):
        attribute_name_string = f", attribute name ={self.attribute_name}" if self.attribute_name else ""
        return f"AttributeNode(name={str(attribute_name_string)})"



class AttributeDotAccessNode(ASTNode):
    def __init__(self, attribute_before_dot, attribute_after_dot):
        self.attribute_before_dot = attribute_before_dot
        self.attribute_after_dot = attribute_after_dot

    def __str__(self):
        return f"AttributeDotAccessNode(attribute before dot = {str(self.attribute_before_dot)}, attribute after dot = {str(self.attribute_after_dot)}"



class ExtendsNode(ASTNode):
    def __init__(self, extended_modules):
        self.extended_modules = extended_modules


    def __str__(self):
        extended_class_string = f", extends={self.extended_modules}" if self.extended_modules else ""
        return f"ExtendsNode = (extended modules = {str(extended_class_string)}"
    


class ConstantsNode(ASTNode):
    def __init__(self, constants):
        self.constants = constants  

    def __str__(self):
        
        return f"ConstantsNode = (constants = {str(self.constants)}"

class VariablesNode(ASTNode):
    def __init__(self, variables):
        self.variables = variables  

    def __str__(self):
        return f"VariablesNode = (variables = {str(self.variables)}"
    

class AssumeNode(ASTNode):
    def __init__(self, ASSUME, attribute_1, IN_A_SET, Nat, AND, attribute_2, GREATER_OR_EQ, NUMBER_LITERAL):
       self.ASSUME = ASSUME
       self.attribute_1 = attribute_1
       self.IN_A_SET = IN_A_SET
       self.Nat =  Nat
       self.AND = AND
       self.attribute_2 = attribute_2
       self.GREATER_OR_EQ = GREATER_OR_EQ
       self.NUMBER_LITERAL = NUMBER_LITERAL
       

    def __str__(self):
        return f"AssumeNode = (Assume = {str(self.ASSUME)}, first attribute = {str(self.attribute_1)}, in a set operator = {str(self.IN_A_SET)}, naturals = {str(self.Nat)}, And = {str(self.AND)}, second attribute = {str(self.attribute_2)}, greater or equal = {str(self.GREATER_OR_EQ)}, number = {str(self.NUMBER_LITERAL)})"
       


class ComparisonNode(ASTNode):
    def __init__(self, left, operator, right):
        self.left = left
        self.operator = operator
        self.right = right


    def __str__(self):
        return f"ComparisonNode = (left side of operator = {str(self.left)}, operator = {str(self.operator)}, right side of operator = {str(self.right)})"    


class SetIndividualInfoNode(ASTNode):
    def __init__(self,attribute,scope):
       self.attribute = attribute
       self.scope = scope


    def __str__(self):
        return f"SetIndividualInfoNode = (attribute = {str(self.attribute)}, scope = {str(self.scope)})"
    
class SetScopeNode(ASTNode):
    def __init__(self,start_value,end_value):
       self.start_value = start_value
       self.end_value = end_value
    

    def __str__(self):
        return f"SetScopeNode = (start value =  {str(self.start_value)}, end value =  {str(self.end_value)})"



class SetDefinitionNode(ASTNode):
    def __init__(self, attribute, equals, set_info, ):
        self.attribute = attribute
        self.equals = equals
        self.set_info = set_info


    def __str__(self):
        set_info_str = ', '.join([str(info) for info in self.set_info])
        return f"SetDefinitionNode = (set attribute = {str(self.attribute)}, equals = {str(self.equals)}, set of records = {str(set_info_str)})"


class TypeInvariantNode(ASTNode):
    def __init__(self, name, equals_type, expression):
        self.name = name
        self.equals_type = equals_type
        self.expression = expression
       

    def __str__(self):
        return f"TypeInvariantNode = (name = {str(self.name)}, equals type = {str(self.equals_type)}, expression = {str(self.expression)})"



class TypeInvariantExpressionNode(ASTNode):
    def __init__(self, attribute1, in_a_set_value, attribute2):
        self.attribute1 = attribute1
        self.in_a_set_value = in_a_set_value
        self.attribute2 = attribute2


    def __str__(self):
        return f"TypeInvariantExpressionNode = (first attribute = {str(self.attribute1)}, in a set value = {str(self.in_a_set_value)}, second attribute = {str(self.attribute2)})"



class InitNode(ASTNode):
    def __init__(self, init, equals, attribute, IN_A_SET, init_set_statement):
        self.init = init
        self.equals = equals
        self.attribute = attribute
        self.IN_A_SET = IN_A_SET
        self.init_set = init_set_statement  # List of conditions in the initial state


    def __str__(self):
        return f"InitNode = (init = {str(self.init)}, equals = {str(self.equals)}, attribute = {str(self.attribute)}, in a set operator = {str(self.IN_A_SET)}, init set = {str(self.init_set)})"



class InitSetStatementNode(ASTNode):
    def __init__(self, attribute_1, IN_A_SET, attribute_2, COLON, order):
        self.attribute_1 = attribute_1
        self.IN_A_SET = IN_A_SET
        self.attribute_2 = attribute_2
        self.COLON = COLON
        self.order = order


    def __str__(self):
        return f"InitSetStatementNode = (first attribute = {str(self.attribute_1)}, in a set operator = {str(self.IN_A_SET)}, attribute 2 = {str(self.attribute_2)}, colon = {str(self.COLON)}, order = {str(self.order)})"


class PlusNode(ASTNode):
    def __init__(self, attribute_1_left, attribute_2_right):
        self.attribute_1_left = attribute_1_left
        self.attribute_2_right = attribute_2_right


    def __str__(self):
        return f"PlusNode = (left attribute = {str(self.attribute_1_left)}, right attribute = {str(self.attribute_2_right)})"


class SetValueNode(ASTNode):
    def __init__(self, dot_access_1, plus, dot_access_2, IN_A_SET, range_of_values):
        self.dot_access_1 = dot_access_1
        self.plus = plus
        self.dot_access_2 = dot_access_2
        self.IN_A_SET = IN_A_SET
        self.range_of_values = range_of_values

        
    def __str__(self):
        return f"SetValueNode = (first dot variable = {str(self.dot_access_1)}, plus = {str(self.plus)}, second dot variable = {str(self.dot_access_2)}, in a set operator = {str(self.IN_A_SET)}, range of values = {str(self.range_of_values)})"


class AdditionResultNode(ASTNode):
    def __init__(self, left_value, right_value):
        self.left_value = left_value
        self.right_value = right_value



    def __str__(self):
        return f"AdditionResultNoe = (left value = {str(self.left_value)}, right value = {str(self.right_value)})"



class InitSetRangeOfValuesNode(ASTNode):
    def __init__(self, start_of_range, end_of_range):
        self.start_of_range = start_of_range
        self.end_of_range = end_of_range



    def __str__(self):
        return f"InitSetRangeOfValuesNode = (start of range = {str(self.start_of_range)}, end of range = {str(self.end_of_range)})"


class BeanValueCountNode(ASTNode):
    def __init__(self, attribute, bean_equation):
        self.attribute = attribute
        self.bean_equation = bean_equation


    def __str__(self):
        return f"BeanValueCountNode = (attribute = {str(self.attribute)}, bean equation = {str(self.bean_equation)})"



class FunctionDeclarationNode_1(ASTNode):
    def __init__(self, attribute, equals, AND, function_conditions, AND_1, function_conditions_1, except_section):
        self.attribute = attribute
        self.equals = equals
        self.AND = AND
        self.function_conditions = function_conditions 
        self.AND_1 = AND_1
        self.function_conditions_1 = function_conditions_1 
        self.except_section = except_section


    def __str__(self):
        return f"FunctionDeclarationNode_1 = (attribute = {str(self.attribute)}, equals = {str(self.equals)},  and = {str(self.AND)}, conditions = {str(self.function_conditions)}, and = {str(self.AND_1)}, conditions = {str(self.function_conditions_1)},  except section = {str(self.except_section)})"



class FunctionDeclarationNode_2(ASTNode):
    def __init__(self, attribute, equals, AND, function_conditions, AND_1, function_conditions_1, AND_2, function_conditions_2, except_section):
        self.attribute = attribute
        self.equals = equals
        self.AND = AND
        self.function_conditions = function_conditions 
        self.AND_1 = AND_1
        self.function_conditions_1 = function_conditions_1 
        self.AND_2 = AND_2
        self.function_conditions_2 = function_conditions_2
        self.except_section = except_section


    def __str__(self):
        return f"FunctionDeclarationNode_2 = (attribute = {str(self.attribute)}, equals = {str(self.equals)},  and = {str(self.AND)}, conditions = {str(self.function_conditions)}, and = {str(self.AND_1)}, conditions = {str(self.function_conditions_1)}, and = {str(self.AND_2)}, conditions = {str(self.function_conditions_2)} except section = {str(self.except_section)})"




class FunctionInfoNode(ASTNode):
    def __init__(self, attribute_1, dot, attribute_2, comparison_rule, number):
        self.attribute_1 = attribute_1
        self.dot = dot
        self.attribute_2 = attribute_2
        self.comparison_rule = comparison_rule
        self.number = number


    def __str__(self):
        return f"FunctionInfoNode = (attribute_1 = {str(self.attribute_1)}, dot = {str(self.dot)}, attribute_2 = {str(self.attribute_2)}, comparison rule = {str(self.comparison_rule)}, number = {str(self.number)})"   
        


class FunctionConditionNoDotNode(ASTNode):
    def __init__(self, attribute, comparison_rule, number):
        self.attribute = attribute
        self.comparison_rule = comparison_rule
        self.number = number


    def __str__(self):
        return f"FunctionConditionNoDotNode = (attribute = {str(self.attribute)}, comparison rule = {str(self.comparison_rule)}, number = {str(self.number)})"


class FunctionUNCHANGEDNode(ASTNode):
    def __init__(self, unchanged, attribute):
        self.unchanged = unchanged
        self.attribute = attribute
        

    def __str__(self):
        return f"FunctionUNCHANGEDNode = (unchanged = {str(self.unchanged)}, attribute = {str(self.attribute)})"


class FunctionNameNode(ASTNode):
    def __init__(self, name):
        self.name = name
        

    def __str__(self):
        return f"FunctionNameNode = (name = {str(self.name)})"

class FunctionConditionDotNode(ASTNode):
    def __init__(self, attribute_before_dot, dot, attribute_after_dot, comparison_rule, number):
        self.attribute_before_dot = attribute_before_dot
        self.dot = dot
        self.attribute_after_dot = attribute_after_dot
        self.comparison_rule = comparison_rule
        self.number = number



    def __str__(self):
        return f"FunctionConditionDotNode = (attribute before dot = {str(self.attribute_before_dot)}, dot = {str(self.dot)}, attribute after dot = {str(self.attribute_after_dot)}, comparison rule = {str(self.comparison_rule)}, number = {str(self.number)})"



class ExceptSectionNode(ASTNode):
    def __init__(self, AND, next_value_attribute, equals, except_node):
        self.AND = AND
        self.next_value_attribute = next_value_attribute
        self.equals = equals
        self.except_node = except_node



    def __str__(self):
        return f"ExceptSectionNode = (And = {str(self.AND)}, next value attribute = {str(self.next_value_attribute)}, equals = {str(self.equals)}, except node = {str(self.except_node)})"


class ExceptClauseNode(ASTNode):
    def __init__(self, attribute_1, exclamation_mark, dot, attribute_2, at, operator, number):
        self.attribute_1 = attribute_1
        self.exclamation_mark = exclamation_mark                                                             
        self.dot = dot
        self.attribute_2 = attribute_2
        self.at = at
        self.operator = operator
        self.number = number



    def __str__(self):
        return f"ExceptClauseNode = (first attribute = {str(self.attribute_1)}, exclamation mark = {str(self.exclamation_mark)}, dot = {str(self.dot)}, second attribute = {str(self.attribute_2)}, at = {str(self.at)},)"


class MultipleExceptClauseNode(ASTNode):
    def __init__(self, attribute_1, exclamation_mark_1, dot_1, attribute_2, at_1, operator_1, number_1, exclamation_mark_2, dot_2, attribute_3, at_2, operator_2, number_2):
        self.attribute_1 = attribute_1
        self.exclamation_mark_1 = exclamation_mark_1
        self.dot_1 = dot_1
        self.attribute_2 = attribute_2
        self.at_1= at_1
        self.operator_1 = operator_1
        self.number_1 = number_1
        self.exclamation_mark_2 = exclamation_mark_2
        self.dot_2 = dot_2
        self.attribute_3 = attribute_3
        self.at_2 = at_2
        self.operator_2 = operator_2
        self.number_2 = number_2




    def __str__(self):
        return f"MultipleExceptClauseNode = (first attribute = {str(self.attribute_1)}, first exclamation mark = {str(self.exclamation_mark_1)}, first dot = {str(self.dot_1)}, second attribute = {str(self.attribute_2)}, first AT = {str(self.at_1)}, first operator = {str(self.operator_1)}, first number = {str(self.number_1)}, second exclamation mark = {str(self.exclamation_mark_2)}, second dot = {str(self.dot_2)}, third attribute = {str(self.attribute_3)} second AT = {str(self.at_2)} second operator = {str(self.operator_2)} second number = {str(self.number_2)})"



class TerminationStatementNode(ASTNode):
    def __init__(self, attribute, equals, AND_1, termination_info_1, AND_2, termination_info_2):
        self.attribute = attribute
        self.equals = equals
        self.AND_1 = AND_1
        self.termination_info_1 = termination_info_1
        self.AND_2 = AND_2
        self.termination_info_2 = termination_info_2
        

    def __str__(self):
        return f"TerminationStatementNode = (attribute = {str(self.attribute)}, equals = {str(self.equals)}, AND = {str(self.AND_1)}, termination case 1 = {str(self.termination_info_1)}, and = {str(self.AND_2)}, termination case 2 {str(self.termination_info_2)})"
        

class TerminationInfoNode_1(ASTNode):
    def __init__(self, attribute, equals, NUMBER_LITERAL):
       self.attribute = attribute
       self.equals = equals
       self.NUMBER_LITERAL = NUMBER_LITERAL
       
    def __str__(self):
        return f"TerminationInfoNode_1 = (attribute = {str(self.attribute)}, equals = {str(self.equals)}, number = {str(self.NUMBER_LITERAL)})"




class TerminationInfoNode_2(ASTNode):
    def __init__(self, UNCHANGED, attribute):
        self.UNCHANGED = UNCHANGED
        self.attribute = attribute

    def __str__(self):
        return f"TerminationInfoNode_2 = (Unchanged = {str(self.UNCHANGED)}, attribute = {str(self.attribute)})"
   
        
                  


class NextStateRelationNode(ASTNode):
    def __init__(self, attribute, equals, OR_1, next_state_info_1, OR_2, next_state_info_2, OR_3, next_state_info_3, OR_4, next_state_info_4):
        self.attribute = attribute
        self.equals = equals
        self.OR_1 = OR_1
        self.next_state_info_1 = next_state_info_1
        self.OR_2 = OR_2
        self.next_state_info_2 = next_state_info_2
        self.OR_3 = OR_3
        self.next_state_info_3 = next_state_info_3
        self.OR_4 = OR_4
        self.next_state_info_4 = next_state_info_4
        


    def __str__(self):
        return f"NextStateRelationNode = (attribute = {str(self.attribute)}, equals = {str(self.equals)}, or = {str(self.OR_1)}, next state info = {str(self.next_state_info_1)}, or = {str(self.OR_2)}, next state info = {str(self.next_state_info_2)}, or = {str(self.OR_3)}, next state info = {str(self.next_state_info_3)}, or = {str(self.OR_4)}, next state info = {str(self.next_state_info_4)})"
        


class NextStateNode(ASTNode):
    def __init__(self, attribute):
        self.attribute = attribute


    def __str__(self):
        return f"NextStateInfoNode = (attribute = {str(self.attribute)})"   
        




class FormulaDefinitionNode(ASTNode):
    def __init__(self, attribute, action_formula):
        self.attribute = attribute
        self.action_formula = action_formula
        


    def __str__(self):
        return f"FormulaDefinitionNode = (attribute = {str(self.attribute)}, action formula = {str(self.action_formula)})"    

class ActionFormulaNode(ASTNode):
    def __init__(self, LEFT_SQR_BRACKET_1, RIGHT_SQR_BRACKET_1, LEFT_SQR_BRACKET_2, formula_details, RIGHT_SQR_BRACKET_2, ATTRIBUTE_MAY_CHANGE):
        self.LEFT_SQR_BRACKET_1 = LEFT_SQR_BRACKET_1
        self.RIGHT_SQR_BRACKET_1 = RIGHT_SQR_BRACKET_1
        self.LEFT_SQR_BRACKET_2 = LEFT_SQR_BRACKET_2
        self.formula_details = formula_details
        self.RIGHT_SQR_BRACKET_2 = RIGHT_SQR_BRACKET_2
        self.ATTRIBUTE_MAY_CHANGE = ATTRIBUTE_MAY_CHANGE



    def __str__(self):
        return f"ActionFormulaNode(left square bracket 1 = {str(self.LEFT_SQR_BRACKET_1)}, right square bracket 1 = {str(self.RIGHT_SQR_BRACKET_1)}, left square bracket 2 {str(self.LEFT_SQR_BRACKET_2)}, formula details = {str(self.formula_details)}, right square bracket 2 = {str(self.RIGHT_SQR_BRACKET_2)}, attribute may change = {str(self.ATTRIBUTE_MAY_CHANGE)})"


class ActionFormulaDetailsNode(ASTNode):
    def __init__(self, NEXT_VALUE_OF_ATTRIBUTE, LESS_THAN, attribute):
        self.NEXT_VALUE_OF_ATTRIBUTE = NEXT_VALUE_OF_ATTRIBUTE
        self.LESS_THAN = LESS_THAN
        self.attribute = attribute



    def __str__(self):
        return f"ActionFormulaDetailsNode = (next value of attribute = {str(self.NEXT_VALUE_OF_ATTRIBUTE)}, less than = {str(self.LESS_THAN)}, attribute = {str(self.attribute)})"




class LivenessPropertyNode(ASTNode):
    def __init__(self, attribute, hypothesis_details):
        self.attribute = attribute
        self.hypothesis_details = hypothesis_details



    def __str__(self):
        return f"LivenessPropertyNode = (attribute = {str(self.attribute)}, hypothesis details = {str(self.hypothesis_details)})"   



class PropertyDetailsNode(ASTNode):
    def __init__(self, eventually, enabled, attribute):
        self.eventually = eventually
        self.enabled = enabled
        self.attribute = attribute
        


    def __str__(self):
        return f"PropertyDetailsNode = (eventually = {str(self.eventually)}, enabled = {str(self.enabled)}, attribute = {str(self.attribute)})"



class LoopInvariantNode(ASTNode):
    def __init__(self, attribute, invariant_details):
        self.attribute = attribute
        self.invariant_details = invariant_details



    def __str__(self):
        return f"LoopInvarantNode = (attribute = {str(self.attribute)}, invariant details = {str(self.invariant_details)})"


class InvariantFormulaDetailsNode(ASTNode):
    def __init__(self, dot_access_1, MODULUS_1, expression_1, equals_1, NUMBER_LITERAL_1, EQUIVALENCE_OPERATOR, dot_access_2, MODULUS_2, expression_2, equals_2, NUMBER_LITERAL_2):
        self.dot_access_1 = dot_access_1
        self.MODULUS_1 = MODULUS_1
        self.expression_1 = expression_1
        self.equals_1 = equals_1
        self.NUMBER_LITERAL_1 = NUMBER_LITERAL_1
        self.EQUIVALENCE_OPERATOR = EQUIVALENCE_OPERATOR
        self.dot_access_2 = dot_access_2
        self.MODULUS_2 = MODULUS_2
        self.expression_2 = expression_2
        self.equals_2 = equals_2
        self.NUMBER_LITERAL_2 = NUMBER_LITERAL_2



    def __str__(self):
        return f"InvariantFormulaDetailsNode = (first dot access = {str(self.dot_access_1)}, first modulus = {str(self.MODULUS_1)}, first expression = {str(self.expression_1)}, first equals = {str(self.equals_1)}, first number literal = {str(self.NUMBER_LITERAL_1)}, equivalece operator = {str(self.EQUIVALENCE_OPERATOR)}, second dot access = {str(self.dot_access_2)}, second modulus = {str(self.MODULUS_2)}, second expression = {str(self.expression_2)}, second equals = {str(self.equals_2)}, second number literal = {str(self.NUMBER_LITERAL_2)})"




class TerminationHypothesisNode(ASTNode):
    def __init__(self, operator, statement):
        self.operator = operator
        self.statement = statement



    def __str__(self):
        return f"TerminationHypothesisNode = (operator = {str(self.operator)}, statement = {str(self.statement)})"




class ConditionalStatementInfoNode(ASTNode):    #the condtional statement operator information
    def __init__(self, IF, conditional_statement_if, THEN, conditional_statement_then, ELSE, conditional_statement_else):
        self.IF = IF
        self.conditional_statement_if = conditional_statement_if
        self.THEN = THEN
        self.conditional_statement_then = conditional_statement_then
        self.ELSE = ELSE
        self.conditional_statement_else = conditional_statement_else
       
        


    def __str__(self):
        return f"ConditionalStatementInfoNode = (If = {str(self.IF)}, if conditional statement = {str(self.conditional_statement_if)}, then = {str(self.THEN)}, then conditional statement = {str(self.conditional_statement_then)}, else = {str(self.ELSE)}, else conditional statement = {str(self.conditional_statement_else)})"



class Conditional_IF_Node(ASTNode):
    def __init__(self, dot_access, MODULUS, NUMBER_LITERAL_1, equals, NUMBER_LITERAL_2):
        self.dot_access = dot_access
        self.MODULUS = MODULUS
        self.NUMBER_LITERAL_1 = NUMBER_LITERAL_1
        self.equals = equals
        self.NUMBER_LITERAL_2 = NUMBER_LITERAL_2



    def __str__(self):
        return f"Conditional_IF_Node = (dot access = {str(self.dot_access)}, modulus = {str(self.MODULUS)}, first number literal = {str(self.NUMBER_LITERAL_1)}, equals = {str(self.equals)}, second number literal = {str(self.NUMBER_LITERAL_2)})"

        

class ConditionalStatementNode(ASTNode):     #the context of the conditional operator
    def __init__(self, EVENTUALLY, LEFT_PAREN, dot_access_1, equals_1, NUMBER_LITERAL_1, AND, dot_access, equals, NUMBER_LITERAL, RIGHT_PAREN):
        self.EVENTUALLY = EVENTUALLY
        self.LEFT_PAREN = LEFT_PAREN
        self.dot_access_1 = dot_access_1
        self.equals_1 = equals_1
        self.NUMBER_LITERAL_1 = NUMBER_LITERAL_1
        self.AND = AND
        self.dot_access = dot_access
        self.equals = equals
        self.NUMBER_LITERAL = NUMBER_LITERAL
        self.RIGHT_PAREN = RIGHT_PAREN



    def __str__(self):
        return f"ConditionalStatementNode = (eventually = {str(self.EVENTUALLY)}, left parenthesis = {str(self.LEFT_PAREN)}, first dot access = {str(self.dot_access_1)}, first equals = {str(self.equals_1)}, first number literal = {str(self.NUMBER_LITERAL_1)}, and = {str(self.AND)}, second dot access = {str(self.dot_access)}, second equals = {str(self.equals)}, second number literal = {str(self.NUMBER_LITERAL)}, right parenthesis = {str(self.RIGHT_PAREN)})"


class SpecDefinitionNode(ASTNode):
    def __init__(self, SPEC, equals, AND_1, spec_info_1, AND_2, spec_info_2, AND_3, spec_info_3):
        self.SPEC = SPEC
        self.equals = equals
        self.AND_1 = AND_1
        self.spec_info_1 = spec_info_1
        self.AND_2 = AND_2
        self.spec_info_2 = spec_info_2
        self.AND_3 = AND_3
        self.spec_info_3 = spec_info_3


    def __str__(self):
        return f"SpecDefinitionNode = (spec = {str(self.SPEC)}, equals = {str(self.equals)}, and = {str(self.AND_1)}, spec info = {str(self.spec_info_1)}, and = {str(self.AND_2)}, spec info = {str(self.spec_info_2)}, and = {str(self.AND_3)}, spec info = {str(self.spec_info_3)})"



class SpecInfoNode_1(ASTNode):
    def __init__(self, LEFT_SQR_BRACKET_1, RIGHT_SQR_BRACKET_1, LEFT_SQR_BRACKET_2, attribute, RIGHT_SQR_BRACKET_2, ATTRIBUTE_MAY_CHANGE):
        self.LEFT_SQR_BRACKET_1 = LEFT_SQR_BRACKET_1
        self.RIGHT_SQR_BRACKET_1 = RIGHT_SQR_BRACKET_1
        self. LEFT_SQR_BRACKET_2 =  LEFT_SQR_BRACKET_2
        self.attribute = attribute
        self.RIGHT_SQR_BRACKET_2 = RIGHT_SQR_BRACKET_2
        self.ATTRIBUTE_MAY_CHANGE = ATTRIBUTE_MAY_CHANGE


    def __str__(self):
        return f"SpecInfoNode_1 = (left sqr bracket = {str(self.LEFT_SQR_BRACKET_1)}, right sqr bracket = {str(self.RIGHT_SQR_BRACKET_1)}, left sqr bracket = {str(self.LEFT_SQR_BRACKET_2)}, attribute = {str(self.attribute)}, right sqr bracket = {str(self.RIGHT_SQR_BRACKET_2)}, attribute may change = {str(self.ATTRIBUTE_MAY_CHANGE)})"  



class SpecInfoNode_2(ASTNode):
    def __init__(self, WEAK_FAIRNESS, ATTRIBUTE_MAY_CHANGE, LEFT_PAREN, attribute, RIGHT_PAREN):
        self.WEAK_FAIRNESS = WEAK_FAIRNESS
        self.ATTRIBUTE_MAY_CHANGE = ATTRIBUTE_MAY_CHANGE
        self.LEFT_PAREN = LEFT_PAREN
        self.attribute = attribute
        self.RIGHT_PAREN = RIGHT_PAREN



    def __str__(self):
        return f"SpecInfoNode_2 = (weak fairness = {str(self.WEAK_FAIRNESS)}, attribute may chnage = {str(self.ATTRIBUTE_MAY_CHANGE)}, left paren = {str(self.LEFT_PAREN)}, attribute = {str(self.attribute)}, right paren = {str(self.RIGHT_PAREN)})"



class SpecInfoNode_3(ASTNode):
    def __init__(self, init):
        self.init = init

    def __str__(self):
        return f"SpecInfoNode_3 = (attribute = {str(self.init)})"   
        



class TheoremDefinitionNode(ASTNode):
    def __init__(self, THEOREM, SPEC, IMPLIES, AND_1, theorem_info_1, AND_2, theorem_info_2, AND_3, theorem_info_3, AND_4, theorem_info_4, AND_5, theorem_info_5):
        self.THEOREM = THEOREM
        self.SPEC = SPEC
        self.IMPLIES = IMPLIES
        self.AND_1 = AND_1
        self.theorem_info_1 = theorem_info_1
        self.AND_2 = AND_2
        self.theorem_info_2 = theorem_info_2
        self.AND_3 = AND_3
        self.theorem_info_3 = theorem_info_3
        self.AND_4 = AND_4
        self.theorem_info_4 = theorem_info_4
        self.AND_5 = AND_5
        self.theorem_info_5 = theorem_info_5



    def __str__(self):
        return f"TheoremDefinitionNode = (theorem = {str(self.THEOREM)}, spec = {str(self.SPEC)}, implies = {str(self.IMPLIES)}, and = {str(self.AND_1)}, theorem info = {str(self.theorem_info_1)}, and = {str(self.AND_2)}, theorem info = {str(self.theorem_info_2)}, and = {str(self.AND_3)}, theorem info = {str(self.theorem_info_3)}, and = {str(self.AND_4)}, theorem info = {str(self.theorem_info_4)}, and = {str(self.AND_5)}, theorem info = {str(self.theorem_info_5)})"



class TheoremInfoNode(ASTNode):
    def __init__(self, name):
        self.name = name

    def __str__(self):
        return f"TheoremInfoNode = (name = {str(self.name)})"



class NumberNode(ASTNode):
    def __init__(self, value):
        self.value = value
    
    def __str__(self):
        return f"NumberNode = (value = {str(self.value)})"



# This builds the PLY Yacc parser
parser = yacc.yacc(debug=True)

#we LR parse the inputted code into the parser, which is saved in result
result = parser.parse(tla_code)

