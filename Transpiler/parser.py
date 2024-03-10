import ply.yacc as yacc
from tokenizer import tokens
from tokenizer import tla_code



# Placeholder for storing parsed module information
parsed_data = {}

#This precedence table determines the precedence of operators in the parser, this will contain the number of shift/reduce conflicts 
precedence = (
    #('left', 'OR'),  # Logical OR
    ('left', 'EQUIVALENCE_OPERATOR'),
    ('left', 'AND'),  # Logical AND
    ('nonassoc', 'EQUALS_DEFINITIONS', 'NOT_EQUALS'),  # Equality and inequality
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
        p[0] = ModuleNode(name=p[3], extends=p[5], statements=p[6])
    else:
        p[0] = ModuleNode(name=p[3], extends=None, statements=p[5])


def p_attribute(p):
    '''attribute : ATTRIBUTE'''
    p[0] = p[1]  


def p_dot_access(p):
    '''dot_access : attribute DOT attribute
                  | NEXT_VALUE_OF_ATTRIBUTE DOT attribute'''
    p[0] = AttributeDotAccessNode(p[1], p[3])

def p_extends(p):
    '''extends : EXTENDS names'''
    p[0] = p[1]     

    

def p_names(p):
    '''names : names COMMA attribute
             | attribute'''
    if len(p) == 4:
        p[0] = p[1] + [p[3]]                                    #if-else statement used to handle multiple names seperated by a comma
         
    else:
        p[0] = [p[1]]
       
        

#This section deals with the parsing of various statements, this includes keywords, variables, constants etc

def p_statements(p):
    '''statements : statements statement
                    | statement'''
    if len(p) == 3:
        p[1].append(p[2])
        p[0] = p[1]
    else:
        p[0] = [p[1]]


   
# Define rules for `variable_statement`, `constants_statement`, etc.


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


def p_constants_statement(p):
    '''constants_statement : CONSTANTS names'''
    p[0] = ConstantsNode(constants=p[2])


def p_variables_statement(p):
    '''variables_statement : VARIABLES names'''
    p[0] = VariablesNode(variables=p[2])


def p_assume_statement(p):
    '''assume_statement : ASSUME expression AND expression'''
    p[0] = AssumeNode(p[2], p[4])



def p_expression(p):                                      #this section of code was made with help from ChatGPT language model
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
    
    if len(p) == 4:
        # Handles binary operations
        p[0] = BinaryOperationNode(p[1], p[2], p[3])
    elif p.slice[1].type == "ATTRIBUTE":
        # Handles identifiers
        p[0] = IdentifierNode(p[1])
    else:
        # Handles literals (numbers and strings)
        p[0] = NumberNode(p[1])


def p_type_invariant_expression(p):
    '''type_invariant_expression : attribute IN_A_SET attribute'''
    p[0] = TypeInvariantExpressionNode(p[1], p[2], p[3])

def p_init_expression(p):
    '''init_expression : '''

def p_comparison(p):
    '''comparison : attribute comparison_rule NUMBER_LITERAL
                  | attribute comparison_rule attribute'''
    p[0] = ComparisonNode(p[1], p[2], p[3])
    
def p_comparison_rule(p):
    '''comparison_rule :   GREATER_OR_EQ
                    | LESS_OR_EQ
                    | GREATER_THAN                         
                    | LESS_THAN '''
    p[0] = p[1]
    
def p_set_membership(p):
    '''set_membership : attribute IN_A_SET Nat '''
    p[0] = p[1]

def p_equals(p):
    '''equals : EQUALS_DEFINITIONS
              | EQUALS_EQUALITY'''
    p[0] = p[1]

def p_set_definition(p):
    '''set_definition : attribute equals LEFT_SQR_BRACKET set_info RIGHT_SQR_BRACKET'''
    p[0] = SetDefinitionNode(p[1], p[3])




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
    p[0] = InitNode(p[1], p[5])


def p_init_set_statement(p):
    '''init_set_statement : LEFT_BRACE attribute IN_A_SET attribute COLON order'''
    p[0] = InitSetStatementNode(p[2], p[4], p[6])


def p_order(p):
    '''order : dot_access PLUS dot_access IN_A_SET range_of_values'''
    addition_result = PlusNode(p[1], p[3])
    p[0] = SetValueNode(addition_result, p[5])


def p_range_of_values(p):
    '''range_of_values :  NUMBER_LITERAL DOT DOT attribute RIGHT_BRACE'''
    p[0] = InitSetRangeOfValuesNode(p[1], p[4])



def p_bean_value_count(p):
    '''bean_value_count : attribute equals bean_equation'''
    p[0] = BeanValueCountNode(p[1], p[3])



def p_bean_equation(p):
    '''bean_equation : dot_access PLUS dot_access'''          #This node represents the equation of two c.black + c.white values  
    p[0] = AdditionResultNode(p[1], p[3])









#Rule handling all of our funcions in TLA, for example for this: picking two black beans, removing them, then replacing with one black bean
def p_function_declaration(p):
    '''function_declaration : attribute equals AND function_conditions except_section'''
    p[0] = FunctionDeclarationNode(p[1], p[3], p[4], p[5])


def p_function_conditions(p):
    '''function_conditions : function_condition
                           | function_conditions AND function_condition
                           | function_conditions OR function_condition'''
    if len(p) == 2:
        p[0] = [p[1]]
    else:
        p[0] = p[1] + [p[3]]
        


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

    
def p_except_section(p):     #This handles our transition function
    '''except_section : AND NEXT_VALUE_OF_ATTRIBUTE equals except_clause'''
    p[0] = ExceptSectionNode(p[2], p[3], p[4])


def p_except_clause(p):      #This handles our except clause section
    '''except_clause : LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET
                     | LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT PLUS NUMBER_LITERAL COMMA EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET'''
    if len(p) == 12:
        p[0] = ExceptClauseNode(p[2], p[4], p[5], p[6], p[8], p[9], p[10])
    else:
        p[0] = MultipleExceptClauseNode(p[2], p[4], p[5], p[6], p[8], p[9], p[10], p[12], p[13], p[14], p[16], p[17], p[18])    

    

def p_termination_statement(p):
    '''termination_statement : attribute equals AND function_conditions'''
    p[0] = TerminationStatementNode(p[1], p[3], p[4])




def p_next_state_relation(p):
    '''next_state_relation : attribute equals OR function_conditions'''
    p[0] = NextStateRelationNode(p[1], p[3], p[4])



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



def p_liveness_property(p):
    '''liveness_property : EventuallyTerminates equals property_details'''
    p[0] = LivenessPropertyNode(p[1], p[3])



def p_property_details(p):
    '''property_details : EVENTUALLY LEFT_PAREN ENABLED attribute RIGHT_PAREN'''
    p[0] = PropertyDetailsNode(p[1], p[3], p[4])



#CURRENT WORKING SECTION~~~~~~~~~~~~~~~~~~~~~~

def p_loop_invariant(p):
    '''loop_invariant : LoopInvariant equals action_formula'''
    p[0] = LoopInvariantNode(p[1], p[3])






#termination hypothesis section
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






#Spec section
        
def p_spec_definition(p):
    '''spec_definition : SPEC equals AND function_conditions'''        
    p[0] = SpecDefinitionNode(p[1], p[2], p[3], p[4])




def p_theorem_definition(p):
    '''theorem_definition : THEOREM SPEC IMPLIES AND function_conditions'''
    p[0] = TheoremDefinitionNode(p[1], p[2], p[3], p[4], p[5])







#Grouping expressions
def p_expression_group(p):
    'expression : LEFT_PAREN expression RIGHT_PAREN' 
    p[0] = p[2]  # Grouped expression, no node needed


def p_empty(p):
    'empty :'
    pass

# Error handling for syntax errors
def p_error(p):
    if p:
        print(f"Syntax error at token '{p.type}', value: '{p.value}', line: {p.lineno}, position: {p.lexpos}")
        # Optionally, print a few tokens leading up to the error for context
        context = max(0, p.lexpos - 50)  # Adjust as needed for context size
        print("Error context:")
        print(tla_code[context:p.lexpos + 10])  # Adjust slicing as needed
    else:
        print("Syntax error at EOF")




#THESE ARE OUR NODES FOR THE ABSTRACT SYNTAX TREE
class ASTNode:     #AST classes 
    pass

class ModuleNode(ASTNode):
    def __init__(self, name, extends, statements):
        self.name = name
        self.extends = extends
        self.statements = statements

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
        self.constants = constants  # List of constant names

    def __str__(self):
        constants_string = f", constants={self.constants}" if self.constants else ""
        return f"ConstantsNode = (constants = {str(constants_string)}"

class VariablesNode(ASTNode):
    def __init__(self, variables):
        self.variables = variables  # List of variable names

    def __str__(self):
        variables_string = f", constants={self.variables}" if self.variables else ""
        return f"VariablesNode = (variables = {str(variables_string)}"
    

class AssumeNode(ASTNode):
    def __init__(self, expression_1, expression_2):
       self.expression_1 = expression_1
       self.expression_2 = expression_2

    def __str__(self):
        return f"AssumeNode = (first expression = {str(self.expression_1)}, second expression = {str(self.expression_2)})"
       


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
        return f"SetScopeNode = (start value = {str(self.start_value)}, end value + {str(self.end_value)})"



class SetDefinitionNode(ASTNode):
    def __init__(self, set_attribute, set_of_records):
        self.set_attribute = set_attribute
        self.set_of_records = set_of_records   


    def __str__(self):
        return f"SetDefinitionNode = (set attribute = {str(self.set_attribute)}, set of records = {str(self.set_of_records)})"


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
    def __init__(self, init, init_set):
        self.init = init
        self.init_set = init_set  # List of conditions in the initial state


    def __str__(self):
        return f"InitNode = (init = {str(self.init)}, init set = {str(self.init_set)})"



class InitSetStatementNode(ASTNode):
    def __init__(self, attribute1, attribute2, order):
        self.attribute1 = attribute1
        self.attribute2 = attribute2
        self.order = order


    def __str__(self):
        return f"InitSetStatementNode = (first attribute = {str(self.attribute1)}, attribute 2 = {str(self.attribute2)}, order = {str(self.order)})"


class PlusNode(ASTNode):
    def __init__(self, attribute_1_left, attribute_2_right):
        self.attribute_1_left = attribute_1_left
        self.attribute_2_right = attribute_2_right


    def __str__(self):
        return f"PlusNode = (left attribute = {str(self.attribute_1_left)}, right attribute = {str(self.attribute_2_right)})"


class SetValueNode(ASTNode):
    def __init__(self, addition_result, range_of_values):
        self.addition_result = addition_result
        self.range_of_values = range_of_values

        
    def __str__(self):
        return f"SetValueNode = (addition result = {str(self.addition_result)}, range of values = {str(self.range_of_values)})"


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



class FunctionDeclarationNode(ASTNode):
    def __init__(self, attribute, AND, conditions, except_section):
        self.attribute = attribute
        self.AND = AND
        self.conditions = conditions 
        self.except_section = except_section


    def __str__(self):
        conditions_str = ',\n    '.join(str(condition) for condition in self.conditions)
        return f"FunctionDeclarationNode = (attribute = {str(self.attribute)}, and ={str(self.AND)}, conditions = [\n{conditions_str}\n], except section = {str(self.except_section)})"


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
    def __init__(self, next_value_attribute, equals, except_node):
        self.next_value_attribute = next_value_attribute
        self.equals = equals
        self.except_node = except_node



    def __str__(self):
        return f"ExceptSectionNode = (next value attribute = {str(self.next_value_attribute)}, equals = {str(self.equals)}, except node = {str(self.except_node)})"


class ExceptClauseNode(ASTNode):
    def __init__(self, attribute_1, exclamation_mark, dot, attribute_2, at, operator, number):
        self.attribute_1 = attribute_1
        self.exclamation_mark = exclamation_mark                                                              #implement dot_access here
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
    def __init__(self, attribute, AND, conditions):
        self.attribute = attribute
        self.AND = AND
        self.conditions = conditions
        

    def __str__(self):
        return f"TerminationStatementNode = (attribute = {str(self.attribute)}, AND = {str(self.AND)}, conditions = {str(self.conditions)})"
        


class NextStateRelationNode(ASTNode):
    def __init__(self, next_declaration, OR, conditions):
        self.next_declaration = next_declaration
        self.OR = OR
        self.conditions  = conditions
        


    def __str__(self):
        return f"NextStateRelationNode = (next declaration = {str(self.next_declaration)}, OR = {str(self.OR)}, conditions = {str(self.conditions)})"


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
    def __init__(self, SPEC, equals, AND, function_conditions):
        self.SPEC = SPEC
        self.equals = equals
        self.AND = AND
        self.function_conditions = function_conditions



    def __str__(self):
        return f"SpecDefinitionNode = (spec = {str(self.SPEC)}, equals = {str(self.equals)}, and = {str(self.AND)}, function conditions = {str(self.function_conditions)})"



class TheoremDefinitionNode(ASTNode):
    def __init__(self, THEOREM, SPEC, IMPLIES, AND, function_conditions):
        self.THEOREM = THEOREM
        self.SPEC = SPEC
        self.IMPLIES = IMPLIES
        self.AND = AND
        self.function_conditions = function_conditions



    def __str__(self):
        return f"TheoremDefinitionNode = (theorem = {str(self.THEOREM)}, spec = {str(self.SPEC)}, implies = {str(self.IMPLIES)}, and = {str(self.AND)}, function conditions = {str(self.function_conditions)})"











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

class NumberNode(ASTNode):
    def __init__(self, value):
        self.value = value
    
    def __str__(self):
        return f"NumberNode = (value = {str(self.value)})"



















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
parser = yacc.yacc(debug=True)


result = parser.parse(tla_code)
print(result)
print(parsed_data)

#module_node = ModuleNode("CoffeeCan", None, ["Variable can", "Constant MaxBeanCount"])
print(ModuleNode)
