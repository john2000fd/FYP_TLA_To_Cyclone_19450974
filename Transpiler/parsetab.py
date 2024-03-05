
# parsetab.py
# This file is automatically generated. Do not edit.
# pylint: disable=W,C,R
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = 'leftANDnonassocEQUALS_DEFINITIONSNOT_EQUALSnonassocLESS_THANLESS_OR_EQGREATER_THANGREATER_OR_EQleftPLUSMINUSleftSTARDIVIDEMODULUSnonassocLEFT_PARENRIGHT_PARENAND ARROW ASSUME AT ATTRIBUTE ATTRIBUTE_MAY_CHANGE BACK_SLASH CHECK COLON COMMA CONSTANTS DIVIDE DOT EDGE ELSE EQUALS_DEFINITIONS EQUALS_EQUALITY EXCEPT EXCLAMATION_MARK EXTENDS FORWARD_SLASH GOAL GRAPH GREATER_OR_EQ GREATER_THAN IF INIT INVARIANT IN_A_SET LEFT_BRACE LEFT_PAREN LEFT_SQR_BRACKET LESS_OR_EQ LESS_THAN MINUS MODULE MODULE_WRAPPER MODULUS NEXT_VALUE_OF_ATTRIBUTE NODE NOT_EQUALS NUMBER_LITERAL Nat OR PLUS RIGHT_BRACE RIGHT_PAREN RIGHT_SQR_BRACKET SEMICOLON SINGLE_QUOTE SPEC STAR STRING_LITERAL THEN UNCHANGED UNDERSCORE VARIABLES VARIABLE_NAMEmodule : MODULE_WRAPPER MODULE attribute MODULE_WRAPPER extends statements\n              | MODULE_WRAPPER MODULE attribute MODULE_WRAPPER statementsattribute : ATTRIBUTEdot_access : attribute DOT attributeextends : EXTENDS namesnames : names COMMA attribute\n             | attributestatements : statements statement\n                    | statementstatement :   constants_statement\n                   | variables_statement\n                   | assume_statement\n                   | type_invariant\n                   | set_definition\n                   | bean_value_count\n                   | function_declaration\n                   | termination_statement\n                   | next_state_relation\n                   | action_formula_definition\n                   | initconstants_statement : CONSTANTS namesvariables_statement : VARIABLES namesassume_statement : ASSUME expression AND expressionexpression : expression PLUS expression\n                  | expression MINUS expression\n                  | expression STAR expression\n                  | expression DIVIDE expression\n                  | set_membership\n                  | comparison\n                  | attribute\n                  | type_invariant_expression\n                  | NUMBER_LITERAL\n                  | STRING_LITERALtype_invariant_expression : attribute IN_A_SET attributeinit_expression : comparison : attribute comparison_rule NUMBER_LITERAL\n                  | attribute comparison_rule attributecomparison_rule :   GREATER_OR_EQ\n                    | LESS_OR_EQ\n                    | GREATER_THAN                         \n                    | LESS_THAN set_membership : attribute IN_A_SET Nat equals : EQUALS_DEFINITIONS\n              | EQUALS_EQUALITYset_definition : attribute equals LEFT_SQR_BRACKET set_info RIGHT_SQR_BRACKETset_info : set_info COMMA set_individual_info\n                      | set_individual_infoset_individual_info : ATTRIBUTE COLON set_scopeset_scope : NUMBER_LITERAL DOT DOT attributetype_invariant : attribute equals expressioninit : INIT equals attribute IN_A_SET init_set_statementinit_set_statement : LEFT_BRACE attribute IN_A_SET attribute COLON orderorder : dot_access PLUS dot_access IN_A_SET range_of_valuesrange_of_values :  NUMBER_LITERAL DOT DOT attribute RIGHT_BRACEbean_value_count : attribute equals bean_equationbean_equation : dot_access PLUS dot_accessfunction_declaration : attribute equals AND function_conditions except_sectionfunction_conditions : function_condition\n                           | function_conditions AND function_condition\n                           | function_conditions OR function_conditionfunction_condition : attribute comparison_rule NUMBER_LITERAL\n                          | attribute equals NUMBER_LITERAL\n                          | UNCHANGED attribute\n                          | attribute\n                          | attribute DOT attribute comparison_rule NUMBER_LITERALexcept_section : AND NEXT_VALUE_OF_ATTRIBUTE equals except_clauseexcept_clause : LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET\n                     | LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT PLUS NUMBER_LITERAL COMMA EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKETtermination_statement : attribute equals AND function_conditionsnext_state_relation : attribute equals OR function_conditionsaction_formula_definition : attribute equals action_formulaaction_formula : LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET formula_details RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGEformula_details : NEXT_VALUE_OF_ATTRIBUTE LESS_THAN attributeexpression : LEFT_PAREN expression RIGHT_PARENempty :'
    
_lr_action_items = {'MODULE_WRAPPER':([0,4,5,],[2,6,-3,]),'$end':([1,5,9,11,12,13,14,15,16,17,18,19,20,21,22,30,31,33,34,35,37,38,39,40,41,42,45,46,48,51,72,73,74,76,78,79,80,81,82,83,84,85,86,87,88,90,91,99,101,103,105,112,113,115,117,125,128,129,136,145,155,157,165,],[0,-3,-2,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-1,-8,-7,-21,-22,-28,-29,-30,-31,-32,-33,-30,-50,-55,-71,-64,-69,-58,-70,-6,-23,-24,-25,-26,-27,-34,-42,-37,-36,-74,-4,-45,-57,-63,-56,-51,-61,-62,-59,-60,-72,-65,-66,-52,-53,-67,-54,-68,]),'MODULE':([2,],[3,]),'ATTRIBUTE':([3,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,27,28,29,30,31,32,33,34,35,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,53,54,55,56,57,58,59,60,61,62,63,64,67,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,90,91,92,97,98,99,100,101,102,103,105,106,112,113,115,117,120,124,125,127,128,129,130,134,136,139,140,145,151,155,157,159,165,],[5,-3,5,5,5,5,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,5,5,5,5,-43,-44,5,-8,-5,-7,-21,-22,-28,-29,-30,-31,-32,-33,5,5,-30,-50,71,-55,5,5,-71,5,5,5,5,5,5,5,5,-38,-39,-40,-41,5,-64,-69,-58,5,-70,5,-6,-23,-24,-25,-26,-27,-34,-42,-37,-36,-74,-4,-45,71,5,5,-57,5,-63,5,-56,-51,5,-61,-62,-59,-60,5,5,-72,5,-65,-66,5,5,-52,5,5,-53,5,-67,-54,5,-68,]),'EQUALS_DEFINITIONS':([5,7,26,72,116,142,160,],[-3,28,28,28,28,28,28,]),'EQUALS_EQUALITY':([5,7,26,72,116,142,160,],[-3,29,29,29,29,29,29,]),'COMMA':([5,32,33,34,35,68,70,78,107,110,132,153,],[-3,53,-7,53,53,92,-47,-6,-46,-48,-49,156,]),'CONSTANTS':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,30,31,32,33,34,35,37,38,39,40,41,42,45,46,48,51,72,73,74,76,78,79,80,81,82,83,84,85,86,87,88,90,91,99,101,103,105,112,113,115,117,125,128,129,136,145,155,157,165,],[-3,23,23,23,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,23,-8,-5,-7,-21,-22,-28,-29,-30,-31,-32,-33,-30,-50,-55,-71,-64,-69,-58,-70,-6,-23,-24,-25,-26,-27,-34,-42,-37,-36,-74,-4,-45,-57,-63,-56,-51,-61,-62,-59,-60,-72,-65,-66,-52,-53,-67,-54,-68,]),'VARIABLES':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,30,31,32,33,34,35,37,38,39,40,41,42,45,46,48,51,72,73,74,76,78,79,80,81,82,83,84,85,86,87,88,90,91,99,101,103,105,112,113,115,117,125,128,129,136,145,155,157,165,],[-3,24,24,24,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,24,-8,-5,-7,-21,-22,-28,-29,-30,-31,-32,-33,-30,-50,-55,-71,-64,-69,-58,-70,-6,-23,-24,-25,-26,-27,-34,-42,-37,-36,-74,-4,-45,-57,-63,-56,-51,-61,-62,-59,-60,-72,-65,-66,-52,-53,-67,-54,-68,]),'ASSUME':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,30,31,32,33,34,35,37,38,39,40,41,42,45,46,48,51,72,73,74,76,78,79,80,81,82,83,84,85,86,87,88,90,91,99,101,103,105,112,113,115,117,125,128,129,136,145,155,157,165,],[-3,25,25,25,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,25,-8,-5,-7,-21,-22,-28,-29,-30,-31,-32,-33,-30,-50,-55,-71,-64,-69,-58,-70,-6,-23,-24,-25,-26,-27,-34,-42,-37,-36,-74,-4,-45,-57,-63,-56,-51,-61,-62,-59,-60,-72,-65,-66,-52,-53,-67,-54,-68,]),'INIT':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,30,31,32,33,34,35,37,38,39,40,41,42,45,46,48,51,72,73,74,76,78,79,80,81,82,83,84,85,86,87,88,90,91,99,101,103,105,112,113,115,117,125,128,129,136,145,155,157,165,],[-3,26,26,26,-9,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,26,-8,-5,-7,-21,-22,-28,-29,-30,-31,-32,-33,-30,-50,-55,-71,-64,-69,-58,-70,-6,-23,-24,-25,-26,-27,-34,-42,-37,-36,-74,-4,-45,-57,-63,-56,-51,-61,-62,-59,-60,-72,-65,-66,-52,-53,-67,-54,-68,]),'IN_A_SET':([5,39,45,66,90,118,141,],[-3,59,59,89,-4,124,143,]),'GREATER_OR_EQ':([5,39,45,72,114,],[-3,61,61,61,61,]),'LESS_OR_EQ':([5,39,45,72,114,],[-3,62,62,62,62,]),'GREATER_THAN':([5,39,45,72,114,],[-3,63,63,63,63,]),'LESS_THAN':([5,39,45,72,109,114,],[-3,64,64,64,120,64,]),'AND':([5,27,28,29,36,37,38,39,40,41,42,72,73,74,76,80,81,82,83,84,85,86,87,88,101,112,113,115,117,128,],[-3,49,-43,-44,54,-28,-29,-30,-31,-32,-33,-64,98,-58,102,-24,-25,-26,-27,-34,-42,-37,-36,-74,-63,-61,-62,-59,-60,-65,]),'PLUS':([5,36,37,38,39,40,41,42,45,46,52,65,79,80,81,82,83,84,85,86,87,88,90,137,147,],[-3,55,-28,-29,-30,-31,-32,-33,-30,55,77,55,55,-24,-25,-26,-27,-34,-42,-37,-36,-74,-4,139,150,]),'MINUS':([5,36,37,38,39,40,41,42,45,46,65,79,80,81,82,83,84,85,86,87,88,147,162,],[-3,56,-28,-29,-30,-31,-32,-33,-30,56,56,56,-24,-25,-26,-27,-34,-42,-37,-36,-74,149,163,]),'STAR':([5,36,37,38,39,40,41,42,45,46,65,79,80,81,82,83,84,85,86,87,88,],[-3,57,-28,-29,-30,-31,-32,-33,-30,57,57,57,57,57,-26,-27,-34,-42,-37,-36,-74,]),'DIVIDE':([5,36,37,38,39,40,41,42,45,46,65,79,80,81,82,83,84,85,86,87,88,],[-3,58,-28,-29,-30,-31,-32,-33,-30,58,58,58,58,58,-26,-27,-34,-42,-37,-36,-74,]),'DOT':([5,45,72,104,111,121,138,146,148,158,],[-3,67,97,67,121,127,140,148,151,159,]),'RIGHT_PAREN':([5,37,38,39,40,41,42,65,80,81,82,83,84,85,86,87,88,],[-3,-28,-29,-30,-31,-32,-33,88,-24,-25,-26,-27,-34,-42,-37,-36,-74,]),'OR':([5,27,28,29,72,73,74,76,101,112,113,115,117,128,],[-3,50,-43,-44,-64,100,-58,100,-63,-61,-62,-59,-60,-65,]),'RIGHT_SQR_BRACKET':([5,47,68,70,107,108,110,126,132,152,164,],[-3,69,91,-47,-46,119,-48,-73,-49,155,165,]),'COLON':([5,71,131,],[-3,94,134,]),'EXCEPT':([5,133,],[-3,135,]),'RIGHT_BRACE':([5,154,],[-3,157,]),'EXTENDS':([6,],[10,]),'NUMBER_LITERAL':([25,27,28,29,43,54,55,56,57,58,60,61,62,63,64,94,95,96,122,143,149,150,163,],[41,41,-43,-44,41,41,41,41,41,41,87,-38,-39,-40,-41,111,112,113,128,146,152,153,164,]),'STRING_LITERAL':([25,27,28,29,43,54,55,56,57,58,],[42,42,-43,-44,42,42,42,42,42,42,]),'LEFT_PAREN':([25,27,28,29,43,54,55,56,57,58,],[43,43,-43,-44,43,43,43,43,43,43,]),'LEFT_SQR_BRACKET':([27,28,29,69,123,],[47,-43,-44,93,130,]),'AT':([28,29,144,161,],[-43,-44,147,162,]),'UNCHANGED':([49,50,98,100,102,],[75,75,75,75,75,]),'Nat':([59,],[85,]),'LEFT_BRACE':([89,],[106,]),'NEXT_VALUE_OF_ATTRIBUTE':([93,98,],[109,116,]),'ATTRIBUTE_MAY_CHANGE':([119,],[125,]),'EXCLAMATION_MARK':([135,156,],[138,158,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'module':([0,],[1,]),'attribute':([3,6,8,9,10,23,24,25,27,30,43,44,49,50,53,54,55,56,57,58,59,60,67,75,77,97,98,100,102,106,120,124,127,130,134,139,140,151,159,],[4,7,7,7,33,33,33,39,45,7,39,66,72,72,78,39,39,39,39,39,84,86,90,101,104,114,72,72,72,118,126,131,132,133,104,104,142,154,160,]),'extends':([6,],[8,]),'statements':([6,8,],[9,30,]),'statement':([6,8,9,30,],[11,11,31,31,]),'constants_statement':([6,8,9,30,],[12,12,12,12,]),'variables_statement':([6,8,9,30,],[13,13,13,13,]),'assume_statement':([6,8,9,30,],[14,14,14,14,]),'type_invariant':([6,8,9,30,],[15,15,15,15,]),'set_definition':([6,8,9,30,],[16,16,16,16,]),'bean_value_count':([6,8,9,30,],[17,17,17,17,]),'function_declaration':([6,8,9,30,],[18,18,18,18,]),'termination_statement':([6,8,9,30,],[19,19,19,19,]),'next_state_relation':([6,8,9,30,],[20,20,20,20,]),'action_formula_definition':([6,8,9,30,],[21,21,21,21,]),'init':([6,8,9,30,],[22,22,22,22,]),'equals':([7,26,72,116,142,160,],[27,44,96,123,144,161,]),'names':([10,23,24,],[32,34,35,]),'expression':([25,27,43,54,55,56,57,58,],[36,46,65,79,80,81,82,83,]),'set_membership':([25,27,43,54,55,56,57,58,],[37,37,37,37,37,37,37,37,]),'comparison':([25,27,43,54,55,56,57,58,],[38,38,38,38,38,38,38,38,]),'type_invariant_expression':([25,27,43,54,55,56,57,58,],[40,40,40,40,40,40,40,40,]),'bean_equation':([27,],[48,]),'action_formula':([27,],[51,]),'dot_access':([27,77,134,139,],[52,103,137,141,]),'comparison_rule':([39,45,72,114,],[60,60,95,122,]),'set_info':([47,],[68,]),'set_individual_info':([47,92,],[70,107,]),'function_conditions':([49,50,],[73,76,]),'function_condition':([49,50,98,100,102,],[74,74,115,117,115,]),'except_section':([73,],[99,]),'init_set_statement':([89,],[105,]),'formula_details':([93,],[108,]),'set_scope':([94,],[110,]),'except_clause':([123,],[129,]),'order':([134,],[136,]),'range_of_values':([143,],[145,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> module","S'",1,None,None,None),
  ('module -> MODULE_WRAPPER MODULE attribute MODULE_WRAPPER extends statements','module',6,'p_module','parser.py',29),
  ('module -> MODULE_WRAPPER MODULE attribute MODULE_WRAPPER statements','module',5,'p_module','parser.py',30),
  ('attribute -> ATTRIBUTE','attribute',1,'p_attribute','parser.py',38),
  ('dot_access -> attribute DOT attribute','dot_access',3,'p_dot_access','parser.py',43),
  ('extends -> EXTENDS names','extends',2,'p_extends','parser.py',47),
  ('names -> names COMMA attribute','names',3,'p_names','parser.py',53),
  ('names -> attribute','names',1,'p_names','parser.py',54),
  ('statements -> statements statement','statements',2,'p_statements','parser.py',66),
  ('statements -> statement','statements',1,'p_statements','parser.py',67),
  ('statement -> constants_statement','statement',1,'p_statement','parser.py',80),
  ('statement -> variables_statement','statement',1,'p_statement','parser.py',81),
  ('statement -> assume_statement','statement',1,'p_statement','parser.py',82),
  ('statement -> type_invariant','statement',1,'p_statement','parser.py',83),
  ('statement -> set_definition','statement',1,'p_statement','parser.py',84),
  ('statement -> bean_value_count','statement',1,'p_statement','parser.py',85),
  ('statement -> function_declaration','statement',1,'p_statement','parser.py',86),
  ('statement -> termination_statement','statement',1,'p_statement','parser.py',87),
  ('statement -> next_state_relation','statement',1,'p_statement','parser.py',88),
  ('statement -> action_formula_definition','statement',1,'p_statement','parser.py',89),
  ('statement -> init','statement',1,'p_statement','parser.py',90),
  ('constants_statement -> CONSTANTS names','constants_statement',2,'p_constants_statement','parser.py',95),
  ('variables_statement -> VARIABLES names','variables_statement',2,'p_variables_statement','parser.py',100),
  ('assume_statement -> ASSUME expression AND expression','assume_statement',4,'p_assume_statement','parser.py',105),
  ('expression -> expression PLUS expression','expression',3,'p_expression','parser.py',111),
  ('expression -> expression MINUS expression','expression',3,'p_expression','parser.py',112),
  ('expression -> expression STAR expression','expression',3,'p_expression','parser.py',113),
  ('expression -> expression DIVIDE expression','expression',3,'p_expression','parser.py',114),
  ('expression -> set_membership','expression',1,'p_expression','parser.py',115),
  ('expression -> comparison','expression',1,'p_expression','parser.py',116),
  ('expression -> attribute','expression',1,'p_expression','parser.py',117),
  ('expression -> type_invariant_expression','expression',1,'p_expression','parser.py',118),
  ('expression -> NUMBER_LITERAL','expression',1,'p_expression','parser.py',119),
  ('expression -> STRING_LITERAL','expression',1,'p_expression','parser.py',120),
  ('type_invariant_expression -> attribute IN_A_SET attribute','type_invariant_expression',3,'p_type_invariant_expression','parser.py',134),
  ('init_expression -> <empty>','init_expression',0,'p_init_expression','parser.py',138),
  ('comparison -> attribute comparison_rule NUMBER_LITERAL','comparison',3,'p_comparison','parser.py',141),
  ('comparison -> attribute comparison_rule attribute','comparison',3,'p_comparison','parser.py',142),
  ('comparison_rule -> GREATER_OR_EQ','comparison_rule',1,'p_comparison_rule','parser.py',146),
  ('comparison_rule -> LESS_OR_EQ','comparison_rule',1,'p_comparison_rule','parser.py',147),
  ('comparison_rule -> GREATER_THAN','comparison_rule',1,'p_comparison_rule','parser.py',148),
  ('comparison_rule -> LESS_THAN','comparison_rule',1,'p_comparison_rule','parser.py',149),
  ('set_membership -> attribute IN_A_SET Nat','set_membership',3,'p_set_membership','parser.py',153),
  ('equals -> EQUALS_DEFINITIONS','equals',1,'p_equals','parser.py',157),
  ('equals -> EQUALS_EQUALITY','equals',1,'p_equals','parser.py',158),
  ('set_definition -> attribute equals LEFT_SQR_BRACKET set_info RIGHT_SQR_BRACKET','set_definition',5,'p_set_definition','parser.py',162),
  ('set_info -> set_info COMMA set_individual_info','set_info',3,'p_set_info','parser.py',169),
  ('set_info -> set_individual_info','set_info',1,'p_set_info','parser.py',170),
  ('set_individual_info -> ATTRIBUTE COLON set_scope','set_individual_info',3,'p_set_individual_info','parser.py',177),
  ('set_scope -> NUMBER_LITERAL DOT DOT attribute','set_scope',4,'p_set_scope','parser.py',182),
  ('type_invariant -> attribute equals expression','type_invariant',3,'p_type_invariant','parser.py',187),
  ('init -> INIT equals attribute IN_A_SET init_set_statement','init',5,'p_init','parser.py',192),
  ('init_set_statement -> LEFT_BRACE attribute IN_A_SET attribute COLON order','init_set_statement',6,'p_init_set_statement','parser.py',197),
  ('order -> dot_access PLUS dot_access IN_A_SET range_of_values','order',5,'p_order','parser.py',202),
  ('range_of_values -> NUMBER_LITERAL DOT DOT attribute RIGHT_BRACE','range_of_values',5,'p_range_of_values','parser.py',208),
  ('bean_value_count -> attribute equals bean_equation','bean_value_count',3,'p_bean_value_count','parser.py',214),
  ('bean_equation -> dot_access PLUS dot_access','bean_equation',3,'p_bean_equation','parser.py',220),
  ('function_declaration -> attribute equals AND function_conditions except_section','function_declaration',5,'p_function_declaration','parser.py',251),
  ('function_conditions -> function_condition','function_conditions',1,'p_function_conditions','parser.py',256),
  ('function_conditions -> function_conditions AND function_condition','function_conditions',3,'p_function_conditions','parser.py',257),
  ('function_conditions -> function_conditions OR function_condition','function_conditions',3,'p_function_conditions','parser.py',258),
  ('function_condition -> attribute comparison_rule NUMBER_LITERAL','function_condition',3,'p_function_condition','parser.py',267),
  ('function_condition -> attribute equals NUMBER_LITERAL','function_condition',3,'p_function_condition','parser.py',268),
  ('function_condition -> UNCHANGED attribute','function_condition',2,'p_function_condition','parser.py',269),
  ('function_condition -> attribute','function_condition',1,'p_function_condition','parser.py',270),
  ('function_condition -> attribute DOT attribute comparison_rule NUMBER_LITERAL','function_condition',5,'p_function_condition','parser.py',271),
  ('except_section -> AND NEXT_VALUE_OF_ATTRIBUTE equals except_clause','except_section',4,'p_except_section','parser.py',283),
  ('except_clause -> LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET','except_clause',11,'p_except_clause','parser.py',288),
  ('except_clause -> LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT PLUS NUMBER_LITERAL COMMA EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET','except_clause',19,'p_except_clause','parser.py',289),
  ('termination_statement -> attribute equals AND function_conditions','termination_statement',4,'p_termination_statement','parser.py',298),
  ('next_state_relation -> attribute equals OR function_conditions','next_state_relation',4,'p_next_state_relation','parser.py',304),
  ('action_formula_definition -> attribute equals action_formula','action_formula_definition',3,'p_action_formula_definition','parser.py',310),
  ('action_formula -> LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET formula_details RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE','action_formula',6,'p_action_formula','parser.py',315),
  ('formula_details -> NEXT_VALUE_OF_ATTRIBUTE LESS_THAN attribute','formula_details',3,'p_action_details','parser.py',321),
  ('expression -> LEFT_PAREN expression RIGHT_PAREN','expression',3,'p_expression_group','parser.py',332),
  ('empty -> <empty>','empty',0,'p_empty','parser.py',337),
]
