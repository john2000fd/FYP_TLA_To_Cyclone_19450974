
# parsetab.py
# This file is automatically generated. Do not edit.
# pylint: disable=W,C,R
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = 'leftEQUIVALENCE_OPERATORleftANDnonassocEQUALS_DEFINITIONSNOT_EQUALSnonassocLESS_THANLESS_OR_EQGREATER_THANGREATER_OR_EQleftPLUSMINUSleftSTARDIVIDEMODULUSnonassocLEFT_PARENRIGHT_PARENAND ARROW ASSUME AT ATTRIBUTE ATTRIBUTE_MAY_CHANGE BACK_SLASH CHECK COLON COMMA CONSTANTS DIVIDE DOT EDGE ELSE ENABLED EQUALS_DEFINITIONS EQUALS_EQUALITY EQUIVALENCE_OPERATOR EVENTUALLY EXCEPT EXCLAMATION_MARK EXTENDS EventuallyTerminates FORWARD_SLASH GOAL GRAPH GREATER_OR_EQ GREATER_THAN IF IMPLIES INIT INVARIANT IN_A_SET LEFT_BRACE LEFT_PAREN LEFT_SQR_BRACKET LESS_OR_EQ LESS_THAN LoopInvariant MINUS MODULE MODULE_WRAPPER MODULUS NEXT_VALUE_OF_ATTRIBUTE NODE NOT_EQUALS NUMBER_LITERAL Nat OR PLUS RIGHT_BRACE RIGHT_PAREN RIGHT_SQR_BRACKET SEMICOLON SINGLE_QUOTE SPEC STAR STRING_LITERAL THEN THEOREM TerminationHypothesis UNCHANGED UNDERSCORE VARIABLES VARIABLE_NAME WEAK_FAIRNESSmodule : MODULE_WRAPPER MODULE attribute MODULE_WRAPPER extends statements\n              | MODULE_WRAPPER MODULE attribute MODULE_WRAPPER statementsattribute : ATTRIBUTEdot_access : attribute DOT attribute\n                  | NEXT_VALUE_OF_ATTRIBUTE DOT attributeextends : EXTENDS namesnames : names COMMA attribute\n             | attributestatements : statements statement\n                    | statementstatement :   constants_statement\n                   | variables_statement\n                   | assume_statement\n                   | type_invariant\n                   | set_definition\n                   | bean_value_count\n                   | function_declaration\n                   | termination_statement\n                   | next_state_relation\n                   | action_formula_definition\n                   | liveness_property\n                   | loop_invariant\n                   | termination_hypothesis\n                   | spec_definition\n                   | theorem_definition\n                   | initconstants_statement : CONSTANTS namesvariables_statement : VARIABLES namesassume_statement : ASSUME attribute IN_A_SET Nat AND attribute GREATER_OR_EQ NUMBER_LITERALexpression : expression PLUS expression\n                  | expression MINUS expression\n                  | expression STAR expression\n                  | expression DIVIDE expression\n                  | set_membership\n                  | comparison\n                  | attribute\n                  | type_invariant_expression\n                  | NUMBER_LITERAL\n                  | STRING_LITERALtype_invariant_expression : attribute IN_A_SET attributecomparison : attribute comparison_rule NUMBER_LITERAL\n                  | attribute comparison_rule attributecomparison_rule :   GREATER_OR_EQ\n                    | LESS_OR_EQ\n                    | GREATER_THAN                         \n                    | LESS_THAN set_membership : attribute IN_A_SET Nat equals : EQUALS_DEFINITIONS\n              | EQUALS_EQUALITYset_definition : attribute equals LEFT_SQR_BRACKET set_info RIGHT_SQR_BRACKETset_info : set_info COMMA set_individual_info\n                      | set_individual_infoset_individual_info : ATTRIBUTE COLON set_scopeset_scope : NUMBER_LITERAL DOT DOT attributetype_invariant : attribute equals expressioninit : INIT equals attribute IN_A_SET init_set_statementinit_set_statement : LEFT_BRACE attribute IN_A_SET attribute COLON orderorder : dot_access PLUS dot_access IN_A_SET range_of_valuesrange_of_values :  NUMBER_LITERAL DOT DOT attribute RIGHT_BRACEbean_value_count : attribute equals bean_equationbean_equation : dot_access PLUS dot_accessfunction_declaration : attribute equals AND function_info AND function_info except_section\n                            | attribute equals AND function_info AND function_info AND function_info except_sectionfunction_info : attribute DOT attribute comparison_rule NUMBER_LITERAL\n                     | attribute comparison_rule NUMBER_LITERALfunction_conditions : function_condition\n                           | function_conditions AND function_condition\n                           | function_conditions OR function_conditionfunction_condition : attribute comparison_rule NUMBER_LITERAL\n                          | attribute equals NUMBER_LITERAL\n                          | UNCHANGED attribute\n                          | LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET attribute RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE\n                          | WEAK_FAIRNESS ATTRIBUTE_MAY_CHANGE LEFT_PAREN attribute RIGHT_PAREN\n                          | attribute\n                          | INIT\n                          | EventuallyTerminates\n                          | LoopInvariant\n                          | TerminationHypothesis\n                          | attribute DOT attribute comparison_rule NUMBER_LITERALexcept_section : AND NEXT_VALUE_OF_ATTRIBUTE equals except_clauseexcept_clause : LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET\n                     | LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT PLUS NUMBER_LITERAL COMMA EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKETtermination_statement : attribute equals AND termination_info AND termination_infotermination_info : attribute equals NUMBER_LITERAL\n                        | UNCHANGED attributenext_state_relation : attribute equals OR next_state_info OR next_state_info OR next_state_info OR next_state_infonext_state_info : attributeaction_formula_definition : attribute equals action_formulaaction_formula : LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET formula_details RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGEformula_details : NEXT_VALUE_OF_ATTRIBUTE LESS_THAN attribute\n                       | dot_access MODULUS expression equals NUMBER_LITERAL EQUIVALENCE_OPERATOR dot_access MODULUS expression equals NUMBER_LITERALliveness_property : EventuallyTerminates equals property_detailsproperty_details : EVENTUALLY LEFT_PAREN ENABLED attribute RIGHT_PARENloop_invariant : LoopInvariant equals action_formulatermination_hypothesis : TerminationHypothesis equals conditional_statementsconditional_statements : IF conditional_statement THEN conditional_statement ELSE conditional_statementconditional_statement : dot_access MODULUS NUMBER_LITERAL equals NUMBER_LITERAL\n                             | EVENTUALLY LEFT_PAREN dot_access equals NUMBER_LITERAL AND dot_access equals NUMBER_LITERAL RIGHT_PARENspec_definition : SPEC equals AND spec_info AND spec_info AND spec_infospec_info : LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET attribute RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE\n                 | WEAK_FAIRNESS ATTRIBUTE_MAY_CHANGE LEFT_PAREN attribute RIGHT_PAREN\n                 | INITtheorem_definition : THEOREM SPEC IMPLIES AND theorem_info AND theorem_info AND theorem_info AND theorem_info AND theorem_infotheorem_info : EventuallyTerminates\n                    | attribute\n                    | LoopInvariant\n                    | TerminationHypothesisexpression : LEFT_PAREN expression RIGHT_PAREN'
    
_lr_action_items = {'MODULE_WRAPPER':([0,4,5,],[2,6,-3,]),'$end':([1,5,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,185,188,197,205,206,207,209,211,217,221,225,227,230,244,245,249,261,264,273,],[0,-3,-2,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,-1,-9,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,-62,-93,-89,-29,-96,-97,-99,-101,-63,-100,-80,-86,-57,-98,-103,-58,-59,-81,-82,]),'MODULE':([2,],[3,]),'ATTRIBUTE':([3,5,6,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,37,38,39,40,41,42,43,44,45,52,53,54,55,56,57,58,59,60,61,62,63,64,65,68,70,72,74,75,79,80,81,82,83,84,85,86,87,88,89,97,98,101,102,103,104,114,115,117,118,119,120,121,122,123,124,125,126,127,128,130,133,134,135,136,137,138,139,140,141,142,144,149,150,151,152,153,154,163,167,175,176,177,180,181,184,185,186,188,189,196,197,200,205,206,207,209,211,212,217,219,220,221,223,225,226,227,229,230,232,236,240,242,244,245,248,249,256,261,264,267,273,],[5,-3,5,5,5,5,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,5,5,5,5,-48,-49,5,-9,-6,-8,-27,-28,5,-36,-55,93,-60,5,5,-88,-34,-35,-37,-38,-39,5,5,-92,-94,-95,5,5,5,5,-43,-44,-45,-46,5,5,5,5,5,-87,-36,5,5,-7,-102,5,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,93,5,5,5,5,-85,5,-108,-61,-5,5,5,5,5,-104,-105,-106,-107,-56,5,-84,-83,5,5,5,5,5,5,-62,5,-93,5,5,-89,5,-29,-96,-97,-99,-101,5,-63,5,5,-100,5,-80,5,-86,5,-57,5,5,5,5,-98,-103,5,-58,5,-59,-81,5,-82,]),'EQUALS_DEFINITIONS':([5,7,31,32,33,34,36,60,61,62,63,64,94,101,117,118,119,120,121,122,123,124,125,137,139,166,172,173,199,203,228,247,252,268,],[-3,38,38,38,38,38,38,-34,-35,-37,-38,-39,38,-36,-40,-47,-42,-41,-4,-30,-31,-32,-33,-108,-5,38,38,38,38,38,38,38,38,38,]),'EQUALS_EQUALITY':([5,7,31,32,33,34,36,60,61,62,63,64,94,101,117,118,119,120,121,122,123,124,125,137,139,166,172,173,199,203,228,247,252,268,],[-3,39,39,39,39,39,39,-34,-35,-37,-38,-39,39,-36,-40,-47,-42,-41,-4,-30,-31,-32,-33,-108,-5,39,39,39,39,39,39,39,39,39,]),'COMMA':([5,42,43,44,45,90,92,104,155,159,215,263,],[-3,68,-8,68,68,127,-52,-7,-51,-53,-54,265,]),'CONSTANTS':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,185,188,197,205,206,207,209,211,217,221,225,227,230,244,245,249,261,264,273,],[-3,28,28,28,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,28,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,-62,-93,-89,-29,-96,-97,-99,-101,-63,-100,-80,-86,-57,-98,-103,-58,-59,-81,-82,]),'VARIABLES':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,185,188,197,205,206,207,209,211,217,221,225,227,230,244,245,249,261,264,273,],[-3,29,29,29,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,29,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,-62,-93,-89,-29,-96,-97,-99,-101,-63,-100,-80,-86,-57,-98,-103,-58,-59,-81,-82,]),'ASSUME':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,185,188,197,205,206,207,209,211,217,221,225,227,230,244,245,249,261,264,273,],[-3,30,30,30,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,30,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,-62,-93,-89,-29,-96,-97,-99,-101,-63,-100,-80,-86,-57,-98,-103,-58,-59,-81,-82,]),'EventuallyTerminates':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,115,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,177,185,188,197,205,206,207,209,211,212,217,221,225,227,229,230,240,244,245,249,261,264,273,],[-3,31,31,31,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,31,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,149,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,149,-62,-93,-89,-29,-96,-97,-99,-101,149,-63,-100,-80,-86,149,-57,149,-98,-103,-58,-59,-81,-82,]),'LoopInvariant':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,115,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,177,185,188,197,205,206,207,209,211,212,217,221,225,227,229,230,240,244,245,249,261,264,273,],[-3,32,32,32,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,32,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,151,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,151,-62,-93,-89,-29,-96,-97,-99,-101,151,-63,-100,-80,-86,151,-57,151,-98,-103,-58,-59,-81,-82,]),'TerminationHypothesis':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,115,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,177,185,188,197,205,206,207,209,211,212,217,221,225,227,229,230,240,244,245,249,261,264,273,],[-3,33,33,33,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,33,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,152,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,152,-62,-93,-89,-29,-96,-97,-99,-101,152,-63,-100,-80,-86,152,-57,152,-98,-103,-58,-59,-81,-82,]),'SPEC':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,35,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,185,188,197,205,206,207,209,211,217,221,225,227,230,244,245,249,261,264,273,],[-3,34,34,34,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,51,34,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,-62,-93,-89,-29,-96,-97,-99,-101,-63,-100,-80,-86,-57,-98,-103,-58,-59,-81,-82,]),'THEOREM':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,98,101,104,114,117,118,119,120,121,122,123,124,125,126,135,137,138,139,149,150,151,152,153,163,167,185,188,197,205,206,207,209,211,217,221,225,227,230,244,245,249,261,264,273,],[-3,35,35,35,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,35,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,-87,-36,-7,-102,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,-104,-105,-106,-107,-56,-84,-83,-62,-93,-89,-29,-96,-97,-99,-101,-63,-100,-80,-86,-57,-98,-103,-58,-59,-81,-82,]),'INIT':([5,6,8,9,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,40,41,42,43,44,45,53,54,56,59,60,61,62,63,64,70,72,74,76,98,101,104,114,117,118,119,120,121,122,123,124,125,126,135,137,138,139,145,149,150,151,152,153,163,167,185,188,192,197,205,206,207,209,211,217,221,225,227,230,244,245,249,261,264,273,],[-3,36,36,36,-10,-11,-12,-13,-14,-15,-16,-17,-18,-19,-20,-21,-22,-23,-24,-25,-26,36,-9,-6,-8,-27,-28,-36,-55,-60,-88,-34,-35,-37,-38,-39,-92,-94,-95,114,-87,-36,-7,-102,-40,-47,-42,-41,-4,-30,-31,-32,-33,-50,-85,-108,-61,-5,114,-104,-105,-106,-107,-56,-84,-83,-62,-93,114,-89,-29,-96,-97,-99,-101,-63,-100,-80,-86,-57,-98,-103,-58,-59,-81,-82,]),'IN_A_SET':([5,46,53,78,101,121,139,178,241,],[-3,69,79,116,79,-4,-5,196,246,]),'DOT':([5,53,67,94,110,157,160,164,182,243,250,253,266,],[-3,81,103,130,81,103,182,130,200,248,253,256,267,]),'GREATER_OR_EQ':([5,53,94,101,161,164,169,],[-3,82,82,82,82,82,187,]),'LESS_OR_EQ':([5,53,94,101,161,164,],[-3,83,83,83,83,83,]),'GREATER_THAN':([5,53,94,101,161,164,],[-3,84,84,84,84,84,]),'LESS_THAN':([5,53,94,101,157,161,164,],[-3,85,85,85,180,85,85,]),'PLUS':([5,53,54,60,61,62,63,64,66,100,101,117,118,119,120,121,122,123,124,125,137,139,199,231,247,257,],[-3,-36,86,-34,-35,-37,-38,-39,102,86,-36,-40,-47,-42,-41,-4,-30,-31,-32,-33,-108,-5,86,236,86,260,]),'MINUS':([5,53,54,60,61,62,63,64,100,101,117,118,119,120,122,123,124,125,137,199,247,257,270,],[-3,-36,87,-34,-35,-37,-38,-39,87,-36,-40,-47,-42,-41,-30,-31,-32,-33,-108,87,87,259,271,]),'STAR':([5,53,54,60,61,62,63,64,100,101,117,118,119,120,122,123,124,125,137,199,247,],[-3,-36,88,-34,-35,-37,-38,-39,88,-36,-40,-47,-42,-41,88,88,-32,-33,-108,88,88,]),'DIVIDE':([5,53,54,60,61,62,63,64,100,101,117,118,119,120,122,123,124,125,137,199,247,],[-3,-36,89,-34,-35,-37,-38,-39,89,-36,-40,-47,-42,-41,89,89,-32,-33,-108,89,89,]),'OR':([5,37,38,39,98,99,168,204,],[-3,58,-48,-49,-87,136,186,219,]),'RIGHT_PAREN':([5,60,61,62,63,64,100,101,117,118,119,120,122,123,124,125,137,170,194,239,],[-3,-34,-35,-37,-38,-39,137,-36,-40,-47,-42,-41,-30,-31,-32,-33,-108,188,211,244,]),'MODULUS':([5,108,121,139,158,237,],[-3,143,-4,-5,181,242,]),'AND':([5,37,38,39,50,77,95,96,105,111,114,135,148,149,150,151,152,162,163,165,174,195,201,202,208,211,221,222,235,],[-3,57,-48,-49,76,115,133,134,140,145,-102,-85,177,-104,-105,-106,-107,-65,-84,184,192,212,-64,216,220,-101,-100,229,240,]),'RIGHT_SQR_BRACKET':([5,55,73,90,92,112,155,156,159,193,198,215,254,262,272,],[-3,91,91,126,-52,146,-51,179,-53,210,-90,-54,-91,264,273,]),'COLON':([5,93,213,],[-3,129,223,]),'EXCEPT':([5,233,],[-3,238,]),'RIGHT_BRACE':([5,258,],[-3,261,]),'EXTENDS':([6,],[10,]),'LEFT_SQR_BRACKET':([37,38,39,48,76,91,145,146,192,218,],[55,-48,-49,73,112,128,112,175,112,226,]),'NUMBER_LITERAL':([37,38,39,65,80,82,83,84,85,86,87,88,89,129,131,132,143,181,183,187,190,191,214,234,242,246,251,259,260,271,],[63,-48,-49,63,120,-43,-44,-45,-46,63,63,63,63,160,162,163,172,63,201,205,207,208,224,239,63,250,254,262,263,272,]),'STRING_LITERAL':([37,38,39,65,86,87,88,89,181,242,],[64,-48,-49,64,64,64,64,64,64,64,]),'LEFT_PAREN':([37,38,39,65,71,86,87,88,89,109,147,181,242,],[65,-48,-49,65,106,65,65,65,65,144,176,65,65,]),'NEXT_VALUE_OF_ATTRIBUTE':([37,38,39,75,102,128,142,144,184,189,216,220,223,232,236,],[67,-48,-49,67,67,157,67,67,203,67,203,67,67,67,67,]),'EVENTUALLY':([38,39,47,75,142,189,],[-48,-49,71,109,109,109,]),'IF':([38,39,49,],[-48,-49,75,]),'AT':([38,39,255,269,],[-48,-49,257,270,]),'IMPLIES':([51,],[77,]),'UNCHANGED':([57,134,],[97,97,]),'Nat':([69,79,],[105,118,]),'WEAK_FAIRNESS':([76,145,192,],[113,113,113,]),'ENABLED':([106,],[141,]),'THEN':([107,207,244,],[142,-97,-98,]),'ATTRIBUTE_MAY_CHANGE':([113,179,210,],[147,197,221,]),'LEFT_BRACE':([116,],[154,]),'ELSE':([171,207,244,],[189,-97,-98,]),'EQUIVALENCE_OPERATOR':([224,],[232,]),'EXCLAMATION_MARK':([238,265,],[243,266,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'module':([0,],[1,]),'attribute':([3,6,8,9,10,28,29,30,37,40,52,57,58,65,68,75,79,80,81,86,87,88,89,97,102,103,115,128,130,133,134,136,140,141,142,144,154,175,176,177,180,181,184,186,189,196,200,212,219,220,223,226,229,232,236,240,242,248,256,267,],[4,7,7,7,43,43,43,46,53,7,78,94,98,101,104,110,117,119,121,101,101,101,101,135,110,139,150,110,161,164,166,98,169,170,110,110,178,193,194,150,198,101,164,98,110,213,215,150,98,110,110,233,150,110,110,150,101,252,258,268,]),'extends':([6,],[8,]),'statements':([6,8,],[9,40,]),'statement':([6,8,9,40,],[11,11,41,41,]),'constants_statement':([6,8,9,40,],[12,12,12,12,]),'variables_statement':([6,8,9,40,],[13,13,13,13,]),'assume_statement':([6,8,9,40,],[14,14,14,14,]),'type_invariant':([6,8,9,40,],[15,15,15,15,]),'set_definition':([6,8,9,40,],[16,16,16,16,]),'bean_value_count':([6,8,9,40,],[17,17,17,17,]),'function_declaration':([6,8,9,40,],[18,18,18,18,]),'termination_statement':([6,8,9,40,],[19,19,19,19,]),'next_state_relation':([6,8,9,40,],[20,20,20,20,]),'action_formula_definition':([6,8,9,40,],[21,21,21,21,]),'liveness_property':([6,8,9,40,],[22,22,22,22,]),'loop_invariant':([6,8,9,40,],[23,23,23,23,]),'termination_hypothesis':([6,8,9,40,],[24,24,24,24,]),'spec_definition':([6,8,9,40,],[25,25,25,25,]),'theorem_definition':([6,8,9,40,],[26,26,26,26,]),'init':([6,8,9,40,],[27,27,27,27,]),'equals':([7,31,32,33,34,36,94,166,172,173,199,203,228,247,252,268,],[37,47,48,49,50,52,132,132,190,191,214,218,234,251,255,269,]),'names':([10,28,29,],[42,44,45,]),'expression':([37,65,86,87,88,89,181,242,],[54,100,122,123,124,125,199,247,]),'bean_equation':([37,],[56,]),'action_formula':([37,48,],[59,72,]),'set_membership':([37,65,86,87,88,89,181,242,],[60,60,60,60,60,60,60,60,]),'comparison':([37,65,86,87,88,89,181,242,],[61,61,61,61,61,61,61,61,]),'type_invariant_expression':([37,65,86,87,88,89,181,242,],[62,62,62,62,62,62,62,62,]),'dot_access':([37,75,102,128,142,144,189,220,223,232,236,],[66,108,138,158,108,173,108,228,231,237,241,]),'property_details':([47,],[70,]),'conditional_statements':([49,],[74,]),'comparison_rule':([53,94,101,161,164,],[80,131,80,183,131,]),'set_info':([55,],[90,]),'set_individual_info':([55,127,],[92,155,]),'function_info':([57,133,184,],[95,165,202,]),'termination_info':([57,134,],[96,167,]),'next_state_info':([58,136,186,219,],[99,168,204,227,]),'conditional_statement':([75,142,189,],[107,171,206,]),'spec_info':([76,145,192,],[111,174,209,]),'theorem_info':([115,177,212,229,240,],[148,195,222,235,245,]),'init_set_statement':([116,],[153,]),'formula_details':([128,],[156,]),'set_scope':([129,],[159,]),'except_section':([165,202,],[185,217,]),'except_clause':([218,],[225,]),'order':([223,],[230,]),'range_of_values':([246,],[249,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> module","S'",1,None,None,None),
  ('module -> MODULE_WRAPPER MODULE attribute MODULE_WRAPPER extends statements','module',6,'p_module','tla_parser.py',35),
  ('module -> MODULE_WRAPPER MODULE attribute MODULE_WRAPPER statements','module',5,'p_module','tla_parser.py',36),
  ('attribute -> ATTRIBUTE','attribute',1,'p_attribute','tla_parser.py',44),
  ('dot_access -> attribute DOT attribute','dot_access',3,'p_dot_access','tla_parser.py',49),
  ('dot_access -> NEXT_VALUE_OF_ATTRIBUTE DOT attribute','dot_access',3,'p_dot_access','tla_parser.py',50),
  ('extends -> EXTENDS names','extends',2,'p_extends','tla_parser.py',55),
  ('names -> names COMMA attribute','names',3,'p_names','tla_parser.py',61),
  ('names -> attribute','names',1,'p_names','tla_parser.py',62),
  ('statements -> statements statement','statements',2,'p_statements','tla_parser.py',74),
  ('statements -> statement','statements',1,'p_statements','tla_parser.py',75),
  ('statement -> constants_statement','statement',1,'p_statement','tla_parser.py',88),
  ('statement -> variables_statement','statement',1,'p_statement','tla_parser.py',89),
  ('statement -> assume_statement','statement',1,'p_statement','tla_parser.py',90),
  ('statement -> type_invariant','statement',1,'p_statement','tla_parser.py',91),
  ('statement -> set_definition','statement',1,'p_statement','tla_parser.py',92),
  ('statement -> bean_value_count','statement',1,'p_statement','tla_parser.py',93),
  ('statement -> function_declaration','statement',1,'p_statement','tla_parser.py',94),
  ('statement -> termination_statement','statement',1,'p_statement','tla_parser.py',95),
  ('statement -> next_state_relation','statement',1,'p_statement','tla_parser.py',96),
  ('statement -> action_formula_definition','statement',1,'p_statement','tla_parser.py',97),
  ('statement -> liveness_property','statement',1,'p_statement','tla_parser.py',98),
  ('statement -> loop_invariant','statement',1,'p_statement','tla_parser.py',99),
  ('statement -> termination_hypothesis','statement',1,'p_statement','tla_parser.py',100),
  ('statement -> spec_definition','statement',1,'p_statement','tla_parser.py',101),
  ('statement -> theorem_definition','statement',1,'p_statement','tla_parser.py',102),
  ('statement -> init','statement',1,'p_statement','tla_parser.py',103),
  ('constants_statement -> CONSTANTS names','constants_statement',2,'p_constants_statement','tla_parser.py',108),
  ('variables_statement -> VARIABLES names','variables_statement',2,'p_variables_statement','tla_parser.py',113),
  ('assume_statement -> ASSUME attribute IN_A_SET Nat AND attribute GREATER_OR_EQ NUMBER_LITERAL','assume_statement',8,'p_assume_statement','tla_parser.py',118),
  ('expression -> expression PLUS expression','expression',3,'p_expression','tla_parser.py',125),
  ('expression -> expression MINUS expression','expression',3,'p_expression','tla_parser.py',126),
  ('expression -> expression STAR expression','expression',3,'p_expression','tla_parser.py',127),
  ('expression -> expression DIVIDE expression','expression',3,'p_expression','tla_parser.py',128),
  ('expression -> set_membership','expression',1,'p_expression','tla_parser.py',129),
  ('expression -> comparison','expression',1,'p_expression','tla_parser.py',130),
  ('expression -> attribute','expression',1,'p_expression','tla_parser.py',131),
  ('expression -> type_invariant_expression','expression',1,'p_expression','tla_parser.py',132),
  ('expression -> NUMBER_LITERAL','expression',1,'p_expression','tla_parser.py',133),
  ('expression -> STRING_LITERAL','expression',1,'p_expression','tla_parser.py',134),
  ('type_invariant_expression -> attribute IN_A_SET attribute','type_invariant_expression',3,'p_type_invariant_expression','tla_parser.py',141),
  ('comparison -> attribute comparison_rule NUMBER_LITERAL','comparison',3,'p_comparison','tla_parser.py',146),
  ('comparison -> attribute comparison_rule attribute','comparison',3,'p_comparison','tla_parser.py',147),
  ('comparison_rule -> GREATER_OR_EQ','comparison_rule',1,'p_comparison_rule','tla_parser.py',152),
  ('comparison_rule -> LESS_OR_EQ','comparison_rule',1,'p_comparison_rule','tla_parser.py',153),
  ('comparison_rule -> GREATER_THAN','comparison_rule',1,'p_comparison_rule','tla_parser.py',154),
  ('comparison_rule -> LESS_THAN','comparison_rule',1,'p_comparison_rule','tla_parser.py',155),
  ('set_membership -> attribute IN_A_SET Nat','set_membership',3,'p_set_membership','tla_parser.py',160),
  ('equals -> EQUALS_DEFINITIONS','equals',1,'p_equals','tla_parser.py',165),
  ('equals -> EQUALS_EQUALITY','equals',1,'p_equals','tla_parser.py',166),
  ('set_definition -> attribute equals LEFT_SQR_BRACKET set_info RIGHT_SQR_BRACKET','set_definition',5,'p_set_definition','tla_parser.py',171),
  ('set_info -> set_info COMMA set_individual_info','set_info',3,'p_set_info','tla_parser.py',178),
  ('set_info -> set_individual_info','set_info',1,'p_set_info','tla_parser.py',179),
  ('set_individual_info -> ATTRIBUTE COLON set_scope','set_individual_info',3,'p_set_individual_info','tla_parser.py',186),
  ('set_scope -> NUMBER_LITERAL DOT DOT attribute','set_scope',4,'p_set_scope','tla_parser.py',191),
  ('type_invariant -> attribute equals expression','type_invariant',3,'p_type_invariant','tla_parser.py',196),
  ('init -> INIT equals attribute IN_A_SET init_set_statement','init',5,'p_init','tla_parser.py',201),
  ('init_set_statement -> LEFT_BRACE attribute IN_A_SET attribute COLON order','init_set_statement',6,'p_init_set_statement','tla_parser.py',206),
  ('order -> dot_access PLUS dot_access IN_A_SET range_of_values','order',5,'p_order','tla_parser.py',211),
  ('range_of_values -> NUMBER_LITERAL DOT DOT attribute RIGHT_BRACE','range_of_values',5,'p_range_of_values','tla_parser.py',216),
  ('bean_value_count -> attribute equals bean_equation','bean_value_count',3,'p_bean_value_count','tla_parser.py',222),
  ('bean_equation -> dot_access PLUS dot_access','bean_equation',3,'p_bean_equation','tla_parser.py',228),
  ('function_declaration -> attribute equals AND function_info AND function_info except_section','function_declaration',7,'p_function_declaration','tla_parser.py',238),
  ('function_declaration -> attribute equals AND function_info AND function_info AND function_info except_section','function_declaration',9,'p_function_declaration','tla_parser.py',239),
  ('function_info -> attribute DOT attribute comparison_rule NUMBER_LITERAL','function_info',5,'p_function_info','tla_parser.py',248),
  ('function_info -> attribute comparison_rule NUMBER_LITERAL','function_info',3,'p_function_info','tla_parser.py',249),
  ('function_conditions -> function_condition','function_conditions',1,'p_function_conditions','tla_parser.py',259),
  ('function_conditions -> function_conditions AND function_condition','function_conditions',3,'p_function_conditions','tla_parser.py',260),
  ('function_conditions -> function_conditions OR function_condition','function_conditions',3,'p_function_conditions','tla_parser.py',261),
  ('function_condition -> attribute comparison_rule NUMBER_LITERAL','function_condition',3,'p_function_condition','tla_parser.py',270),
  ('function_condition -> attribute equals NUMBER_LITERAL','function_condition',3,'p_function_condition','tla_parser.py',271),
  ('function_condition -> UNCHANGED attribute','function_condition',2,'p_function_condition','tla_parser.py',272),
  ('function_condition -> LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET attribute RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE','function_condition',6,'p_function_condition','tla_parser.py',273),
  ('function_condition -> WEAK_FAIRNESS ATTRIBUTE_MAY_CHANGE LEFT_PAREN attribute RIGHT_PAREN','function_condition',5,'p_function_condition','tla_parser.py',274),
  ('function_condition -> attribute','function_condition',1,'p_function_condition','tla_parser.py',275),
  ('function_condition -> INIT','function_condition',1,'p_function_condition','tla_parser.py',276),
  ('function_condition -> EventuallyTerminates','function_condition',1,'p_function_condition','tla_parser.py',277),
  ('function_condition -> LoopInvariant','function_condition',1,'p_function_condition','tla_parser.py',278),
  ('function_condition -> TerminationHypothesis','function_condition',1,'p_function_condition','tla_parser.py',279),
  ('function_condition -> attribute DOT attribute comparison_rule NUMBER_LITERAL','function_condition',5,'p_function_condition','tla_parser.py',280),
  ('except_section -> AND NEXT_VALUE_OF_ATTRIBUTE equals except_clause','except_section',4,'p_except_section','tla_parser.py',293),
  ('except_clause -> LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET','except_clause',11,'p_except_clause','tla_parser.py',298),
  ('except_clause -> LEFT_SQR_BRACKET attribute EXCEPT EXCLAMATION_MARK DOT attribute equals AT PLUS NUMBER_LITERAL COMMA EXCLAMATION_MARK DOT attribute equals AT MINUS NUMBER_LITERAL RIGHT_SQR_BRACKET','except_clause',19,'p_except_clause','tla_parser.py',299),
  ('termination_statement -> attribute equals AND termination_info AND termination_info','termination_statement',6,'p_termination_statement','tla_parser.py',308),
  ('termination_info -> attribute equals NUMBER_LITERAL','termination_info',3,'p_termination_info','tla_parser.py',314),
  ('termination_info -> UNCHANGED attribute','termination_info',2,'p_termination_info','tla_parser.py',315),
  ('next_state_relation -> attribute equals OR next_state_info OR next_state_info OR next_state_info OR next_state_info','next_state_relation',10,'p_next_state_relation','tla_parser.py',326),
  ('next_state_info -> attribute','next_state_info',1,'p_next_state_info','tla_parser.py',332),
  ('action_formula_definition -> attribute equals action_formula','action_formula_definition',3,'p_action_formula_definition','tla_parser.py',337),
  ('action_formula -> LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET formula_details RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE','action_formula',6,'p_action_formula','tla_parser.py',342),
  ('formula_details -> NEXT_VALUE_OF_ATTRIBUTE LESS_THAN attribute','formula_details',3,'p_formula_details','tla_parser.py',348),
  ('formula_details -> dot_access MODULUS expression equals NUMBER_LITERAL EQUIVALENCE_OPERATOR dot_access MODULUS expression equals NUMBER_LITERAL','formula_details',11,'p_formula_details','tla_parser.py',349),
  ('liveness_property -> EventuallyTerminates equals property_details','liveness_property',3,'p_liveness_property','tla_parser.py',358),
  ('property_details -> EVENTUALLY LEFT_PAREN ENABLED attribute RIGHT_PAREN','property_details',5,'p_property_details','tla_parser.py',364),
  ('loop_invariant -> LoopInvariant equals action_formula','loop_invariant',3,'p_loop_invariant','tla_parser.py',372),
  ('termination_hypothesis -> TerminationHypothesis equals conditional_statements','termination_hypothesis',3,'p_termination_hypothesis','tla_parser.py',380),
  ('conditional_statements -> IF conditional_statement THEN conditional_statement ELSE conditional_statement','conditional_statements',6,'p_conditional_statements','tla_parser.py',386),
  ('conditional_statement -> dot_access MODULUS NUMBER_LITERAL equals NUMBER_LITERAL','conditional_statement',5,'p_conditional_statement','tla_parser.py',392),
  ('conditional_statement -> EVENTUALLY LEFT_PAREN dot_access equals NUMBER_LITERAL AND dot_access equals NUMBER_LITERAL RIGHT_PAREN','conditional_statement',10,'p_conditional_statement','tla_parser.py',393),
  ('spec_definition -> SPEC equals AND spec_info AND spec_info AND spec_info','spec_definition',8,'p_spec_definition','tla_parser.py',407),
  ('spec_info -> LEFT_SQR_BRACKET RIGHT_SQR_BRACKET LEFT_SQR_BRACKET attribute RIGHT_SQR_BRACKET ATTRIBUTE_MAY_CHANGE','spec_info',6,'p_spec_info','tla_parser.py',413),
  ('spec_info -> WEAK_FAIRNESS ATTRIBUTE_MAY_CHANGE LEFT_PAREN attribute RIGHT_PAREN','spec_info',5,'p_spec_info','tla_parser.py',414),
  ('spec_info -> INIT','spec_info',1,'p_spec_info','tla_parser.py',415),
  ('theorem_definition -> THEOREM SPEC IMPLIES AND theorem_info AND theorem_info AND theorem_info AND theorem_info AND theorem_info','theorem_definition',13,'p_theorem_definition','tla_parser.py',428),
  ('theorem_info -> EventuallyTerminates','theorem_info',1,'p_theorem_info','tla_parser.py',433),
  ('theorem_info -> attribute','theorem_info',1,'p_theorem_info','tla_parser.py',434),
  ('theorem_info -> LoopInvariant','theorem_info',1,'p_theorem_info','tla_parser.py',435),
  ('theorem_info -> TerminationHypothesis','theorem_info',1,'p_theorem_info','tla_parser.py',436),
  ('expression -> LEFT_PAREN expression RIGHT_PAREN','expression',3,'p_expression_group','tla_parser.py',446),
]
