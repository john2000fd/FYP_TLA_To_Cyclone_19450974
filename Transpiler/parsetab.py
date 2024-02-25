
# parsetab.py
# This file is automatically generated. Do not edit.
# pylint: disable=W,C,R
_tabversion = '3.10'

_lr_method = 'LALR'

_lr_signature = 'leftPLUSMINUSleftSTARDIVIDEnonassocLEFT_PARENRIGHT_PARENAND ARROW BACK_SLASH CHECK COLON COMMA CONSTANTS DIVIDE EDGE EQUALS EXTENDS FORWARD_SLASH GOAL GRAPH GREATER_THAN IDENTIFIER INIT INVARIANT LEFT_BRACE LEFT_PAREN LEFT_SQR_BRACKET LESS_THAN MINUS MODULE MODULE_NAME MODULE_WRAPPER MODULUS NEXT NODE NUMBER_LITERAL OR PLUS RIGHT_BRACE RIGHT_PAREN RIGHT_SQR_BRACKET SEMICOLON SINGLE_QUOTE SPEC STAR STRING_LITERAL UNDERSCORE VARIABLE VARIABLE_NAMEmodule : MODULE_WRAPPER MODULE IDENTIFIER MODULE_WRAPPER extends declarations\n              | MODULE_WRAPPER MODULE IDENTIFIER MODULE_WRAPPER declarationsextends : EXTENDS IDENTIFIER\n               | emptydeclarations : declarations declaration\n                    | declarationdeclaration : constants_declaration\n                   | variables_declaration\n                   | assignment_statementconstants_declaration : CONSTANTS IDENTIFIER_LISTvariables_declaration : VARIABLE IDENTIFIER_LISTgraph_declaration : GRAPH IDENTIFIER graph_bodygraph_body : graph_body graph_statement\n                  | graph_statementgraph_statement : node_declaration\n                       | edge_declarationnode_declaration : NODE IDENTIFIERedge_declaration : EDGE IDENTIFIER ARROW IDENTIFIERinvariant_declaration : INVARIANT expressionproperty_goal_declaration : GOAL expressionassignment_statement : IDENTIFIER EQUALS expressionexpression : expression PLUS expression\n                  | expression MINUS expression\n                  | expression STAR expression\n                  | expression DIVIDE expression\n                  | IDENTIFIER\n                  | NUMBER_LITERAL\n                  | STRING_LITERALexpression : LEFT_PAREN expression RIGHT_PARENIDENTIFIER_LIST : IDENTIFIER_LIST COMMA IDENTIFIER\n                       | IDENTIFIERinit_declaration : INIT EQUALS expressionempty :'
    
_lr_action_items = {'MODULE_WRAPPER':([0,4,],[2,5,]),'$end':([1,8,11,12,13,14,18,19,21,22,23,24,25,26,27,35,36,37,38,39,40,],[0,-2,-6,-7,-8,-9,-1,-5,-10,-31,-11,-26,-21,-27,-28,-30,-22,-23,-24,-25,-29,]),'MODULE':([2,],[3,]),'IDENTIFIER':([3,5,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,35,36,37,38,39,40,],[4,6,6,6,20,-4,-6,-7,-8,-9,22,22,24,6,-5,-3,-10,-31,-11,-26,-21,-27,-28,24,35,24,24,24,24,-30,-22,-23,-24,-25,-29,]),'EXTENDS':([5,],[9,]),'CONSTANTS':([5,7,8,10,11,12,13,14,18,19,20,21,22,23,24,25,26,27,35,36,37,38,39,40,],[15,15,15,-4,-6,-7,-8,-9,15,-5,-3,-10,-31,-11,-26,-21,-27,-28,-30,-22,-23,-24,-25,-29,]),'VARIABLE':([5,7,8,10,11,12,13,14,18,19,20,21,22,23,24,25,26,27,35,36,37,38,39,40,],[16,16,16,-4,-6,-7,-8,-9,16,-5,-3,-10,-31,-11,-26,-21,-27,-28,-30,-22,-23,-24,-25,-29,]),'EQUALS':([6,],[17,]),'NUMBER_LITERAL':([17,28,30,31,32,33,],[26,26,26,26,26,26,]),'STRING_LITERAL':([17,28,30,31,32,33,],[27,27,27,27,27,27,]),'LEFT_PAREN':([17,28,30,31,32,33,],[28,28,28,28,28,28,]),'COMMA':([21,22,23,35,],[29,-31,29,-30,]),'PLUS':([24,25,26,27,34,36,37,38,39,40,],[-26,30,-27,-28,30,-22,-23,-24,-25,-29,]),'MINUS':([24,25,26,27,34,36,37,38,39,40,],[-26,31,-27,-28,31,-22,-23,-24,-25,-29,]),'STAR':([24,25,26,27,34,36,37,38,39,40,],[-26,32,-27,-28,32,32,32,-24,-25,-29,]),'DIVIDE':([24,25,26,27,34,36,37,38,39,40,],[-26,33,-27,-28,33,33,33,-24,-25,-29,]),'RIGHT_PAREN':([24,26,27,34,36,37,38,39,40,],[-26,-27,-28,40,-22,-23,-24,-25,-29,]),}

_lr_action = {}
for _k, _v in _lr_action_items.items():
   for _x,_y in zip(_v[0],_v[1]):
      if not _x in _lr_action:  _lr_action[_x] = {}
      _lr_action[_x][_k] = _y
del _lr_action_items

_lr_goto_items = {'module':([0,],[1,]),'extends':([5,],[7,]),'declarations':([5,7,],[8,18,]),'empty':([5,],[10,]),'declaration':([5,7,8,18,],[11,11,19,19,]),'constants_declaration':([5,7,8,18,],[12,12,12,12,]),'variables_declaration':([5,7,8,18,],[13,13,13,13,]),'assignment_statement':([5,7,8,18,],[14,14,14,14,]),'IDENTIFIER_LIST':([15,16,],[21,23,]),'expression':([17,28,30,31,32,33,],[25,34,36,37,38,39,]),}

_lr_goto = {}
for _k, _v in _lr_goto_items.items():
   for _x, _y in zip(_v[0], _v[1]):
       if not _x in _lr_goto: _lr_goto[_x] = {}
       _lr_goto[_x][_k] = _y
del _lr_goto_items
_lr_productions = [
  ("S' -> module","S'",1,None,None,None),
  ('module -> MODULE_WRAPPER MODULE IDENTIFIER MODULE_WRAPPER extends declarations','module',6,'p_module','parser.py',134),
  ('module -> MODULE_WRAPPER MODULE IDENTIFIER MODULE_WRAPPER declarations','module',5,'p_module','parser.py',135),
  ('extends -> EXTENDS IDENTIFIER','extends',2,'p_extends','parser.py',143),
  ('extends -> empty','extends',1,'p_extends','parser.py',144),
  ('declarations -> declarations declaration','declarations',2,'p_declarations','parser.py',151),
  ('declarations -> declaration','declarations',1,'p_declarations','parser.py',152),
  ('declaration -> constants_declaration','declaration',1,'p_declaration','parser.py',161),
  ('declaration -> variables_declaration','declaration',1,'p_declaration','parser.py',162),
  ('declaration -> assignment_statement','declaration',1,'p_declaration','parser.py',163),
  ('constants_declaration -> CONSTANTS IDENTIFIER_LIST','constants_declaration',2,'p_constants_declaration','parser.py',167),
  ('variables_declaration -> VARIABLE IDENTIFIER_LIST','variables_declaration',2,'p_variables_declaration','parser.py',172),
  ('graph_declaration -> GRAPH IDENTIFIER graph_body','graph_declaration',3,'p_graph_declaration','parser.py',178),
  ('graph_body -> graph_body graph_statement','graph_body',2,'p_graph_body','parser.py',183),
  ('graph_body -> graph_statement','graph_body',1,'p_graph_body','parser.py',184),
  ('graph_statement -> node_declaration','graph_statement',1,'p_graph_statement','parser.py',193),
  ('graph_statement -> edge_declaration','graph_statement',1,'p_graph_statement','parser.py',194),
  ('node_declaration -> NODE IDENTIFIER','node_declaration',2,'p_node_declaration','parser.py',199),
  ('edge_declaration -> EDGE IDENTIFIER ARROW IDENTIFIER','edge_declaration',4,'p_edge_declaration','parser.py',204),
  ('invariant_declaration -> INVARIANT expression','invariant_declaration',2,'p_invariant_declaration','parser.py',209),
  ('property_goal_declaration -> GOAL expression','property_goal_declaration',2,'p_property_goal_declaration','parser.py',214),
  ('assignment_statement -> IDENTIFIER EQUALS expression','assignment_statement',3,'p_assignment_statement','parser.py',219),
  ('expression -> expression PLUS expression','expression',3,'p_expression','parser.py',224),
  ('expression -> expression MINUS expression','expression',3,'p_expression','parser.py',225),
  ('expression -> expression STAR expression','expression',3,'p_expression','parser.py',226),
  ('expression -> expression DIVIDE expression','expression',3,'p_expression','parser.py',227),
  ('expression -> IDENTIFIER','expression',1,'p_expression','parser.py',228),
  ('expression -> NUMBER_LITERAL','expression',1,'p_expression','parser.py',229),
  ('expression -> STRING_LITERAL','expression',1,'p_expression','parser.py',230),
  ('expression -> LEFT_PAREN expression RIGHT_PAREN','expression',3,'p_expression_group','parser.py',245),
  ('IDENTIFIER_LIST -> IDENTIFIER_LIST COMMA IDENTIFIER','IDENTIFIER_LIST',3,'p_identifier_list','parser.py',252),
  ('IDENTIFIER_LIST -> IDENTIFIER','IDENTIFIER_LIST',1,'p_identifier_list','parser.py',253),
  ('init_declaration -> INIT EQUALS expression','init_declaration',3,'p_init_declaration','parser.py',262),
  ('empty -> <empty>','empty',0,'p_empty','parser.py',268),
]
