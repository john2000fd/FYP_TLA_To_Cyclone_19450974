from tla_parser import result


#ast = parse_tla_to_ast(result)

class CycloneTranslator: 
    def visit(self, node):     #here is our visitor pattern for the nodes 
        method_name = 'visit_' + type(node).__name__
        visitor = getattr(self, method_name, self.generic_visit)
        return visitor(node)

    def generic_visit(self, node):
        comment = f"# Skipping irrelevant node: {type(node).__name__}"
        return comment
    
    # Example visitor method for ModuleNode
    def visit_ModuleNode(self, node):
        module_declaration = f"Graph {node.name} {{"
        translated_statements = [self.visit(statement) for statement in node.statements]
        module_body = '\n'.join(translated_statements)
        module_end = "}"
        translation = f"{module_declaration}\n{module_body}\n{module_end}"
        return translation

    def visit_SetDefinitionNode(self,node):
        record_name = node.attribute
        record_info = []   #temporary list to store the Cyclone code generated for a single field 

        for SetIndividualInfoNode in node.set_info:
            record_information = self.visit(SetIndividualInfoNode)  # Visit each field
            record_info.append(record_information)
        
        record_definition = f"record {record_name}{{\n\t" + "\n\t".join(record_info) + "\n };"
        return record_definition



    def visit_SetIndividualInfoNode(self,node):
        attribute_name = node.attribute
        scope_info = node.scope
        scope = scope_info.start_value

        info = f"int {attribute_name} where {attribute_name} >= {scope}"
        return info

        

    def visit_FunctionDeclarationNode_1(self,node):
       function_start  = f" normal state {node.attribute} {{"         #abstract start state Start {{}}\n
       function_info_list = []
        
        
        # Check if there's an except_section to translate
       if hasattr(node, 'except_section'):
            except_translation = self.visit(node.except_section)
            function_info_list += except_translation
      

       function_information = f"{function_start}\n\n\t" + "\n\t".join(function_info_list) + "\n}"            #+ "\n abstract final state T{}"
       function_information_altered = f"abstract start state Start {{}}\n" + function_information
       return function_information_altered
       


    def visit_FunctionInfoNode(self,node):
        attribute_1 = node.attribute_1
        dot = node.dot
        attribute_2 = node.attribute_2

        info = f"{attribute_1}{dot}{attribute_2} "
        return info




     #passes the except clause node back up to FunctionDeclarationNode_1
    def visit_ExceptSectionNode(self,node):
        translation = self.visit(node.except_node)
        return translation





    def visit_ExceptClauseNode(self, node):
    

        updates = []
        if node.attribute_2 == 'black':
            updates.append  (f"Can.black{node.operator}{node.number};")
        elif node.attribute_2 == 'white':
            updates.append(f"Can.white{node.operator}{node.number};")

        # Assuming there's logic to handle operator and number to translate the operation correctly
        # For example, "--" for decrement, "++" for increment, etc.

        # Compile the updates into a single translation string
        #translation = "\n".join(updates)
        return updates





    def visit_MultipleExceptClauseNode(self, node):
        # Handle multiple operations
        updates = []
        # Assuming you have a way to iterate over operations in MultipleExceptClauseNode
        # This is an example; adjust according to your actual data structure
        #operations = [(node.attribute_1, node.operator_1, node.number_1),
                    #(node.attribute_3, node.operator_2, node.number_2)]
        
        if node.attribute_2 == 'black':
            updates.append(f"Can.black{node.operator_1}{node.number_1};\n" + "\t"f"Can.white{node.operator_2}{node.number_2};")
            #updates.append(f"Can.white{node.operator_2}{node.number_2};")

       
        return updates



        
translator = CycloneTranslator()
cyclone_code = translator.visit(result)
print(cyclone_code)








def translate_state_var(ast_node):
    # Translate a state variable definition to Cyclone
    return f"state {ast_node.name} : {translate_type(ast_node.type)};"

def translate_init(ast_node):
    # Translate initialization logic to Cyclone
    # Assuming ast_node.value is the initial value for the variable
    return f"init {ast_node.name} = {ast_node.value};"

def translate_action(ast_node):
    # Translate an action (state transition) to Cyclone
    # This is highly simplified; actual logic depends on AST structure
    conditions = ' and '.join([f"{cond.var} {cond.op} {cond.value}" for cond in ast_node.conditions])
    updates = ', '.join([f"{upd.var} := {upd.value}" for upd in ast_node.updates])
    return f"transition {ast_node.name} when {conditions} do {updates};"

def translate_invariant(ast_node):
    # Translate an invariant (property) to Cyclone
    # Again, simplifying for illustration
    return f"invariant {ast_node.expression};"

def translate_type(tla_type):
    # Map TLA+ types to Cyclone types, if different
    # Placeholder for actual type mapping logic
    return tla_type








