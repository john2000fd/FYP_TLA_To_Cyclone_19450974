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
        scopeinfo = node.scope
        scope = scopeinfo.start_value

        info = f"int {attribute_name} where {attribute_name} >= {scope}"
        return info

        

    def visit_FunctionDeclarationNode_1(self,node):
       function_info = []

       for FunctionInfoNode in node.conditions:
            function_information = self.visit(FunctionInfoNode)
       
       
       function_declaration  = f"abstract start state Start {{}}\n normal state {node.attribute} {{" 













        
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








