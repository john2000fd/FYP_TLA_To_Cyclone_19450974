#Target output was translated to be in a similar formatting to Hao Wu's CoffeCan cyclone implementation

#This is our translator file from TLA to Cyclone. It takes the output from the tla_parser.py and uses the visit pattern to visit AST Nodes and perform corresponding translations  




from tla_parser import result


class CycloneTranslator: 
    def __init__(self):
        self.start_state_added = False   #our tracker to insert the start state in visit_FunctionDeclarationNode_1

    def visit(self, node):     #here is our visitor pattern for the nodes 
        method_name = 'visit_' + type(node).__name__
        visitor = getattr(self, method_name, self.generic_visit)
        return visitor(node)

    def generic_visit(self, node):
        comment = f"  // Skipping irrelevant node: {type(node).__name__}"
        return comment
    
    # Example visitor method for ModuleNode
    def visit_ModuleNode(self, node):
        module_declaration = f"graph {node.name} {{"
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
        
        record_definition = f"    record {record_name}{{\n    " + "\n    ".join(record_info) + "\n    };"
        return record_definition



    def visit_SetIndividualInfoNode(self,node):
        attribute_name = node.attribute
        scope_info = node.scope
        scope = scope_info.start_value

        info = f"    int {attribute_name} where {attribute_name} >= {scope};"
        return info

        

    def visit_FunctionDeclarationNode_1(self,node):
       function_start  = f"    normal state {node.attribute} {{"         
       function_info_list = []
        
       if not self.start_state_added:      # this section is used to handle the insertion of our start state, this is necessary due to this visit function being called twice, which inserted two start states
            start_state_declaration = "    abstract start state Pick {}\n"
            self.start_state_added = True  # changes the boolean to True when added
       else:
            start_state_declaration = ""

        # Check if there's an except_section to translate
       if hasattr(node, 'except_section'):
            except_translation = self.visit(node.except_section)
            function_info_list += except_translation
      

       function_information = f"{start_state_declaration}\n\n{function_start}\n\n    " + "\n    ".join(function_info_list) + "\n    }"           
       return function_information
       



    def visit_FunctionDeclarationNode_2(self,node):
       function_start  = f"    normal state {node.attribute} {{"         #abstract start state Start {{}}\n
       function_info_list = []
        
        
        # Check if there's an except_section to translate
       if hasattr(node, 'except_section'):
            except_translation = self.visit(node.except_section)
            function_info_list += except_translation
      

       function_information = f"{function_start}\n\n    " + "\n    ".join(function_info_list) + "\n    }" + "\n\n    abstract final state T{}"            #+ "\n abstract final state T{}"
       #function_information_altered = f"abstract start state Start {{}}\n" + function_information
       return function_information



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
            updates.append  (f"    Can.black{node.operator}{node.operator};")
        elif node.attribute_2 == 'white':
            updates.append(f"    Can.white{node.operator}{node.operator};")

        # Assuming there's logic to handle operator and number to translate the operation correctly
        # For example, "--" for decrement, "++" for increment, etc.

        # Compile the updates into a single translation string
        #translation = "\n".join(updates)
        return updates





    def visit_MultipleExceptClauseNode(self, node):
        # Handle multiple operations
        updates = []
        
        
        if node.attribute_2 == 'black':
            updates.append(f"    Can.black{node.operator_1}{node.operator_1};\n" + "    "f"    Can.white{node.operator_2}={node.number_2};")
            #updates.append(f"Can.white{node.operator_2}{node.number_2};")

       
        return updates


    def visit_NextStateRelationNode(self, node):
        translations = []
        #we are checking for each individual next_state_info instance that is relevant for translation
        if hasattr(node, 'next_state_info_1'):
            translation = self.visit(node.next_state_info_1)
            translations.append(translation)

        if hasattr(node, 'next_state_info_2'):
            translation = self.visit(node.next_state_info_2)
            translations.append(translation)

        if hasattr(node, 'next_state_info_3'):
            translation = self.visit(node.next_state_info_3)
            translations.append(translation)

        translation = "\n".join(translations)
        return translation



    
    def visit_NextStateNode(self, node):
        translation = f"    trans {{ Pick -> {node.attribute} }}\n" + f"    trans {{ {node.attribute} ->  T where Can.white+Can.black==1;}}\n" + f"    trans {{ {node.attribute} -> Pick }}\n"
        return translation




    def visit_TerminationHypothesisNode(self,node):
        translations = []
        if hasattr(node, 'statement'):
            translation = self.visit(node.statement)
            translations.append(translation)

        translation = "\n".join(translations)
        return translation



    def visit_ConditionalStatementInfoNode(self,node):
        translations = []
        if hasattr(node, 'conditional_statement_if'):
            translation = self.visit(node.conditional_statement_if)
            translations.append(translation)


        if hasattr(node, 'conditional_statement_then'):
            translation = self.visit(node.conditional_statement_then)
            translations.append(translation)


        if hasattr(node, 'conditional_statement_else'):
            translation = self.visit(node.conditional_statement_else)
            translations.append(translation)


        translation = "\n".join(translations)    
        return translation
    


    def visit_Conditional_IF_Node(self,node):
        translation = self.visit(node.dot_access)
        return translation


    def visit_AttributeDotAccessNode(self,node):
        
        translation = f"      goal {{ \n        assert  !(((initial(Can.{node.attribute_after_dot}) % 2 == 0) => (Can.black == 1)) ||\n                " + f"((initial(Can.{node.attribute_after_dot}) % 2 != 0) =>  (Can.white==1)));\n\n" + "        check for 4" + "\n    }"
        return translation


translator = CycloneTranslator()    #creates an instance of our translator
cyclone_code = translator.visit(result)   #we call the visit method on our parsed AST from our parser

#Here we are saving our completed translated file to our designated filepath, which is CoffeeCan.cyclone in this case, you can change this value to your desired path for testing the output 
output_path = r"C:\Users\frand\OneDrive\Desktop\FYP\FYP_TLA_To_Cyclone_19450974\Transpiler\CoffeeCan.cyclone"
with open(output_path, 'w') as output_file:
    output_file.write(cyclone_code)
    print(f"The translated Cyclone code has been saved to the file CoffeeCan.cyclone")









