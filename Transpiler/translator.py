#Target output was translated to be in a similar formatting to Hao Wu's CoffeCan cyclone implementation

#This is our translator file from TLA to Cyclone. It takes the outputted AST from the tla_parser.py file
#and uses the visitor pattern algorithm to visit AST Nodes and perform the corresponding translation to cyclone.
#This pattern allows us to add new operations to the existing AST nodes without modifying the structures themselves. 
#the node being visited contains child nodes , the visit method is called recursively on each child.
# This ensures that the entire AST is traversed, and each node is translated that needs to be translated.


#import the AST from the tla_parser file
from tla_parser import result

#This is the main class of our translator file, this implements the visitor pattern to visit all the relevant ast nodes
#and recursively 
class CycloneTranslator:    #Visitor Pattern code developed with help from ChatGPT language model https://chat.openai.com/?model=text-davinci-002-render-sha
    def __init__(self):
        self.start_state_added = False   #our tracker to insert the start state in visit_FunctionDeclarationNode_1

    def visit(self, node):     #here is our created visitor pattern for the nodes 
        method_name = 'visit_' + type(node).__name__
        #here we are using a dynamic dispatch method to get the right method for a specific node
        visitor = getattr(self, method_name, self.generic_visit)
        return visitor(node)

    def generic_visit(self, node):   #a generic visitor pattern developed for nodes that don't have developed visit_ functions
        comment = f"  // Skipping irrelevant node: {type(node).__name__}"
        return comment
    
    #the translation process begins by calling the visit method on the root node of the AST, which is ModuleNode here
    def visit_ModuleNode(self, node):
        module_declaration = f"graph {node.name} {{"
        translated_statements = [self.visit(statement) for statement in node.statements]
        module_body = '\n'.join(translated_statements)  #we join all translated elements of the file seperated by a new line
        module_end = "}"
        translation = f"{module_declaration}\n{module_body}\n{module_end}"   #the structure of our finished cyclone file
        return translation

    def visit_SetDefinitionNode(self,node):
        record_name = node.attribute
        record_info = []   #temporary list to store the Cyclone code generated for a single field 

        for SetIndividualInfoNode in node.set_info:
            record_information = self.visit(SetIndividualInfoNode)  # Visit each field
            record_info.append(record_information)
        
        record_definition = f"    record {record_name}{{\n    " + "\n    ".join(record_info) + "\n    };"   #translate into this cyclone syntax using the attributes from the nodes
        return record_definition



    def visit_SetIndividualInfoNode(self,node):   #this node passes the info back to SetDefinitionNode as it is a nested node in the AST
        attribute_name = node.attribute
        scope_info = node.scope
        scope = scope_info.start_value

        info = f"    int {attribute_name} where {attribute_name} >= {scope};"
        return info

        
    #function to translate the first type of FunctionDeclarationNode
    def visit_FunctionDeclarationNode_1(self,node): 
       function_start  = f"    normal state {node.attribute} {{"         
       function_info_list = []
        
       if not self.start_state_added:      # this section is used to handle the insertion of our start state, this is necessary due to this visit function being called twice, which inserted two start states
            start_state_declaration = "    abstract start state Pick {}\n"
            self.start_state_added = True  # changes the boolean value to True when added
       else:
            start_state_declaration = ""

        # Check if there's an except_section to translate in the node
       if hasattr(node, 'except_section'):
            except_translation = self.visit(node.except_section) #nested node visitation code developed with help from ChatGPT language model https://chat.openai.com/?model=text-davinci-002-render-sha
            function_info_list += except_translation
      

       function_information = f"{start_state_declaration}\n\n{function_start}\n\n    " + "\n    ".join(function_info_list) + "\n    }"           
       return function_information
       



    def visit_FunctionDeclarationNode_2(self,node):
       function_start  = f"    normal state {node.attribute} {{"         
       function_info_list = []
        
        
        # Check if there's an except_section to translate
       if hasattr(node, 'except_section'):
            except_translation = self.visit(node.except_section)
            function_info_list += except_translation
      

       function_information = f"{function_start}\n\n    " + "\n    ".join(function_info_list) + "\n    }" + "\n\n    abstract final state T{}"            
      
       return function_information



    def visit_FunctionInfoNode(self,node):
        attribute_1 = node.attribute_1
        dot = node.dot
        attribute_2 = node.attribute_2

        info = f"{attribute_1}{dot}{attribute_2} "
        return info




     #passes the except clause and multiple except clause node values back up to FunctionDeclarationNode_1 and 2 respectively
    def visit_ExceptSectionNode(self,node):
        translation = self.visit(node.except_node)
        return translation




    
    #handles the translation of the nested ExceptClauseNode, this passed back up to FunctionDeclarationNode_1 and 2 via visit_ExceptSectionNode
    def visit_ExceptClauseNode(self, node):
    

        updates = []
        if node.attribute_2 == 'black':
            updates.append  (f"    Can.black{node.operator}{node.operator};") #inserting operator value from the node to complete the translation
        elif node.attribute_2 == 'white':
            updates.append(f"    Can.white{node.operator}{node.operator};")
       
        return updates




    #handles the translation of nodes with multiple except clause values 
    def visit_MultipleExceptClauseNode(self, node):
        updates = []
        
        if node.attribute_2 == 'black':
            updates.append(f"    Can.black{node.operator_1}{node.operator_1};\n" + "    "f"    Can.white{node.operator_2}={node.number_2};")
            
        return updates


    def visit_NextStateRelationNode(self, node):
        translations = []
        #we are checking for each individual next_state_info instance in NextStateRelationNode that is relevant for translation
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



    #handling the translation of each node in next_state_info values, this builds up a fulll translation of the section using the cyclone syntax below
    def visit_NextStateNode(self, node):
        translation = f"    trans {{ Pick -> {node.attribute} }}\n" + f"    trans {{ {node.attribute} ->  T where Can.white+Can.black==1;}}\n" + f"    trans {{ {node.attribute} -> Pick }}\n"
        return translation




    def visit_TerminationHypothesisNode(self,node):
        translations = []
        if hasattr(node, 'statement'):   #visiting each instance of 'statement' in TerminationHypothesisNode, this is a ConditionalStatementInfoNode
            translation = self.visit(node.statement)
            translations.append(translation)

        translation = "\n".join(translations)    #join the translated statements together seperated by a new line
        return translation #return to parent node ModuleNode


    #visitng each conditional statement instance seperately to build up a cyclone translation
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


        translation = "\n".join(translations)    #join the translated statements together seperated by a new line
        return translation    #passing the translated Conditional_IF_Node back up to TerminationHypothesisNode
    

    #visit the nested node AttributeDotAccessNode
    def visit_Conditional_IF_Node(self,node):
        translation = self.visit(node.dot_access)
        return translation #passing the translated AttributeDotAccessNode back up to ConditionalStatementInfoNode

    #use the AttributeDotAccessNode to complerte
    def visit_AttributeDotAccessNode(self,node):
        
        translation = f"      goal {{ \n        assert  !(((initial(Can.{node.attribute_after_dot}) % 2 == 0) => (Can.black == 1)) ||\n                " + f"((initial(Can.{node.attribute_after_dot}) % 2 != 0) =>  (Can.white==1)));\n\n" + "        check for 4" + "\n    }"
        return translation #pass translation back up to Conditional_IF_Node


translator = CycloneTranslator()    #creates an instance of our translator
cyclone_code = translator.visit(result)   #we call the visit method on our parsed AST from our parser, this uses the created Visitor Pattern to translate the AST
print(f"The translated Cyclone code has been saved to the file CoffeeCan.cyclone")

#Here we are saving our completed translated file to our designated filepath, which is CoffeeCan.cyclone in this case,
#you can change this file to your desired path for testing the output 
output_path = r"C:\Users\frand\OneDrive\Desktop\FYP\FYP_TLA_To_Cyclone_19450974\Transpiler\CoffeeCan.cyclone"
with open(output_path, 'w') as output_file:
    output_file.write(cyclone_code)
    








