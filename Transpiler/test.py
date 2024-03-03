import ply.yacc as yacc
from tokenizer import tokens

# Import your lexer and parser modules here
# from your_parser_module import tokens, parser  # Adjust this import statement as per your module structure

# Your TLA+ code as a string
tla_code = """
---------------------------- MODULE TestModule ----------------------------
EXTENDS Integers

CONSTANTS MaxBeanCount
VARIABLES can

Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

Init == can \in Can

Next == \E can' \in Can : can' /= can

=============================================================================
"""

# Assuming your parser object is named `parser` and it's accessible here
# If your parser is defined in a separate module, ensure to import it correctly
parser = yacc.yacc()  # You might already have this instantiation somewhere in your parser definition

# Parse the TLA+ code
result = parser.parse(tla_code)

# Print or inspect the result
print(result)