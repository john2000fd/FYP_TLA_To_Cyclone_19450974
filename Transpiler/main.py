#Transpiler program proposed to convert a TLA specification to an equivalent Cyclone file.
#J. Dunne
#Last edit: 28.03.24

#Final Year Project FYP24WH002 TLA To Cyclone by John Dunne 19450974
#This is the main hub file of the developed demonstration TLA to Cyclone transpiler
#Here we are taking in a TLA file, passing it into various systems such as a lexer, parser and translator, then saving the resulting tranbslation to a file

#Repository located here -> https://github.com/john2000fd/FYP_TLA_To_Cyclone_19450974




import tokenizer        #Importing the necessary modules
import tla_parser
import translator
import time

# Here we are reading in our TLA code, this is taken from the TLA demonstration repository on GitHub. https://github.com/tlaplus/Examples/tree/master
#This details the Coffee Can algorithim:
#A coffee can contains some black beans and white beans. The following   *)
#(* process is to be repeated as long as possible:             
#(* throw them out, but put another black bean in. (Enough extra black      *)
#(* beans are available to do this.) If they are different colors, place    *)
#(* the white one back into the can and throw the black one away.           *)
##                                                                         *)
#(* Execution of this process reduces the number of beans in the can by     *)
#(* one. Repetition of this process must terminate with exactly one bean in *)
#(* the can, for then two beans cannot be selected. The question is: what,  *)
#(* if anything, can be said about the color of the final bean based on the *)
#(* number of white beans and the number of black beans initially in the can   *)

tla_code = """                           
---------------------------- MODULE CoffeeCan ----------------------------       


EXTENDS Naturals

CONSTANTS MaxBeanCount

ASSUME MaxBeanCount \in Nat /\ MaxBeanCount >= 1

VARIABLES can

\* The set of all possible cans
Can == [black : 0..MaxBeanCount, white : 0..MaxBeanCount]

\* Possible values the can variable can take on
TypeInvariant == can \in Can

\* Initialize can so it contains between 1 and MaxBeanCount beans
Init == can \in {c \in Can : c.black + c.white \in 1..MaxBeanCount}

\* Number of beans currently in the can
BeanCount == can.black + can.white

\* Pick two black beans; throw both away, put one black bean in
PickSameColorBlack ==
    /\ BeanCount > 1
    /\ can.black >= 2
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Pick two white beans; throw both away, put one black bean in
PickSameColorWhite ==
    /\ BeanCount > 1
    /\ can.white >= 2
    /\ can' = [can EXCEPT !.black = @ + 1, !.white = @ - 2]

\* Pick one bean of each color; put white back, throw away black
PickDifferentColor ==
    /\ BeanCount > 1
    /\ can.black >= 1
    /\ can.white >= 1
    /\ can' = [can EXCEPT !.black = @ - 1]

\* Termination action to avoid triggering deadlock detection
Termination ==
    /\ BeanCount = 1
    /\ UNCHANGED can

\* Next-state relation: what actions can be taken
Next ==
    \/ PickSameColorWhite
    \/ PickSameColorBlack
    \/ PickDifferentColor
    \/ Termination

\* Action formula: every step decreases the number of beans in the can
MonotonicDecrease == [][BeanCount' < BeanCount]_can

\* Liveness property: we eventually end up with one bean left
EventuallyTerminates == <>(ENABLED Termination)

\* Loop invariant: every step preserves white bean count mod 2
LoopInvariant == [][can.white % 2 = 0 <=> can'.white % 2 = 0]_can

\* Hypothesis: If we start out with an even number of white beans, we end up
\* with a single black bean. Otherwise, we end up with a single white bean.
TerminationHypothesis ==
    IF can.white % 2 = 0
    THEN <>(can.black = 1 /\ can.white = 0)
    ELSE <>(can.black = 0 /\ can.white = 1)

\* Start out in a state defined by the Init operator and every step is one
\* defined by the Next operator. Assume weak fairness so the system can't
\* stutter indefinitely: we eventually take some beans out of the can.
Spec ==
    /\ Init
    /\ [][Next]_can
    /\ WF_can(Next)

\* What we want to show: that if our system follows the rules set out by the
\* Spec operator, then all our properties and assumptions will be satisfied.
THEOREM Spec =>
    /\ TypeInvariant
    /\ MonotonicDecrease
    /\ EventuallyTerminates
    /\ LoopInvariant
    /\ TerminationHypothesis

=============================================================================
"""


def main(tla_code):
    #Here we are calling the lexer method in our tokenizer.py file, this returns the stream of tokens and stores it in the lexer_tokens variable
    lexer_tokens = tokenizer.tokenizer.input(tla_code)
    
    start_of_runtime = time.time()   #uses time module to get the time currently, this is saved as our start time


    result = tla_parser.parser.parse(lexer_tokens)   #pass our stream of lexer tokens into the parser method in tla_parser.py, store generated AST in result variable
    print(result)

    cyclone_code = translator.translator.visit(result)   #pass our AST into the translator method in translator.py, this returns the translated Cyclone code, stored in cyclone_code
    print(cyclone_code)
    print()
    print(f"The translated Cyclone code has been saved to the file CoffeeCan.cyclone")
    
    
    end_time = time.time()   #gets the time when the program finishes

    runtime = end_time - start_of_runtime   #calculates the difference between the end and start time to get our program duration
    print()
    print(f"Program runtime: {runtime} seconds")   #print runtime


if __name__ == "__main__":
    main(tla_code)