from os import truncate
import sys
from myLexerParserv2 import QUADSlist, TABLEof_functions
from myLexerParserv2 import CONSTANTSvar_set,SPECIALMETHODSlist
import statistics, matplotlib.pyplot as plt # SHORTCUTS FOR THE WIN


### READING MY QUADRUPLES
file = open("Quads.mir","r")
Quads = file.read()
Quads =  Quads.split("\n") # GIVE ME THE SEPARATED LINES
Quads = Quads[:-1] # GET RID OF THE LAST CHAR

##### STACK OF MEMORY HANDLERS, GLOBAL VARIABLES, MEMORY CLASS AND MISC #####
STACKofexecs = []
PROCList = []
PROCCOUNTER = 0
globalsensor = True

class Memory:
    def __init__(self):
        self.memor = {} ### A SET FOR OUR MEMORY####
