from os import truncate
import sys
from MyLexerParser import QUADRUPLESlist, THETABLEoffunctions
from MyLexerParser import THECONSTANTSset,SPECIALMETHODSlist
import statistics, matplotlib.pyplot as plt # SHORTCUTS FOR THE WIN

#### MY QUADS SHORTCUT OPERATORS GUIDE
###HASHOFOPERATORSINquads = {
###    '+' : 1,
###    '-' : 2,
###    '*' : 3,
###    '/' : 4,
###    '>' : 5,
###    '>= : 6,
###    '<' : 7,
###    '<=' : 8,
###    '==' : 9,
###    '<>' : 10,
###    '=' : 11,
###    'READ' : 12,
###    'WRITE' : 13,
###    'and' : 14,
###    'OR' : 15,
###    'GOTO' : 16,
###    'GOTOF' : 17,
###    'GOTOV' : 18,
###    'ERA' : 19,
###    'VER' : 20,
###    'ENDPROC' : 21,
###    'PARAM' : 22,
###    'GOSUB' : 23,
###   'MEDIA' : 24,
###   'MEDIANA' : 25,
###    'MODA' : 26,
###    'STDEV' : 27,
###    'VARIANZA' : 28,
###    'PLOTXY' : 29,
###   'RETURN' : 30,
###    '' : -1
###}

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

#UNIVERSAL METHODS FOR THE VM ###############
# ERROR HANDLER
def ERROR(type,location = ""):
    print("ERROR: ", type , " at ===>", location)
    sys.exit()

# GET THE CONSTANT VALUE
def gettheCTE(value):
    global THECONSTANTSset
    for key, value2 in THECONSTANTSset.items():
        if value == value2: ### IF FOUND IN THE CONSTANT TABLE
            return key

def nonesensor(value,quadruple): ## CHECKING IF A QUADRUPLE OPERATION HAS A NONE VALUE
    global globalsensor
    if value is None:
        ERROR("NONE IN HERE", quadruple)

def isReadable(Varia, value):# CHECK IF IT CAN BE READ AS VARIABLE
    global globalsensor
    if globalsensor:
        if Varia < 3000 and Varia >= 1000:
            try:
                value = int(value)
            except:
                ERROR("TYPE MISMATCH", value)
        elif Varia < 5000 and Varia >= 3000:
            try:
                value = float(value)
            except: 
                ERROR("TYPE MISMATCH", value)
        elif Varia < 7000 and Varia >= 5000:
            if len(value) > 1:
                ERROR("NOT A CHAR", value)
            value = str(value)
        else:
            ERROR("TYPE MISMATCH", value)

def loadvirtualmemory(processname): # LOAD THE MEMORY WE ARE WORKING WITH
    for element in THETABLEoffunctions[processname]['variables']:
        virtualaddr = THETABLEoffunctions[processname]['variables'][element]['virtualaddress'] # GET THE VIRTUAL ADDRESS
        actualmemory.memor[virtualaddr] = None # LIBERATE

def vectorsensor(value): # FAST ARRAY SENSOR FOR THE ADDRESS
    return value >= 30000


def fromVector(indexz): # HANDLE THE VECTORS WITH THE DOUBLE INDEXING
    global globalsensor
    if globalsensor:
        try: 
            return int(GLOBALmemory.memor[indexz])
        except:
            print("The index ==> ",indexz)
            print(GLOBALmemory.memor)
            return indexz
    else:
        try:
            return actualmemory.memor[indexz]
        except:
            print("The index ==> ", indexz)
            print(actualmemory.memor)
            return indexz

def localsensor(value): # AS DEFINED
    try:
        actualmemory.memor[value]
        return True
    except:
        return False

def globalsensor2(value): # AS DEFINED
    try:
        GLOBALmemory.memor[value]
        return True
    except:
        ERROR("NO EXISTENCE FOR THIS VALUE ", str(value))

def changecontextlocalsensor(value): # HANDLE IF IT WAS THE LAST LOCAL VARIABLE BEFORE A CONTEXT CHANGE
    global STACKofexecs
    try:
        STACKofexecs[-1].memor[value]
        return True
    except:
        return False

for x in THETABLEoffunctions.keys(): # GET THE THE NAME OF THE FUNCTION PROGRAM
    if THETABLEoffunctions[x]['context'] == 'g':
        actualprogramname = x

######## MEMORY INITIALIZERS ########
GLOBALmemory = Memory()
actualmemory = None

for element in THETABLEoffunctions[actualprogramname]['variables']: # LOAD THE GLOBAL MEMORY
    virtualaddr = THETABLEoffunctions[actualprogramname]['variables'][element]['virtualaddress']
    GLOBALmemory.memor[virtualaddr] = None

for element2 in THECONSTANTSset: # LOAD THE CONSTANT TO THE MEMORY
    virtualaddr = THECONSTANTSset[element2]
    if virtualaddr < 23000:
        GLOBALmemory.memor[virtualaddr]=int(element2)
    elif virtualaddr < 25000:
        GLOBALmemory.memor[virtualaddr]=float(element2)
    elif virtualaddr < 27000:
        GLOBALmemory.memor[virtualaddr]=str(element2)

###DEBUGGIN GOES HERE ##########
#print("\n", THETABLEoffunctions) LOOK WHAT WE ARE WORKING WITH HERE
#print("\n", THECONSTANTSset)

#### THE GREAT CYCLE OF PROCESSING THE QUADRUPLES READED######
while PROCCOUNTER <= len(Quads):
    # DEFRAG THE READ FILE INTO ELEMENTS
    (indexz,operat,leftoperd,rightoperd,result) = Quads[PROCCOUNTER].split("~")
    #DEBUG
    #print(PROCCOUNTER+1, "<=== QUADRUPLE WE ARE GOING TO WORK WITH")
    # GOTO
    if int(operat) == 16:
        PROCCOUNTER = int(result) - 2 # LOAD THE JUMP, ADJUSTING WITH THE OFFSET
    # EQUAL = 
    elif int(operat) == 11:
        if vectorsensor(int(result)): # LOAD THE ACTUAL ARRAY VALUE
            result = fromVector(int(result))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],int(leftoperd)) # DONT GET NONES
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] # ASSIGN THE VAL
        else:
            try:
                nonesensor(actualmemory.memor[int(leftoperd)],int(leftoperd)) # DONT GET NONES
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] # ASSIGN THE VAL
            except:
                nonesensor(GLOBALmemory.memor[int(leftoperd)],int(leftoperd)) # DONT GET NONES
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] # ASSIGN THE VAL, ACCOUNTING FOR CHANGE CONTEXT
    # SUM +
    elif int(operat) == 1:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],1)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],1)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] + GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] + actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] + GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] + actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] + GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE SUM QUADS")
    # TIMES *
    elif int(operat) == 3:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],3)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],3)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] * GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] * actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] * GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] * actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] * GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE TIMES QUADS")
    # REST -
    elif int(operat) == 2:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],2)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],2)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] - GLOBALmemory.memor[int(rightoperd)]
        else:
            if len(STACKofexecs) > 0:
                if changecontextlocalsensor(int(leftoperd)) and changecontextlocalsensor(int(rightoperd)):
                    STACKofexecs[-1].memor[int(result)] = STACKofexecs[-1].memor[int(leftoperd)] - STACKofexecs[-1].memor[int(rightoperd)]
                elif changecontextlocalsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                    STACKofexecs[-1].memor[int(result)] = STACKofexecs[-1].memor[int(leftoperd)] - GLOBALmemory.memor[int(rightoperd)]
                elif globalsensor2(int(leftoperd)) and changecontextlocalsensor(int(rightoperd)):
                    STACKofexecs[-1].memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] - STACKofexecs[-1].memor[int(rightoperd)]
                elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                    STACKofexecs[-1].memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] - GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
                else:
                    ERROR("TRYING NONES IN THE REST QUADS")
            else:
                if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                    actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] - actualmemory.memor[int(rightoperd)]
                elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                    actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] - GLOBALmemory.memor[int(rightoperd)]
                elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                    actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] - actualmemory.memor[int(rightoperd)]
                elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                    actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] - GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
                else:
                    ERROR("TRYING NONES IN THE REST QUADS")
    #DIVIDE /
    elif int(operat) == 4:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],4)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],4)
            if type(GLOBALmemory.memor[int(leftoperd)]) == int and type(GLOBALmemory.memor[int(leftoperd)]) == int:
                GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] // GLOBALmemory.memor[int(rightoperd)] # FLOOR DIVISION
            else:
                GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] / GLOBALmemory.memor[int(rightoperd)] # NORMAL DIVISION
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                if type(actualmemory.memor[int(leftoperd)]) == int and type(actualmemory.memor[int(rightoperd)]) == int:
                    actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] // actualmemory.memor[int(rightoperd)]
                else:
                    actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] / actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                if type(actualmemory.memor[int(leftoperd)]) == int and type(GLOBALmemory.memor[int(rightoperd)]) == int:
                    actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] // GLOBALmemory.memor[int(rightoperd)]
                else:
                    actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] / GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                if type(GLOBALmemory.memor[int(leftoperd)]) == int and type(actualmemory.memor[int(rightoperd)]) == int:
                    actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] // actualmemory.memor[int(rightoperd)]
                else:
                    actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] / actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                if type(GLOBALmemory.memor[int(leftoperd)]) == int and type(GLOBALmemory.memor[int(rightoperd)]) == int:
                    actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] // GLOBALmemory.memor[int(rightoperd)]
                else:
                    actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] / GLOBALmemory.memor[int(rightoperd)]
            else:
                ERROR("TRYING NONES IN THE DIVIDE QUADS")
    # WRITE 
    elif int(operat) == 13:
        if result[0] == '"':
            print(result[1:-1]) # PRINT THE ENTIRE COMMENT IN ONE GO
        elif globalsensor:
            if vectorsensor(int(result)): # IF IN VECTOR< GET THE ELEMENT
                result = fromVector(int(result))
            print(GLOBALmemory.memor[int(result)])
        else:
            if vectorsensor(int(result)):
                result = fromVector(int(result))
            try:
                print(actualmemory.memor[int(result)])
            except:
                print(GLOBALmemory.memor[int(result)])
    # GREATER
    elif int(operat) == 5:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],5)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],5)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] > GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] > actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] > GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] > actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] > GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE > QUADS")
    #GOTOF
    elif int(operat) == 17:
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],17)
            if not GLOBALmemory.memor[int(leftoperd)]:
                PROCCOUNTER=int(result)- 2 # DO THE JUMP, ONLY IN THE CONDITION IS FALSE
        else:
            if localsensor(int(leftoperd)):
                nonesensor(actualmemory.memor[int(leftoperd)],17)
                if not actualmemory.memor[int(leftoperd)]:
                    PROCCOUNTER=int(result)- 2 # DO THE JUMP, ONLY IN THE CONDITION IS FALSE
            elif globalsensor2(int(leftoperd)):
                nonesensor(GLOBALmemory.memor[int(leftoperd)],17)
                if not GLOBALmemory.memor[int(leftoperd)]:
                    PROCCOUNTER=int(result)- 2 # DO THE JUMP, ONLY IN THE CONDITION IS FALSE
    #SAME ==
    elif int(operat) == 9:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)], 9)
            nonesensor(GLOBALmemory.memor[int(rightoperd)], 9)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] == GLOBALmemory.memor[int(rightoperd)]  
        else:
            if vectorsensor(int(leftoperd)):
                leftoperd = fromVector(int(leftoperd))
            if vectorsensor(int(rightoperd)):
                dirleftoperd2 = fromVector(int(leftoperd))
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] == actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] == GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] == actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] == GLOBALmemory.memor[int(rightoperd)]
            else:
                ERROR("TRYING NONES IN THE == QUADS")
    #LESSER <
    elif int (operat)==7:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],7)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],7)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] < GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] < actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] < GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] < actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] < GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE < QUADS")
    #LESSERAND <=
    elif int (operat)==8:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],7)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],7)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] <= GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] <= actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] <= GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] <= actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] <= GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE <= QUADS")
    #GREATER AND >=
    elif int(operat)==6:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],7)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],7)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] >= GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] >= actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] >= GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] >= actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] >= GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE >= QUADS")
    #NOTSAME <>
    elif int(operat)==10:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],10)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],10)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] != GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] != actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] != GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] != actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] != GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE <> QUADS")
    #GOTOV
    elif int(operat) == 18:
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],18)
            if GLOBALmemory.memor[int(leftoperd)]:
                PROCCOUNTER=int(result)- 2 # DO THE JUMP, ONLY IN THE CONDITION IS TRUE
        else:
            if localsensor(int(leftoperd)):
                nonesensor(actualmemory.memor[int(leftoperd)],18)
                if actualmemory.memor[int(leftoperd)]:
                    PROCCOUNTER=int(result)- 2 # DO THE JUMP, ONLY IN THE CONDITION IS TRUE
            elif globalsensor2(int(leftoperd)):
                nonesensor(GLOBALmemory.memor[int(leftoperd)],18)
                if GLOBALmemory.memor[int(leftoperd)]:
                    PROCCOUNTER=int(result)- 2 # DO THE JUMP, ONLY IN THE CONDITION IS TRUE
    #READ 
    elif int(operat)==12:
        if vectorsensor(int(result)):
            result = fromVector(int(result))
        if globalsensor:
            value = input() # READ FROM THE USER
            isReadable(int(result),value)
            GLOBALmemory.memor[int(result)] = value # SAVE IT IN MEMORY
        else:
            value = input() # READ FROM THE USER
            isReadable(int(result),value)
            if localsensor(int(result)):
                actualmemory.memor[int(result)] = value
            elif globalsensor2(int(result)):
                GLOBALmemory.memor[int(result)] = value # SAVE IT IN MEMORY
    #AND
    elif int(operat)==14:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],14)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],14)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] and GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] and actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] and GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] and actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] and GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE AND QUADS")
    #OR
    elif int(operat)==15:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            nonesensor(GLOBALmemory.memor[int(leftoperd)],15)
            nonesensor(GLOBALmemory.memor[int(rightoperd)],15)
            GLOBALmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] or GLOBALmemory.memor[int(rightoperd)]
        else:
            if localsensor(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] or actualmemory.memor[int(rightoperd)]
            elif localsensor(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = actualmemory.memor[int(leftoperd)] or GLOBALmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and localsensor(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] or actualmemory.memor[int(rightoperd)]
            elif globalsensor2(int(leftoperd)) and globalsensor2(int(rightoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)] or GLOBALmemory.memor[int(rightoperd)] # ACCOUNT FOR CONTEXT CHANGES
            else:
                ERROR("TRYING NONES IN THE OR QUADS")
    #ENDPROC
    elif int(operat) == 21:
        if STACKofexecs:
            actualmemory=STACKofexecs.pop() # POP THE STACK OF EXECUTIONS
        else:
            globalsensor = True # CHANGE THE CONTEZT
        PROCCOUNTER = PROCList.pop()
    #ERA
    elif int(operat)== 19:
        if actualmemory is not None: # IS IT NOT EMPTY?
            STACKofexecs.append(actualmemory)
            actualmemory = Memory()
            loadvirtualmemory(result) # START THE FUNCTION NAME
        else:
            actualmemory = Memory()
            loadvirtualmemory(result)
    #GOSUB
    elif int(operat)==23:
        globalsensor=False # WE ARE IN FUNCS 
        PROCList.append(PROCCOUNTER+1) # GET ME THE FUCNTION QUADS
        PROCCOUNTER = int(result)-2 # JUMP TO THE FUNC, 
    #RETURN
    elif int(operat)==30:
        if vectorsensor(int(leftoperd)):
            leftoperd=fromVector(int(leftoperd))
        if localsensor(int(leftoperd)):
            GLOBALmemory.memor[int(result)]= actualmemory.memor[int(leftoperd)]
        elif globalsensor2(int(leftoperd)):
            GLOBALmemory.memor[int(result)]= GLOBALmemory.memor[int(leftoperd)]
        if not STACKofexecs:
            globalsensor = True
        else:
            actualmemory=STACKofexecs.pop()
        PROCCOUNTER = PROCList.pop()-1 # JUMP TO THE ACTUAL ADDRESS
    #PARAMS
    elif int(operat)==22:
        if vectorsensor(int(leftoperd)):
            leftoperd = fromVector(int(leftoperd))
        if vectorsensor(int(rightoperd)):
            rightoperd = fromVector(int(rightoperd))
        if globalsensor:
            actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)]
        else:
            if changecontextlocalsensor(int(leftoperd)):
                actualmemory.memor[int(result)] = STACKofexecs[-1].memor[int(leftoperd)]
            elif globalsensor2(int(leftoperd)):
                actualmemory.memor[int(result)] = GLOBALmemory.memor[int(leftoperd)]
    #VER
    elif int(operat)==20:
        if globalsensor:
            if GLOBALmemory.memor[int(leftoperd)]>= GLOBALmemory.memor[int(result)] or GLOBALmemory.memor[int(leftoperd)] < 0:
                ERROR ("VECTOR INDEX OUT OF BOUNDS ",leftoperd)
        else:
            if localsensor(int(leftoperd)):
                if actualmemory.memor[int(leftoperd)]>= GLOBALmemory.memor[int(result)] or GLOBALmemory.memor[int(rightoperd)] < 0:
                    ERROR ("VECTOR INDEX OUT OF BOUNDS ",leftoperd)
            elif globalsensor2(int(leftoperd)):
                if GLOBALmemory.memor[int(leftoperd)]>= GLOBALmemory.memor(int(result)) or GLOBALmemory.memor[int(rightoperd)]< 0:
                    ERROR ("VECTOR INDEX OUT OF BOUNDS ",leftoperd)
    #SPECIAL FUNCTIONS
    #MEDIA
    elif int(operat)==24:
        print (statistics.mean(SPECIALMETHODSlist[int(result)]))
    #MEDIAN
    elif int(operat)==25:
        print (statistics.median(SPECIALMETHODSlist[int(result)]))
    #MODA
    elif int(operat)==26:
        print (statistics.mode(SPECIALMETHODSlist[int(result)]))
    #STDEV
    elif int(operat)==27:
        print (statistics.stdev(SPECIALMETHODSlist[int(result)]))
    #Varianza
    elif int(operat)==28:
        print (statistics.variance(SPECIALMETHODSlist[int(result)]))
    #PLOTXT
    elif int(operat)==29:
        # python3 -m pip install matplotlib
        # pip uninstall matplotlib
        plt.plot(SPECIALMETHODSlist[int(result)])
        plt.show()
    
    #GO TO NEXT QUADRUPLE
    PROCCOUNTER+=1
    if(PROCCOUNTER==len(Quads)): # EXIT THE VM
        sys.exit()