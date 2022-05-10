import sys
import re
import os
import subprocess
import time
import timeit
import signal
from itertools import chain, combinations

#print(sys.path[0])

def powerset(iterable):
    s = list(iterable)
    return chain.from_iterable(combinations(s, r) for r in range(len(s)+1))

def readAspartix(filePath) :

    file = open(filePath, "r")
    #print(file.readlines())

    lignes = file.readlines()

    argDic = {}

    state = 0
    argCount = 0
    for ligne in lignes :
        if ligne == "\n" :
            state += 1
        else :
            if state == 0 :
                argCount += 1
                """ print(ligne)
                print(re.split('\(|\)', ligne)) """
                argDic[re.split('\(|\)', ligne)[1]] = [0, [], [], "x" + str(argCount)]
            if state == 1 :
                """ print(ligne)
                print(re.split('\(|\)|,', ligne)) """
                splitLine = re.split('\(|\)|,', ligne)
                argDic[splitLine[1]][1].append(splitLine[2])
                argDic[splitLine[2]][2].append(splitLine[1])
            if state == 2 :
                """ print(ligne)
                print(re.split('\(|\)|,', ligne)) """
                splitLine = re.split('\(|\)|,', ligne)
                argDic[splitLine[1]][0] = int(splitLine[2])
    for key in argDic.keys() :
        argDic[key].append("x" + str(int(argDic[key][3][1:])+len(argDic.keys())))
    #print(argDic)

    file.close()
    return argDic


def writeStrongCF(argDic, file) :
    unused = []
    constraintCount = 0
    file.write("* Strong Conflict Free\n")
    for key in argDic.keys() :
        if len(argDic[key][1]) > 0 :
            for arg in argDic[key][1] :
                file.write("-1 " + argDic[key][3] + " -1 " + argDic[arg][3] + " >= -1 ;" + "\n")
                constraintCount += 1
        else :
            unused.append(key)
    for arg in unused :
        file.write("+1 " + argDic[arg][3] + " +1 ~" + argDic[arg][3] + " >= 1 ;\n")
        constraintCount += 1
    return constraintCount


def writeWeakCF(argDic, file) :
    constraintCount = 0
    file.write("* Weak Conflict Free\n")

    for key in argDic.keys() :
        constraint = ""
        if len(argDic[key][2]) > 0 :
            m = 1
            for arg in argDic[key][2] :
                m += argDic[arg][0]
                constraint += "-" + str(argDic[arg][0]) + " " + argDic[arg][3] + " "
            #constraint += ">= -" + str(argDic[key][0]) + " " + argDic[key][3] + " ;\n"
            constraint += "+" + str(argDic[key][0]) + " " + argDic[key][3] + " +" + str(m) + " ~"+ argDic[key][3]+ " >= 0 ;\n"
            #print(key, "constraint : ", constraint)
        else :
            constraint = "+1 " + argDic[key][3] + " +1 ~" + argDic[key][3] + " >= 1 ;\n"

        file.write(constraint)
        #print("constraint : ", constraint)
        constraintCount += 1
            
    return constraintCount


def writeDefense(argDic, file) :
    constraintCount = 0
    file.write("* Defense\n")
    m = 1
    for key in argDic.keys() :
        m += argDic[key][0]
    #print(m)
    
    for key in argDic.keys() :
        constraint2 = ""
        constraint3 = ""
        constraint4 = ""
        if len(argDic[key][2]) > 0 :
            attackerStrength = 0
            for arg in argDic[key][2] :
                constraint2 += "+" + str(argDic[arg][0]) + " " + argDic[arg][3] + " "
                constraint3 += "-" + str(argDic[arg][0]) + " " + argDic[arg][3] + " "
                constraint4 += "+" + str(argDic[arg][0]) + " " + argDic[arg][4] + " "
                attackerStrength += argDic[arg][0]
            #constraint2 += ">= +" + str(argDic[key][0]) + " " + argDic[key][4] + " ;\n"
            constraint2 += "-" + str(argDic[key][0]) + " " + argDic[key][4] + " >= 0 ;\n"
            constraint3 += "-" + str(argDic[key][0]) + " " + argDic[key][4] + " +" + str(m) + " " + argDic[key][4] + " >= -" + str(argDic[key][0]) + " ;\n"
            constraint4 += "+" + str(argDic[key][0]) + " " + argDic[key][3] + " -" + str(m) + " " + argDic[key][3] + " >= " + str(attackerStrength - m) + " ;\n"
            #print(constraint2)
            file.write("* Constraint 2\n")
            file.write(constraint2)
            file.write("* Constraint 3\n")
            file.write(constraint3)
            file.write("* Constraint 4\n")
            file.write(constraint4)
            constraintCount += 3
        else :
            file.write("* Constraint 2\n")
            constraint2 += "-1 " + argDic[key][4] + " >= 0 ;\n"
            file.write(constraint2)
            constraintCount += 1

    return constraintCount


def writeCompleteBis(argDic, file) :
    constraintCount = 0
    file.write("* Completeness Constraints\n")
    for key in argDic.keys() :
        if len(argDic[key][2]) > 0 :
            constraint5 = ""
            for arg in argDic[key][2] :
                constraint5 += "+" + str(argDic[arg][0]) + " ~" + argDic[arg][4] + " "
            constraint5 += "-" + str(argDic[key][0]) + " ~" + argDic[key][3] + " >=  0 ;\n"
            file.write(constraint5)
            constraintCount += 1
        else :
            constraint5 = "1 " + argDic[key][3] + " >= 1 ;\n"
            file.write(constraint5)
            constraintCount += 1
    return constraintCount

def writeComplete(argDic, file) :
    
    #print("argdic : ", argDic)
    m = 1
    for key in argDic.keys() :
        m += argDic[key][0]
    constraintCount = 0
    file.write("* Completeness Constraints\n")
    for key in argDic.keys() :
        if len(argDic[key][2]) > 0  or len(argDic[key][1]) > 0:
            constraint5 = ""
            for arg in argDic[key][2] :
                constraint5 += "+" + str(argDic[arg][0]) + " ~" + argDic[arg][4] + " +" + str(m) + " " + argDic[arg][3] + " "
            for arg in argDic[key][1] :
                constraint5 += "+" + str(m) + " " + argDic[arg][3] + " "
            constraint5 += "-" + str(argDic[key][0]) + " ~" + argDic[key][3] + " >= 0 ;\n"
            file.write(constraint5)
            constraintCount += 1
        else :
            constraint5 = "1 " + argDic[key][3] + " >= 1 ;\n"
            file.write(constraint5)
            constraintCount += 1
    return constraintCount


def writeStable(argDic, file) :
    constraintCount = 0
    file.write("* Stable\n")
    m = 1 
    for key in argDic.keys() :
        m += argDic[key][0]

    for key in argDic.keys() :
        if len(argDic[key][2]) > 0 :
            #constraint1 = ""
            constraint2 = ""
            for arg in argDic[key][2] :
                #constraint1 += "-" + str(argDic[arg][0]) + " " + argDic[arg][3] + " "
                constraint2 += "+" + str(argDic[arg][0]) + " " + argDic[arg][3] + " "
            #constraint1 += "-" + str(argDic[key][0]) + " " + argDic[key][3] + " +" + str(m) + " " + argDic[key][3] + " >= " + str(m) + " ;\n"
            constraint2 += "-" + str(argDic[key][0]) + " ~" + argDic[key][3] + " >=  0 ;\n"
            #file.write(constraint1)
            file.write(constraint2)
            constraintCount += 1 
        else :
            constraint2 = "1 " + argDic[key][3] + " >= 1 ;\n"
            file.write(constraint2)
            constraintCount += 1
    #print("number of stable cstr : ", constraintCount)
    return constraintCount

def updateConstraintCount(file, argDiff) :
    with open(file, 'r') as fin:
        data = fin.read().splitlines(True)
    with open(file, 'w') as fout:
        ligne = data[0]
        ligne2 = ligne.split()
        ligne = ligne[:-(len(ligne2[-1])+1)]
        ligne += str(int(ligne2[-1]) + argDiff)
        fout.write(ligne + '\n')
        fout.writelines(data[1:])


def line_prepender(filename, line):
    with open(filename, 'r+') as f:
        content = f.read()
        f.seek(0, 0)
        f.write(line.rstrip('\r\n') + '\n' + content)


#def writeStrongStable(argDic, File) :

def writeWeakStable(inputFile, outputFile) :
    argDic = readAspartix(inputFile)

    file = open(outputFile, "w")
    constraintCount = 0
    variableCount = len(argDic.keys())

    #constraintCount += writeDefense(argDic, file)
    constraintCount += writeWeakCF(argDic, file)
    constraintCount += writeStable(argDic, file)

    header = "* #variable= " + str(variableCount) + " #constraint= " + str(constraintCount) + "\n"

    file.close()

    line_prepender(outputFile, header)

    #print("number of weakstable cstr : ", constraintCount)
    return variableCount, constraintCount

def writeStrongStable(inputFile, outputFile) :
    argDic = readAspartix(inputFile)

    file = open(outputFile, "w")
    constraintCount = 0
    variableCount = len(argDic.keys())

    #constraintCount += writeDefense(argDic, file)
    constraintCount += writeStrongCF(argDic, file)
    constraintCount += writeStable(argDic, file)

    header = "* #variable= " + str(variableCount) + " #constraint= " + str(constraintCount) + "\n"

    file.close()

    line_prepender(outputFile, header)


    return variableCount, constraintCount

def writeWeakComplete(inputFile, outputFile) :
    argDic = readAspartix(inputFile)

    file = open(outputFile, "w")
    constraintCount = 0
    variableCount = len(argDic.keys())

    constraintCount += writeDefense(argDic, file)
    constraintCount += writeWeakCF(argDic, file)
    constraintCount += writeCompleteBis(argDic, file)

    header = "* #variable= " + str(variableCount*2) + " #constraint= " + str(constraintCount) + "\n"

    file.close()

    line_prepender(outputFile, header)


    return variableCount, constraintCount

def writeStrongComplete(inputFile, outputFile) :
    argDic = readAspartix(inputFile)

    file = open(outputFile, "w")
    constraintCount = 0
    variableCount = len(argDic.keys())

    constraintCount += writeDefense(argDic, file)
    constraintCount += writeStrongCF(argDic, file)
    constraintCount += writeComplete(argDic, file)

    header = "* #variable= " + str(variableCount*2) + " #constraint= " + str(constraintCount) + "\n"

    file.close()

    line_prepender(outputFile, header)


    return variableCount, constraintCount

def writeWeakAdmissible(inputFile, outputFile) :
    argDic = readAspartix(inputFile)

    file = open(outputFile, "w")
    constraintCount = 0
    variableCount = len(argDic.keys())

    constraintCount += writeDefense(argDic, file)
    constraintCount += writeWeakCF(argDic, file)

    header = "* #variable= " + str(variableCount*2) + " #constraint= " + str(constraintCount) + "\n"

    file.close()

    line_prepender(outputFile, header)


    return variableCount, constraintCount


def writeStrongAdmissible(inputFile, outputFile) :
    argDic = readAspartix(inputFile)

    file = open(outputFile, "w")
    constraintCount = 0
    variableCount = len(argDic.keys())

    constraintCount += writeDefense(argDic, file)
    constraintCount += writeStrongCF(argDic, file)

    header = "* #variable= " + str(variableCount*2) + " #constraint= " + str(constraintCount) + "\n"

    file.close()

    line_prepender(outputFile, header)


    return variableCount, constraintCount


def runOPB(opbFile, variableCount, constraintCount, solver ) :
    if (solver == "roundingsat") :
        try :
            proc = subprocess.run(["./roundingsat-master/build/roundingsat", opbFile, "--print-sol=1"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
        except subprocess.TimeoutExpired as e: 
            raise e
        x = -2
    
    elif(solver == "sat4j"): 
        try :
            proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", opbFile], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
        except subprocess.TimeoutExpired as e: 
            raise e
        x = -3

    elif(solver == "sat4jcp"):
        try :
            proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "CuttingPlanes", opbFile], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
        except subprocess.TimeoutExpired as e: 
            raise e
        x = -3
    
    elif(solver == "SAT"): 
        try :
            proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "SAT", opbFile], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
        except subprocess.TimeoutExpired as e: 
            raise e
        x = -3

    #proc = subprocess.run(["./roundingsat-master/build/roundingsat", opbFile, "--print-sol=1"], stdout = subprocess.PIPE, encoding= "UTF-8")
    res = proc.stdout.split("\n")
    
    if res[x].split()[0] == "v" :
        #print("res := ", res, "\n\n\n")
        return res[x].split()[1:]
    else :
        return None

def runEveryExtension(opbFile, variableCount, constraintCount, solver) :
    initial_time = time.time()
    #print("cstr count : ", constraintCount)
    extList = []

    try :
        admExt = runOPB(opbFile, variableCount, constraintCount, solver)
    except subprocess.TimeoutExpired as e :
        raise e
    #print("prefExtInit : ", admExt)
    while admExt != None :
        if time.time() - initial_time >= 600 :
            raise TimeoutError
        #print(admExt)
        extList.append(admExt)
        #print("extList : ", extList, "\n")
        constraint = ""

        for i in range(variableCount) :
            #print("i : ", i)
            if admExt[i][0] == "-" :
                constraint += " 1 " + admExt[i][1:]
            else :
                constraint += " 1 ~" + admExt[i]

        constraint += " >= 1 ;\n"

        file = open(opbFile, "a")
        file.write(constraint[1:])
        file.close()

        updateConstraintCount(opbFile, 1)
        constraintCount += 1

        admExt = runOPB(opbFile, variableCount, constraintCount, solver)
    return extList

def runPrefered(opbFile, variableCount, constraintCount, solver) :
    #print("entree runPref")

    file = open(opbFile, "r")
    copy = open("tempOPB.opb", "w")
    lines = file.read()
    copy.write(lines)
    copy.close()
    file.close()
    
    
    if (solver == "roundingsat") :
        try :
            proc = subprocess.run(["./roundingsat-master/build/roundingsat", "tempOPB.opb", "--print-sol=1"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
        except subprocess.TimeoutExpired as e: 
            raise e
        x = -2
    
    elif(solver == "sat4j"):
        #print("premier appel java")
        #print("appel java : ", "java", "-jar", "sat4j/sat4j-pb.jar", "tempOPB.opb")
        try :
            proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "tempOPB.opb"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
        except subprocess.TimeoutExpired as e: 
            raise e
        #print("juste apres appel java")
        x = -3

    elif(solver == "sat4jcp"): 
        try :
            proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "CuttingPlanes", "tempOPB.opb"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
        except subprocess.TimeoutExpired as e: 
            raise e
        #proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "CuttingPlanesStar", "tempOPB.opb"], stdout = subprocess.PIPE, encoding= "UTF-8")
        x = -3

    elif(solver == "SAT"):
        #print("solver SAT")
        try :
            proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "ResolutionGlucose", "tempOPB.opb"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
        except subprocess.TimeoutExpired as e: 
            raise e
        x = -3



    #proc = subprocess.run(["./roundingsat-master/build/roundingsat", "tempOPB.opb", "--print-sol=1"], stdout = subprocess.PIPE, encoding= "UTF-8")


    res = proc.stdout.split("\n")
    old_res = None
    #print("res avant while : ", res[x])

    while res[x].split()[0] == "v" :
        #print("entree while")
        constraint1 = ""
        constraint2 = ""
        c = 0
        
        copy = open("tempOPB.opb", "a")
        copy.write("* Iterative contraints\n")

        for var in res[x].split()[1:variableCount+1] :
            if var[0] == "-" :
                constraint1 += " +1 " + var[1:]
            else :
                #print("var : ", var)
                constraint2 += "+1 " + var + " >= +1 ;\n"
                c += 1
                copy.write(constraint2)
                #print("cosntraint 2 : ", constraint2)
                constraint2 = ""
        
        
        if len(constraint1) == 0 :
            #print('len cstr == 0')
            return res[x].split()[1:]




        constraint1 += " >= +1 ;\n"
        c += 1

        #print("constraint1 :", constraint1)
        
        copy.write(constraint1[1:]) 
        copy.close()
        updateConstraintCount("tempOPB.opb", c)

        old_res = res

        if (solver == "roundingsat") :
            try :
                proc = subprocess.run(["./roundingsat-master/build/roundingsat", "tempOPB.opb", "--print-sol=1"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
            except subprocess.TimeoutExpired as e: 
                raise e
        
        elif(solver == "sat4j"): 
            try :
                proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "tempOPB.opb"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
            except subprocess.TimeoutExpired as e: 
                raise e
        
        elif(solver == "sat4jcp"): 
            try :
                proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "CuttingPlanesStar", "tempOPB.opb"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
            except subprocess.TimeoutExpired as e: 
                raise e

        elif(solver == "SAT"): 
            try :
                proc = subprocess.run(["java", "-jar", "sat4j/sat4j-pb.jar", "ResolutionGlucose", "tempOPB.opb"], timeout=600, stdout = subprocess.PIPE, encoding= "UTF-8")
            except subprocess.TimeoutExpired as e: 
                raise e

        #proc = subprocess.run(["./roundingsat-master/build/roundingsat", "tempOPB.opb", "--print-sol=1"], stdout = subprocess.PIPE, encoding= "UTF-8")
        res = proc.stdout.split("\n")
        #print("res fin while : ", res[x].split()[1:])
    if old_res == None :
        #print("return none")
        return None
    
    #print("old res x split 1 : ", old_res[x].split()[1:], "\n")
    #print("return classic")
    return old_res[x].split()[1:]


def runEveryPrefered(opbFile, variableCount, constraintCount, solver) :
    initial_time = time.time()
    extList = []
    try :
        prefExt = runPrefered(opbFile, variableCount, constraintCount, solver)
    except subprocess.TimeoutExpired as e: 
        raise e
    while prefExt != None :
        if time.time() - initial_time >= 600 :
            raise TimeoutError
        extList.append(prefExt)

        constraint = "" #at least one argument is changing
        constraint2 ="" #one argument that was not accepted now is

        for i in range(variableCount) :
            #print("i : ", i)
            if prefExt[i][0] == "-" :
                constraint += " 1 " + prefExt[i][1:]
                constraint2 += " 1 " + prefExt[i][1:]
            else :
                constraint += " 1 ~" + prefExt[i]
                

        constraint += " >= 1 ;\n"
        
        if constraint2 == "" :
            return extList
        
        constraint2 += " >= 1 ;\n"

        file = open(opbFile, "a")
        file.write(constraint[1:])
        file.write(constraint2[1:])
        updateConstraintCount(opbFile, 2)


        file.close()

        try :
            prefExt = runPrefered(opbFile, variableCount, constraintCount, solver)
        except subprocess.TimeoutExpired as e: 
            raise e

    return extList


def buildOPB(filePath, mode) :
    argDic = readAspartix(filePath)

    file = open("temp.opb", "w")
    #file.write("* #variable=4 #contraint= 4\n")
    constraintCount = 0
    variableCount = len(argDic.keys())

    if mode == "SA" :
        #strong admissible
        constraintCount += writeDefense(argDic, file)
        constraintCount += writeStrongCF(argDic, file)

    if mode == "WA" :
        #weak admissible
        constraintCount += writeDefense(argDic, file)
        constraintCount += writeWeakCF(argDic, file)
    
    
    #print(constraintCount)

    if mode == "SC" :
        #complete strong
        constraintCount += writeDefense(argDic, file)
        constraintCount += writeStrongCF(argDic, file)
        constraintCount += writeComplete(argDic, file)

    if mode == "WC" :
        #complete weak
        constraintCount += writeDefense(argDic, file)
        constraintCount += writeWeakCF(argDic, file)
        constraintCount += writeComplete(argDic, file)

    if mode == "WS": 
        #stable weak
        print("21")
        constraintCount += writeWeakStable(argDic, file)


    if mode == "SP":
        #strong prefered
        constraintCount += writeDefense(argDic, file)
        constraintCount += writeStrongCF(argDic, file)
    
        file.close()
        file = open("generatedOPB2.opb", "w")
        rfile = open("temp.opb", "r")
        content = rfile.read()
        header = "* #variable= " + str(variableCount) + " #constraint= " + str(constraintCount) + "\n"
        file.write(header)
        file.write(content)
        """ footer = "footer\n"
        file.write(footer)
        print("lul") """
        file.close()
        rfile.close()

        proc = subprocess.run(["./roundingsat-master/build/roundingsat", "generatedOPB2.opb", "--print-sol=1"], stdout = subprocess.PIPE, encoding= "UTF-8")
        res = proc.stdout.split("\n")

        while res[-2].split()[0] =="v" :
            
            print(res[-2].split()[1:])
            constraint = ""
            for var in res[-2].split()[1:] :
                if var[0] == "-"  and int(var[2:]) <= variableCount:
                    print()
                    constraint += " +1 " + var[1:]
            
            if len(constraint) == 0 :
                return res[-2].split()

            constraint += " >= +1 ;"
            constraintCount += 1

            print("constraint :", constraint)
            file = open("generatedOPB2.opb", "a")
            file.write(constraint[1:])
            file.close()

            #line_prepender("generatedOPB2.opb", "lul")

            old_res = res

            proc = subprocess.run(["./roundingsat-master/build/roundingsat", "generatedOPB2.opb", "--print-sol=1"], stdout = subprocess.PIPE, encoding= "UTF-8")
            res = proc.stdout.split("\n")
            print(res[-2].split()[1:])

        return old_res[-2].split()


    if mode == "WP":
        #weak weak prefered
        pass

    print("lafin")
    file.close()
    file = open(sys.path[0]+ "\\" +"generatedOPB.opb", "w")
    rfile = open(sys.path[0]+ "\\" +"temp.opb", "r")
    content = rfile.read()
    header = "* #variable= " + str(variableCount) + " #constraint= " + str(constraintCount) + "\n"
    file.write(header)
    file.write(content)
    file.close()
    rfile.close()
    

def isStrongCF(set, argDic) :
    for i in set :
        for j in set :
            if i != j :
                if j in argDic[i][1] :
                    return False
    return True

def isWeakCF(set, argDic) :
    for i in set :
        for j in set :
            if i != j :
                if j in argDic[i][1] :
                    if argDic[i][0] > argDic[j][0] :
                        return False
    return True

def isSelfDefended(set, argDic) :
    for i in set :
        if not isDefended(set, argDic, i) :
            return False
    return True

def isDefended(set, argDic, arg) :
    aStrength = 0
    for attacker in argDic[arg][2] :
        if not isDefeated(set, argDic, attacker) :
            aStrength += argDic[attacker][0]
    #print("comparaison : ", argDic[arg][0], " > ", aStrength)
    return argDic[arg][0] >= aStrength

def isDefeated(set, argDic, arg) :
    aStrength = 0
    for attacker in argDic[arg][2] :
        if attacker in set :
            aStrength += argDic[attacker][0]
    return argDic[arg][0] <= aStrength

def isWeakAdmissible(set, argDic) :
    if isSelfDefended(set, argDic) and isWeakCF(set, argDic) :
        return True
    return False

def isStrongAdmissible(set, argDic) :
    if isSelfDefended(set, argDic) and isStrongCF(set, argDic) :
        return True
    return False

def isStrongStable(set, argDic) : 
    if not isStrongAdmissible(set, argDic) :
        return False
    
    for arg in argDic.keys() :
        if arg not in set :
            if not isDefeated(set, argDic, arg) :
                return False
    return True

def isWeakStable(set, argDic) :
    if not isWeakAdmissible(set, argDic) :
        return False
    #print("set : ", set)
    for arg in argDic.keys() :
        if arg not in set :
            if not isDefeated(set, argDic, arg) :
                return False
    return True

def isStrongComplete(set, argDic) :
    if not isStrongAdmissible(set, argDic) :
        return False
    for arg in argDic.keys() :
        if arg not in set :
            setbis = []
            for a in set : 
                setbis.append(a)
            setbis.append(arg)
            if isDefended(set, argDic, arg) :
                if isStrongCF(setbis, argDic) :
                    return False
    return True

def isWeakComplete(set, argDic) :
    if not isWeakAdmissible(set, argDic) :
        return False
    for arg in argDic.keys() :
        if arg not in set :
            setbis = []
            for a in set : 
                setbis.append(a)
            setbis.append(arg)
            if isDefended(set, argDic, arg) and isWeakCF(setbis, argDic) :
                return False
    return True

def naiveEveryWeakAdmissible(inputFile) :

    argDic = readAspartix(inputFile)
    everyExt = powerset(argDic.keys())
    extList = []

    for ext in everyExt :
        if isWeakAdmissible(ext, argDic) :
            extList.append(ext)
    return extList

def naiveEveryWeakPrefered(inputFile) :
    extList = naiveEveryWeakAdmissible(inputFile)
    #print("extlist : ", extList)
    res = []
    for ext in extList :
        new = True
        for comp in extList :
            if set(ext).issubset(comp) and ext != comp :
                #print("ext1&2 : ", ext, comp)
                new = False

        if new :
            #print("ext1&2 : ", ext, comp)
            res.append(ext)

    return res

def naiveEveryStrongAdmissible(inputFile) :

    argDic = readAspartix(inputFile)
    everyExt = powerset(argDic.keys())
    extList = []

    for ext in everyExt :
        if isStrongAdmissible(ext, argDic) :
            extList.append(ext)
    return extList

def naiveEveryStrongPrefered(inputFile) :
    extList = naiveEveryStrongAdmissible(inputFile)
    #print("extlist : ", extList)
    res = []
    for ext in extList :
        new = True
        for comp in extList :
            if set(ext).issubset(comp) and ext != comp :
                #print("ext1&2 : ", ext, comp)
                new = False

        if new :
            #print("ext1&2 : ", ext, comp)
            res.append(ext)

    return res

def naiveEveryStrongComplete(inputFile) :
    argDic = readAspartix(inputFile)
    everyExt = powerset(argDic.keys())
    extList = []

    for ext in everyExt :
        if isStrongComplete(ext, argDic):
            extList.append(ext)
    return extList

def naiveEveryWeakComplete(inputFile) :
    argDic = readAspartix(inputFile)
    everyExt = powerset(argDic.keys())
    extList = []

    for ext in everyExt :
        if isWeakComplete(ext, argDic):
            extList.append(ext)
    return extList

def naiveEveryStrongStable(inputFile) :
    argDic = readAspartix(inputFile)
    everyExt = powerset(argDic.keys())
    extList = []

    for ext in everyExt :
        if isStrongStable(ext, argDic):
            extList.append(ext)
    return extList

def naiveEveryWeakStable(inputFile) :
    argDic = readAspartix(inputFile)
    everyExt = powerset(argDic.keys())
    extList = []

    for ext in everyExt :
        if isWeakStable(ext, argDic):
            extList.append(ext)
    return extList



def timeout_Handler(signum, frame) :
    raise Exception("timeout reached")

def main():
    solverList = ["sat4j", "roundingsat", "sat4jcp", "SAT", "naive"]

    semantics = {"spref" : writeStrongAdmissible, "wpref" : writeWeakAdmissible, "sadm" : writeStrongAdmissible, "wadm": writeWeakAdmissible, "scom" : writeStrongComplete, "wcom" : writeWeakComplete, "sstb" : writeStrongStable, "wstb" : writeWeakStable}

    operations = ["enum", "verif", "skeptical", "credulous", "one"]

    args = sys.argv

    if args[1] not in solverList :
        print("This solver does not exist")
        return

    if args[2] not in semantics.keys() :
        print("semantics does not exist")
        return
    
    if args[3] not in operations :
        print("operation does not exist")
        return

    fileName = args[4]

    operation = args[3]

    semantic = args[2]
    
    solver = args[1]

    filePath = sys.path[0]+ "/" + fileName

    if solver != "naive" :
        if operation == "enum" :

            variableCount, constraintCount = semantics[semantic](filePath, "generatedOPB0.opb")

            t1_start = time.process_time()
            t2_start = time.time()
            if semantic == "spref" or semantic == "wpref" :
                try :
                    res = runEveryPrefered("generatedOPB0.opb", variableCount, constraintCount, solver)
                except subprocess.TimeoutExpired as e: 
                    print("-1")
                    return
                except TimeoutError :
                    print("-1")
                    return
            else :
                try :
                    res = runEveryExtension("generatedOPB0.opb", variableCount, constraintCount, solver)
                except subprocess.TimeoutExpired :
                    print("-1")
                    return
                except TimeoutError :
                    print("-1")
                    return
            t1_stop = time.process_time()
            t2_stop = time.time()
            #print("res : ", res, "\n")
            print("number of ext : ", len(res), "\n")
            #print("process time : ", t1_stop-t1_start, "\n")
            print(t2_stop-t2_start)

        if operation == "one" :
            variableCount, constraintCount = semantics[semantic](filePath, "generatedOPB0.opb")

            t1_start = time.process_time()
            t2_start = time.time()
            if semantic == "spref" or semantic == "wpref" :
                try :
                    res = runPrefered("generatedOPB0.opb", variableCount, constraintCount, solver)
                except subprocess.TimeoutExpired as e: 
                    print("-1")
                    return


            else :
                try :
                    res = runOPB("generatedOPB0.opb", variableCount, constraintCount, solver)
                except subprocess.TimeoutExpired :
                    print("-1")
                    return
            t1_stop = time.process_time()
            t2_stop = time.time()
            #print("res : ", res, "\n")
            print("number of ext : ", 1, "\n")
            #print("process time : ", t1_stop-t1_start, "\n")
            print(t2_stop-t2_start)
    
    else :

        signal.signal(signal.SIGALRM, timeout_Handler)
        signal.alarm(600)

        t2_start = time.time()

        argDic = readAspartix(filePath)
        try :
            if args[2] == "wpref" :
                res = naiveEveryWeakPrefered(filePath)

            if args[2] == "spref" :
                res = naiveEveryStrongPrefered(filePath)
            
            if args[2] == "wadm" :
                res = naiveEveryWeakAdmissible(filePath)

            if args[2] == "sadm" :
                res = naiveEveryStrongAdmissible(filePath)

            if args[2] == "wstb" :
                res = naiveEveryWeakStable(filePath)

            if args[2] == "sstb" :
                res = naiveEveryStrongStable(filePath)

            if args[2] == "wcom" :
                res = naiveEveryWeakComplete(filePath)

            if args[2] == "scom" :
                res = naiveEveryStrongComplete(filePath)
            #res = naiveEveryWeakAdmissible(filePath)
            #res = naiveEveryStrongAdmissible(filePath)
            #res = naiveEveryStrongPrefered(filePath)
        except Exception :
            print("-1")
            return

        t2_stop = time.time()
        #print("res : ", res, "\n")
        print("number of ext : ", len(res), "\n")
        print(t2_stop-t2_start)



if __name__ == "__main__":
    main()
