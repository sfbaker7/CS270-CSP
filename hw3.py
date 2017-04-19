from collections import defaultdict
import time
state_count = 0
#########################  Problem 1 and 2 code below #####################

class Constraint:
    """A constraint of a CSP.  Members include
     - name: a string for debugging
     - domain, a list of variables on which the constraint acts
     - predicate, a boolean function with the same arity as the domain.
     """
    def __init__(self,name,domain,pred):
        self.name = name
        self.domain = domain
        self.predicate = pred

    def isSatisfied(self,vars):
        """Given a dictionary of variables, evaluates the predicate.
        If a variable in the domain isn't present, raises a KeyError."""
        args = [vars[v] for v in self.domain]
        return self.predicate(*args)

class CSP:
    """Defines a constraint satisfaction problem.  Contains 4 members:
    - variables: a list of variables
    - domains: a dictionary mapping variables to domains
    - constraints: a list of Constraints.
    - incidentConstraints: a dict mapping each variable to a list of
      constraints acting on it.
    """

    def __init__(self,variables=[],domains=[]):
        """Input: a list of variables and a list of domains.

        Note: The variable names must be unique, otherwise undefined behavior
        will result.
        """
        self.variables = variables[:]
        self.domains = dict(zip(variables,domains))
        self.constraints = []
        self.incidentConstraints = dict((v,[]) for v in variables)

    def addVariable(self,var,domain):
        """Adds a new variable with a given domain.  var must not already
        be present in the CSP."""
        if var in self.domains:
            raise ValueError("Variable with name "+val+" already exists in CSP")
        self.variables.append(var)
        self.domains[var] = domain
        self.incidentConstraints[var] = []

    def addConstraint(self,varlist,pred,name=None):
        """Adds a constraint with the domain varlist, the predicate pred,
        and optionally a name for printing."""
        if name==None:
            name = "c("+",".join(str(v) for v in varlist)+")"
        self.constraints.append(Constraint(name,varlist,pred))
        for v in varlist:
            self.incidentConstraints[v].append(self.constraints[-1])

    def addUnaryConstraint(self,var,pred,name=None):
        """Adds a unary constraint with the argument var, the predicate pred,
        and optionally a name for printing."""
        self.addConstraint((var,),pred,name)

    def addBinaryConstraint(self,var1,var2,pred,name=None):
        """Adds a unary constraint with the arguments (var1,var2), the
        predicate pred, and optionally a name for printing."""
        self.addConstraint((var1,var2),pred,name)

    def fixValue(self,var,value,name=None):
        """Adds a constraint that states var = value."""
        if name==None:
            name = str(var)+'='+str(value)
        self.addUnaryConstraint(var,lambda x:x==value,name)

    def nAryConstraints(self,n,var=None):
        """Returns a list of all n-ary constraints in the CSP if var==None,
        or if var is given, returns a list of all n-ary constraints involving
        var."""
        if var==None:
            return [c for c in self.constraints if len(c.domain)==n]
        else:
            return [c for c in self.incidentConstraints[var] if len(c.domain)==n]

    def incident(self,*vars):
        """incident(var1,...,varn) will return a list of constraints
        that involve all of var1 to varn."""
        if len(vars)==0: return self.constraints
        res = set(self.incidentConstraints[vars[0]])
        for v in vars[1:]:
            res &= set(self.incidentConstraints[v])
        return [c for c in res]

    def isConstraintSatisfied(self,c,partialAssignment):
        """Checks if the partial assignment satisfies the constraint c.
        If the partial assignment doesn't cover the domain, this returns
        None. """
        try:
            res = c.isSatisfied(partialAssignment)
            return res
        except KeyError:
            return None

    def isValid(self,partialAssignment,*vars):
        """Checks if the assigned variables in a partial assignment
        are mutually compatible.  Only checks those constraints
        involving assigned variables, and ignores any constraints involving
        unassigned ones.

        If no extra arguments are given, checks all constraints relating
        assigned variables.

        If extra arguments var1,...,vark are given, this only checks
        constraints that are incident to those given variables."""
        for c in self.incident(*vars):
            #all entries in partialAssignment must be in the domain of c
            #for this to be checked
            if self.isConstraintSatisfied(c,partialAssignment)==False:
                return False
        return True

def streetCSP():
    """Returns a CSP corresponding to the street puzzle covered in class."""
    nationalityVars = ['N1','N2','N3','N4','N5']
    colorVars = ['C1','C2','C3','C4','C5']
    drinkVars = ['D1','D2','D3','D4','D5']
    jobVars = ['J1','J2','J3','J4','J5']
    animalVars = ['A1','A2','A3','A4','A5']
    nationalities = ['E','S','J','I','N']
    colors = ['R','G','W','Y','B']
    drinks = ['T','C','M','F','W']
    jobs = ['P','S','Di','V','Do']
    animals = ['D','S','F','H','Z']

    csp = CSP(nationalityVars+colorVars+drinkVars+jobVars+animalVars,
              [nationalities]*5+[colors]*5+[drinks]*5+[jobs]*5+[animals]*5)

    #make sure all of the variables in a particular class take on different values
    for a, na in enumerate(nationalityVars):
        for b, nb in enumerate(nationalityVars):
            if na!=nb and a < b:
                csp.addBinaryConstraint(na,nb,lambda x,y: x!=y,'nationalityVars are not equal')
    #make sure all of the variables in a particular class take on different values
    for a, na in enumerate(colorVars):
        for b, nb in enumerate(colorVars):
            if na!=nb and a < b:
                csp.addBinaryConstraint(na,nb,lambda x,y: x!=y,'colorVars are not equal')
    #make sure all of the variables in a particular class take on different values
    for a, na in enumerate(drinkVars):
        for b, nb in enumerate(drinkVars):
            if na!=nb and a < b:
                csp.addBinaryConstraint(na,nb,lambda x,y: x!=y,'drinkVars are not equal')
    #make sure all of the variables in a particular class take on different values
    for a, na in enumerate(jobVars):
        for b, nb in enumerate(jobVars):
            if na!=nb and a < b:
                csp.addBinaryConstraint(na,nb,lambda x,y: x!=y,'jobVars are not equal')
    #make sure all of the variables in a particular class take on different values
    for a, na in enumerate(animalVars):
        for b, nb in enumerate(animalVars):
            if na!=nb and a < b:
                csp.addBinaryConstraint(na,nb,lambda x,y: x!=y,'animalVars are not equal')

    #Englishman lives in the red house
    for Ni,Ci in zip(nationalityVars,colorVars):
        csp.addBinaryConstraint(Ni,Ci,lambda x,y:(x=='E')==(y=='R'),'Englishman lives in the red house')
    #Spaniard has a dog
    for Ni,Ai in zip(nationalityVars,animalVars):
        csp.addBinaryConstraint(Ni,Ai,lambda x,y:(x=='S')==(y=='D'),'Spaniard has a dog')
    #Japanese is a painter
    for Ni,Ji in zip(nationalityVars,jobVars):
        csp.addBinaryConstraint(Ni,Ji,lambda x,y:(x=='J')==(y=='P'),'Japanese is a painter')

    #Italian drinks tea
    for Ni,Di in zip(nationalityVars,drinkVars):
        csp.addBinaryConstraint(Ni,Di,lambda x,y:(x=='I')==(y=='T'),'The Italian drinks Tea')
    #Norwegian lives in first house
    csp.fixValue('N1','N','Norwegian lives in the first house')

    #green house is to the right of the white house
    for Ci,Cn in zip(colorVars[:-1],colorVars[1:]):
        csp.addBinaryConstraint(Ci,Cn,lambda x,y:(x=='W')==(y=='G'),'Green house is to the right of the white house')
    csp.addUnaryConstraint('C5',lambda x:x!='W','Green house is to the right of the white house')
    csp.addUnaryConstraint('C1',lambda x:x!='G','Green house is to the right of the white house')

    #The owner of the Green house drinks Coffee
    for Ci,Di in zip(colorVars,drinkVars):
        csp.addBinaryConstraint(Ci,Di,lambda x,y:(x=='G')==(y=='C'),'The owner of the Green house drinks Coffee')

    #The Sculptor breeds Snails
    for Ji,Ai in zip(jobVars,animalVars):
        csp.addBinaryConstraint(Ji,Ai,lambda x,y:(x=='S')==(y=='S'),'The Sculptor breeds Snails')

    #The Diplomat lives in the Yellow house
    for Ji,Ci in zip(jobVars,colorVars):
        csp.addBinaryConstraint(Ji,Ci,lambda x,y:(x=='Di')==(y=='Y'),'The Diplomat lives in the Yellow house')

    #The owner of the middle house drinks Milk
    csp.fixValue('D3','M','The owner of the middle house drinks Milk')

    #The Norwegian lives next door to the Blue house
    csp.fixValue('C2','B','The Norwegian lives next door to the Blue house')

    #The Violinist drinks Fruit juice
    for Ji,Di in zip(jobVars,drinkVars):
        csp.addBinaryConstraint(Ji,Di,lambda x,y:(x=='V')==(y=='F'),'The Violinist drinks Fruit juice')

    #The Fox is in the house next to the Doctors
    for Ai,Ji,An in zip(animalVars[0:3],jobVars[1:4], animalVars[2:5]):
        csp.addConstraint([Ai,Ji,An],lambda x,y,z:(x=='F')==(y=='Do') or (z=='F')==(y=='Do'),'The Fox is in the house next to the Doctors')
    csp.addBinaryConstraint('A4','J5',lambda x,y:(x=='F')==(y=='Do'),'The Fox is in the house next to the Doctors')
    csp.addBinaryConstraint('A2','J1',lambda x,y:(x=='F')==(y=='Do'),'The Fox is in the house next to the Doctors')

    #The Horse is next to the Diplomats
    for Ai,Ji,An in zip(animalVars[0:3],jobVars[1:4], animalVars[2:5]):
        csp.addConstraint([Ai,Ji,An],lambda x,y,z:(x=='H')==(y=='Di') or (z=='H')==(y=='Di'),'The Horse is next to the Diplomats')
    csp.addBinaryConstraint('A4','J5',lambda x,y:(x=='H')==(y=='Di'),'The Horse is next to the Diplomats')
    csp.addBinaryConstraint('A2','J1',lambda x,y:(x=='H')==(y=='Di'),'The Horse is next to the Diplomats')

    print "CSP has",len(csp.constraints),"constraints"

    return csp

def p1():
    csp = streetCSP()
    solution = dict([('A1', 'F'), ('A2', 'H'), ('A3', 'S'), ('A4', 'D'), ('A5', 'Z'),
                     ('C1', 'Y'), ('C2', 'B'), ('C3', 'R'), ('C4', 'W'), ('C5', 'G'),
                     ('D1', 'W'), ('D2', 'T'), ('D3', 'M'), ('D4', 'F'), ('D5', 'C'),
                     ('J1', 'Di'), ('J2', 'Do'), ('J3', 'S'), ('J4', 'V'), ('J5', 'P'),
                     ('N1', 'N'), ('N2', 'I'), ('N3', 'E'), ('N4', 'S'), ('N5', 'J')])
    invalid1 = dict([('A1', 'F'), ('A2', 'H'), ('A3', 'S'), ('A4', 'D'), ('A5', 'Z'),
                     ('C1', 'Y'), ('C2', 'B'), ('C3', 'R'), ('C4', 'W'), ('C5', 'G'),
                     ('D1', 'T'), ('D2', 'W'), ('D3', 'M'), ('D4', 'F'), ('D5', 'C'),
                     ('J1', 'Di'), ('J2', 'Do'), ('J3', 'S'), ('J4', 'V'), ('J5', 'P'),
                     ('N1', 'N'), ('N2', 'I'), ('N3', 'E'), ('N4', 'S'), ('N5', 'J')])
    invalid2 = dict([('A1', 'F'), ('A2', 'F'), ('A3', 'S'), ('A4', 'D'), ('A5', 'Z'),
                     ('C1', 'Y'), ('C2', 'B'), ('C3', 'R'), ('C4', 'W'), ('C5', 'G'),
                     ('D1', 'W'), ('D2', 'T'), ('D3', 'M'), ('D4', 'F'), ('D5', 'C'),
                     ('J1', 'Di'), ('J2', 'Do'), ('J3', 'S'), ('J4', 'V'), ('J5', 'P'),
                     ('N1', 'N'), ('N2', 'I'), ('N3', 'E'), ('N4', 'S'), ('N5', 'J')])
    print "Valid assignment valid?",csp.isValid(solution)
    print "Invalid assignment valid?",csp.isValid(invalid1)
    print "Invalid assignment valid?",csp.isValid(invalid2)


    # solver = CSPBacktrackingSolver(csp)
    # res = solver.solve()
    # print "Result:",sorted(res.items())

############################  Problem 2 code below #######################

class CSPBacktrackingSolver:
    """ A CSP solver that uses backtracking.
    A state is a partial assignment dictionary {var1:value1,...,vark:valuek}.
    Also contains a member oneRings that is a dict mapping each variable to
    all variables that share a constraint.
    """
    def __init__(self,csp,doForwardChecking=True,doConstraintPropagation=False):
        self.csp = csp
        self.doForwardChecking = doForwardChecking
        self.doConstraintPropagation = doConstraintPropagation
        #compute 1-rings
        self.oneRings = dict((v,set()) for v in csp.variables)
        for c in csp.constraints:
            cdomain = set(c.domain)
            for v in c.domain:
                self.oneRings[v] |= cdomain
        for v in csp.variables:
            if v in self.oneRings[v]:
                self.oneRings[v].remove(v)

    def solve(self):
        """Solves the CSP, returning an assignment if solved, or False if
        failed."""
        domains = self.initialDomains()
        timer = time.clock()
        final = self.search({},domains)
        print time.clock() - timer
        return final

    def search(self,partialAssignment,domains):
        """Runs recursive backtracking search."""

        global state_count

        if len(partialAssignment)==len(self.csp.variables):
            return partialAssignment
        if self.doConstraintPropagation:
            domains = self.constraintPropagation(partialAssignment,domains)
            #contradiction detected
            if any(len(d)==0 for (v,d) in domains.iteritems()):
                return False
        indent = " "*len(partialAssignment)
        X = self.pickVariable(partialAssignment,domains)
        values = self.orderValues(partialAssignment,domains,X)
        for v in values:
            state_count += 1
            partialAssignment[X] = v
            if self.doForwardChecking:
                print indent+"Trying",X,"=",v
                #do forward checking
                newDomains = self.forwardChecking(partialAssignment,X,domains)
                if any(len(d)==0 for (v,d) in newDomains.iteritems()):
                    #contradiction, go on to next value
                    emptyvars = [v for (v,d) in newDomains.iteritems() if len(d)==0]
                    print indent+" Forward checking found contradiction on",emptyvars[0]
                    continue
                #recursive call
                print 'state_count: %d' %  state_count
                res = self.search(partialAssignment,newDomains)
                if res!=False: return res
            else:
                #check whether the assignment X=v is valid
                if self.csp.isValid(partialAssignment,X):
                    print indent+"Trying",X,"=",v
                    #recursive call
                    res = self.search(partialAssignment,domains)
                    print 'state_count: %d' % state_count
                    if res!=False: return res
        #remove the partial assignment to X, backtrack
        del partialAssignment[X]
        return False

    def initialDomains(self):
        """Does the basic step of checking all unary constraints"""
        domains = dict()
        for v,domain in self.csp.domains.iteritems():
            #save only valid constraints
            vconstraints = self.csp.nAryConstraints(1,v)
            dvalid = [val for val in domain if all(c.predicate(val) for c in vconstraints)]
            domains[v] = dvalid
        return domains

    def pickVariable(self,partialAssignment,domains):
        """Return an unassigned variable to assign next"""

        fin_var = ''
        most_constraining = []
        most_constrained = [(var, len(doms)) for var, doms in domains.items() if var not in partialAssignment]
        most_constrained.sort(key=lambda x: x[1])
        fin_var = most_constrained[0]
        mini = fin_var[1]

        for variable, length in most_constrained:
            if length == mini:
                most_constraining.append((variable, length))
        maxi = -1000
        for variable, length in most_constraining:
            if maxi<len(self.csp.incidentConstraints[variable]):
                maxi = len(self.csp.incidentConstraints[variable])
                fin_var = (variable, length)

        return fin_var[0]


    def orderValues(self,partialAssignment,domains,var):
        """Return an ordering on the domain domains[var]"""

        return domains[var]

    def constraintPropagation(self,partialAssignment,domains):
        """domains is a dict mapping vars to valid values.
        Return a copy of domains but with all invalid values removed."""

        return domains

    def forwardChecking(self,partialAssignment,var,domains):
        """domains is a dict mapping vars to valid values.  var has just been
        assigned.
        Return a copy of domains but with all invalid values removed"""
        resdomain = dict()
        #do a shallow copy for all unaffected domains, this saves time
        for v,domain in domains.iteritems():
            resdomain[v] = domain
        resdomain[var] = [partialAssignment[var]]



        # return resdomain


        #NOTE: be sure not to modify the resdomains directly, but to create
        #      new lists
        for c in self.csp.incidentConstraints[var]:
            #If the domain has size k and exactly k-1 entries are filled, then
            #do forward checking.  If so, 'unassigned' will contain the name of
            #the unassigned variable.
            kassigned = 0
            unassigned = None
            for v in c.domain:
                if v in partialAssignment:
                    kassigned += 1
                else:
                    unassigned = v
            if kassigned+1 == len(c.domain):
                print "Forward checking",unassigned
                validvalues = []
                ndict = {}


                #(resdomain[unassigned]) is compatible under c. May want to use
                #self.csp.isConstraintSatisfied(c,assignment).  If compatible,
                #append the value to validvalues

                for var, val in partialAssignment.items():
                    ndict[var] = val
                for val in resdomain[unassigned]:
                    ndict[unassigned] = val
                    if self.csp.isConstraintSatisfied(c,ndict):
                        validvalues.append(val)

                resdomain[unassigned] = validvalues
                if len(validvalues)==0:

                    #print "Domain of",unassigned,"emptied due to",c.name
                    #early terminate, this setting is a contradiction
                    return resdomain
        return resdomain

def nQueensCSP(n):
    """Returns a CSP for an n-queens problem"""
    vars = ['Q'+str(i) for i in range(1,n+1)]
    domain = range(1,n+1)
    csp = CSP(vars,[domain]*len(vars))
    for i in range(1,n+1):
        for j in range(1,i):
            Qi = 'Q'+str(i)
            Qj = 'Q'+str(j)
            ofs = i-j

            csp.addBinaryConstraint(Qi,Qj,(lambda x,y: x!=y),Qi+"!="+Qj)
            csp.addBinaryConstraint(Qi,Qj,(lambda x,y,ofs=ofs: x!=(y+ofs)),Qi+"!="+Qj+"+"+str(i-j))
            csp.addBinaryConstraint(Qi,Qj,(lambda x,y,ofs=ofs: x!=(y-ofs)),Qi+"!="+Qj+"-"+str(i-j))
    return csp

def p2():

    csp = nQueensCSP(4)
    solver = CSPBacktrackingSolver(csp,doForwardChecking=True)
    res = solver.solve()
    print "Result:",sorted(res.items())


    csp = nQueensCSP(4)
    solver = CSPBacktrackingSolver(csp,doForwardChecking=True)
    res = solver.solve()
    print "Result:",sorted(res.items())
    raw_input()

    csp = nQueensCSP(8)
    solver = CSPBacktrackingSolver(csp,doForwardChecking=True)
    res = solver.solve()
    print "Result:",sorted(res.items())
    raw_input()

    csp = nQueensCSP(20)
    solver = CSPBacktrackingSolver(csp,doForwardChecking=True)
    res = solver.solve()
    print "Result:",sorted(res.items())
    raw_input()

    csp = nQueensCSP(50)
    solver = CSPBacktrackingSolver(csp,doForwardChecking=True)
    res = solver.solve()
    print "Result:",sorted(res.items())





############################  Problem 4 code below #######################

def marginalize(probabilities,index):
    """Given a probability distribution P(X1,...,Xi,...,Xn),
    return the distribution P(X1,...,Xi-1,Xi+1,...,Xn).
    - probabilities: a probability table, given as a map from tuples
      of variable assignments to values
    - index: the value of i.
    """
    probA = {}
    for a, b in probabilities.items():
        templist = []
        for i in range(len(a)):
            if i != index:
                templist.append(a[i])

        new_probs = tuple(templist)

        if new_probs not in probA:
            probA[new_probs] = b
        else:
            probA[new_probs] += b
    return probA


def marginalize_multiple(probabilities,indices):
    """Safely marginalizes multiple indices"""
    pmarg = probabilities
    for index in reversed(sorted(indices)):
        pmarg = marginalize(pmarg,index)
    return pmarg

def condition1(probabilities,index,value):
    """Given a probability distribution P(X1,...,Xi,...,Xn),
    return the distribution P(X1,...,Xi-1,Xi+1,...,Xn | Xi=v).
    - probabilities: a probability table, given as a map from tuples
      of variable assignments to values
    - index: the value of i.
    - value: the value of v
    """
    probs = {}
    denom = 0

# get denominator
    for a, b in probabilities.items():
        for i in range(len(a)):
            if i == index:
                if a[i] == value:
                    denom += probabilities[a]

    for a, b in probabilities.items():
        for i in range(len(a)):
            templist = []
            if i == index:
                if a[i] == value:

                    templist.append(a[0])
                    num = b/denom
                    templist = [a[0]]
                    new_probs = tuple(templist)

                    if new_probs not in probs:
                        probs[new_probs] = num
                    else:
                        probs[new_probs] += num

    return probs



    #Compute the denominator by marginalizing over everything but Xi

def normalize(probabilities):
    """Given an unnormalized distribution, returns a normalized copy that
    sums to 1."""
    vtotal = sum(probabilities.values())
    return dict((k,v/vtotal) for k,v in probabilities.iteritems())

def condition2(probabilities,index,value):
    """Given a probability distribution P(X1,...,Xi,...,Xn),
    return the distribution P(X1,...,Xi-1,Xi+1,...,Xn | Xi=v).
    - probabilities: a probability table, given as a map from tuples
      of variable assignments to values
    - index: the value of i.
    - value: the value of v
    """
    probs = {}

    for a, b in probabilities.items():
        for i in range(len(a)):
            templist = []
            if i == index:
                if a[i] == value:

                    templist.append(a[0])
                    templist = [a[0]]
                    new_probs = tuple(templist)

                    if new_probs not in probs:
                        probs[new_probs] = b
                    else:
                        probs[new_probs] += b
    return normalize(probs)


def p4():
    pAB = {(0,0):0.5,
           (0,1):0.3,
           (1,0):0.1,
           (1,1):0.1}
    pA = marginalize(pAB,1)
    print (pA[(0,)],pA[(1,)]),"should be",(0.8,0.2)

    pABC = {(0,0,0):0.2,
            (0,0,1):0.3,
            (0,1,0):0.06,
            (0,1,1):0.24,
            (1,0,0):0.02,
            (1,0,1):0.08,
            (1,1,0):0.06,
            (1,1,1):0.04}

    print "marginalized p(A,B): ",dict(marginalize(pABC,2))
    pA = marginalize(marginalize(pABC,2),1)
    print (pA[(0,)],pA[(1,)]),"should be",(0.8,0.2)

    pA_B = condition1(pAB,1,1)
    print (pA_B[(0,)],pA_B[(1,)]),"should be",(0.75,0.25)
    pA_B = condition2(pAB,1,1)
    print (pA_B[(0,)],pA_B[(1,)]),"should be",(0.75,0.25)

    pAB_C = condition1(pABC,2,1)
    print "p(A,B|C): ",dict(pAB_C)
    pAB_C = condition2(pABC,2,1)
    print "p(A,B|C): ",dict(pAB_C)

    pA_BC = condition1(condition1(pABC,2,1),1,1)
    print "p(A|B,C): ",dict(pA_BC)
    pA_BC = condition2(condition2(pABC,2,1),1,1)
    print "p(A|BC): ",dict(pA_BC)

if __name__=='__main__':
    print "###### Problem 1 ######"
    p1()
    raw_input()
    print
    print "###### Problem 2 ######"
    p2()
    raw_input()
    print
    print "###### Problem 4 ######"
    p4()
