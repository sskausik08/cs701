from z3 import *
from collections import defaultdict

class Signet(object) :
	def __init__(self) :
		self.z3Solver = Solver()


	def program(self) : 
		self.state = 2 # Number of state variables

		self.ifBlocks = []

	
		predicate = ["and", "or", 0, 1, "not", 1] 
		actions = [[1, "and", 0, 1], [0, "true"]]



	def initializeSATVariables(self, siglen) :
		# Initialize variables for extracting siglen length signatures
		self.stateVariables = defaultdict(lambda:defaultdict(lambda:None))

		for n in range(1, siglen + 1) :
			for var in range(self.state) : 
				self.stateVariables[var][n] = Bool(str(var)+"-"+str(n))



	def generatePredicate(self, predicate, n):
		index = 0

		
	def extractExpression(self, predicate, n) :
		if type(predicate[self.index]) == int : 
			# Variable
			return self.stateVariables[predicate[self.index]][n]
		elif predicate[self.index] == "and" :
			self.index += 1
			lexpr = self.extractExpression(predicate, n)
			self.index += 1
			rexpr = self.extractExpression(predicate, n)
			return And(lexpr, rexpr)
		elif predicate[self.index] == "or" :
			self.index += 1
			lexpr = self.extractExpression(predicate, n)
			self.index += 1
			rexpr = self.extractExpression(predicate, n)
			return Or(lexpr, rexpr)
		elif predicate[self.index] == "not" :
			self.index += 1
			lexpr = self.extractExpression(predicate, n)
			return Not(lexpr)

	def extractAction(self, action, n) :
		# n + 1th state variable depending on state variables of n
		if type(action[0]) != int : 
			print "lvalue not a variable"
			exit(0)

		outputVar = self.stateVariables[action[0]][n+1]
		self.index = 1 # 0th element is lvar
		rexpr = self.extractExpression(action, n)
		return (outputVar == rexpr)

	def extract(self) :
		self.program()
		self.initializeSATVariables(5)
		self.index = 0
		print self.extractAction([1, "and", "and", "or", 0, 1, "not", 1, "and", 0, 1], 2)


signet = Signet()
signet.extract()