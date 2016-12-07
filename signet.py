from z3 import *
from collections import defaultdict

class Signet(object) :
	def __init__(self) :
		self.z3Solver = Solver()
		self.signatures = []

	def program(self) : 
		self.state = 2 # Number of state variables
		self.packetLen = 2 # Number of packet variables
		self.ifBlocks = []

		self.init = ["and", "not", 0, "not", 1]
		
		predicate = ["and", "and", "not", 0, "not", 1, "and", "p", 0, "not", "p", 1] 
		actions = [[0, "not", 0]]
		self.ifBlocks.append([predicate, actions])

		predicate = ["and", "and", 0, "not", 1, "p", 1] 
		actions = [[1, "not", 1]]
		self.ifBlocks.append([predicate, actions])

		self.attackpredicate = ["and", 1, "p", 0]

	def initializeSATVariables(self, siglen) :
		# Initialize variables for extracting siglen length signatures
		self.stateVariables = defaultdict(lambda:defaultdict(lambda:None))
		self.packetVariables = defaultdict(lambda:defaultdict(lambda:None))

		for n in range(0, siglen + 1) :
			for var in range(self.state) : 
				self.stateVariables[var][n] = Bool(str(var)+"-"+str(n))

		for n in range(0, siglen + 1) :
			for var in range(self.packetLen) : 
				self.packetVariables[var][n] = Bool("p"+str(var)+"-"+str(n))

	def generatePredicate(self, predicate, n) :
		self.index = 0
		return self.generateExpression(predicate, n)

	def generateExpression(self, predicate, n) :
		if type(predicate[self.index]) == int : 
			# Variable
			return self.stateVariables[predicate[self.index]][n]
		elif predicate[self.index] == "true" :
			return True
		elif predicate[self.index] == "false" :
			return False
		elif predicate[self.index] == "p" : 
			self.index += 1
			return self.packetVariables[predicate[self.index]][n]
		elif predicate[self.index] == "and" :
			self.index += 1
			lexpr = self.generateExpression(predicate, n)
			self.index += 1
			rexpr = self.generateExpression(predicate, n)
			return And(lexpr, rexpr)
		elif predicate[self.index] == "or" :
			self.index += 1
			lexpr = self.generateExpression(predicate, n)
			self.index += 1
			rexpr = self.generateExpression(predicate, n)
			return Or(lexpr, rexpr)
		elif predicate[self.index] == "not" :
			self.index += 1
			lexpr = self.generateExpression(predicate, n)
			return Not(lexpr)

	def generateAction(self, action, n) :
		# n + 1th state variable depending on state variables of n
		if type(action[0]) != int : 
			print "lvalue not a variable"
			exit(0)

		outputVar = self.stateVariables[action[0]][n+1]
		rexpr = self.generatePredicate(action[1:], n)
		return (outputVar == rexpr)

	def extract(self) :
		self.program()
		for siglen in range(1,5):
			self.z3Solver.reset()
			self.initializeSATVariables(siglen)

			# Initial State
			initExp = self.generatePredicate(self.init, 0)
			self.z3Solver.add(initExp)
			
			# Transitions
			for n in range(siglen - 1) :
				for [predicate, actions] in self.ifBlocks :
					predExp = self.generatePredicate(predicate, n)

					actionExpList = []
					for action in actions :
						actionExpList.append(self.generateAction(action, n))

					actionExp = And(*actionExpList)
					self.z3Solver.add(predExp == actionExp)

			attackExp = self.generatePredicate(self.attackpredicate, siglen - 1)
			self.z3Solver.add(attackExp)

			# Solve for network signature
			modelsat = self.z3Solver.check()

			if modelsat == z3.sat : 
				print "Extracted a signature of length ", siglen
				self.signature(self.z3Solver.model(), siglen)
			else : 
				print "No signatures of length ", siglen

	def signature(self, model, siglen) :
		# Extract Signature from Model 
		signature = []
		for n in range(siglen) :
			packet = ""
			for var in range(self.packetLen) : 
				if is_true(model.evaluate(self.packetVariables[var][n])) : 
					packet = packet + "1"
				elif is_false(model.evaluate(self.packetVariables[var][n])) : 
					packet = packet + "0"  
				else : 
					packet = packet + "*"	
			signature.append(packet)
		
		self.signatures.append(signature)

	def blockingSignature(self, signature, siglen):
		






		



signet = Signet()
signet.extract()