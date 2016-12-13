from z3 import *
import random
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
		self.generateProgram(5,5,5)
		for siglen in range(1,10):
			self.z3Solver.reset()
			self.initializeSATVariables(siglen)

			# Initial State
			initExp = self.generatePredicate(self.init, 0)
			self.z3Solver.add(initExp)
			# print initExp
			# Transitions
			for n in range(siglen - 1) :
				predExpList = []
				for [predicate, actions] in self.ifBlocks :
					predExp = self.generatePredicate(predicate, n)

					actionExpList = []
					for var in range(self.state) : 
						actionExists = False
						for action in actions :
							if action[0] == var:
								actionExpList.append(self.generateAction(action, n))
								actionExists = True
								break

						if not actionExists : 
							actionExpList.append(self.stateVariables[var][n+1] == self.stateVariables[var][n])

					actionExp = And(*actionExpList)
					# print "Action exp", actionExp
					self.z3Solver.add(predExp == actionExp)
					predExpList.append(predExp)

				self.z3Solver.add(Or(*predExpList))

			attackExp = self.generatePredicate(self.attackpredicate, siglen - 1)
			self.z3Solver.add(attackExp)
			# print attackExp

			# Solve for network signature
			modelsat = self.z3Solver.check()

			if modelsat == z3.sat : 
				print "Extracted a signature of length ", siglen
				# print self.z3Solver.model()
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
		print signature	
		self.signatures.append(signature)

	def blockingSignature(self, signature, siglen):
		pass

	def generateProgram(self, stateCount, packetLen, programSize) : 
		self.state = stateCount # Number of state variables
		self.packetLen = packetLen # Number of packet variables
		self.ifBlocks = []

		self.init = self.AndNot(0)

		for i in range(self.state) : 
			statePred = self.shift(0, i)
			j = random.randint(0, packetLen - 1)
			pred = ["and", "p", j]
			pred.extend(statePred)
			actions = [[i, "true"]]	
			self.ifBlocks.append([pred, actions])
			print pred, actions

		self.attackpredicate = self.And(0)

	def And(self, pos) :
		if pos >= self.state :  
			return ["true"]
		elif pos == self.state - 1 :
			return [self.state - 1]
		else : 
			exp = ["and", "and", pos, pos + 1]
			exp.extend(self.And(pos + 2))
			return exp

	def AndNot(self, pos) :
		if pos >= self.state :  
			return ["true"]
		elif pos == self.state - 1 :
			return ["not", self.state - 1]
		else : 
			exp = ["and", "and", "not", pos, "not", pos + 1]
			exp.extend(self.AndNot(pos + 2))
			return exp

	def shift(self, pos, neg) :
		if pos >= self.state :  
			return ["true"]
		elif pos == self.state - 1 :
			if pos >= neg : 
				return ["not", self.state - 1]
			else : 
				return [self.state - 1]
		else : 
			if pos >= neg : 
				exp = ["and", "and", "not", pos, "not", pos + 1]
			elif pos + 1 >= neg : 
				exp = ["and", "and", pos, "not", pos + 1]
			else : 
				exp = ["and", "and", pos, pos + 1]
			exp.extend(self.shift(pos + 2, neg))
			return exp
		


signet = Signet()
signet.extract()