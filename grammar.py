import fileinput
import random
import re
import subprocess
from optparse import OptionParser
from lark import Lark, Transformer, exceptions, Token, ParseTree
from collections import defaultdict

class Graph:
	def __init__(self):
		self.graph = defaultdict(list)	
		self.Time = 0
		self.V=0
	def addVertex(self, v):
		if v not in self.graph:
			self.graph[v] = []
			self.V+=1
	def addEdge(self, u, v):
		self.addVertex(u)
		self.addVertex(v)
		self.graph[u].append(v)
	def SCCUtil(self, u, low, disc, stackMember, st):
		disc[u] = self.Time
		low[u] = self.Time
		self.Time += 1
		stackMember[u] = True
		st.append(u)
		for v in self.graph[u]:
			if disc[v] == -1:
				self.SCCUtil(v, low, disc, stackMember, st)
				low[u] = min(low[u], low[v])
			elif stackMember[v] == True:
				low[u] = min(low[u], disc[v])
		w = -1
		length=0
		if low[u] == disc[u]:
			while w != u:
				length+=1
				w = st.pop()
				stackMember[w] = False
		if(length>1):
			raise ValueError("Cyclic dependency detected")
	def SCC(self):
		disc = [-1] * (self.V)
		low = [-1] * (self.V)
		stackMember = [False] * (self.V)
		st = []
		for i in range(self.V):
			if disc[i] == -1:
				self.SCCUtil(i, low, disc, stackMember, st)

entities = {} #dizionario con chiave nome dell'entità e valore la lista dei parametri e rispettivi tipi
guess={} #dizionario di alias ed entità del primo from del guess
guess_alias={} #dizionario dei nuovi alias delle entità interne al guess
guess_entities={} #dizionario di tutte le entità e alias del costrutto guess
number=0
g=Graph()
num_pred={}
num=0
recursive=False

grammar = """
	start:  _statement+
	_statement: entity | define | guess | assert_ | deny_ | try_assert | try_deny
	entity: "@entity" entity_declaration SEMICOLON
	entity_declaration: ENTITY_NAME COLON declarations
	declarations: declaration (COMMA declaration)*
	declaration: NAME COLON attr_type
	define: def_1 | def_2 | def_3
	def_1: define_definition define_from? define_where
	def_2: define_definition define_from? aggregate define_where
	def_3: define_definition define_from? aggregate SEMICOLON
	define_definition: "define" ENTITY_NAME as_statement?
	as_statement: "as" NAME
	define_from: "from" define_entity (COMMA define_entity)*
	define_entity: NOT? ENTITY_NAME ("as" NAME)?
	define_where: "where" where_define_statement (AND where_define_statement)* SEMICOLON
	where_define_statement: (NAME | ENTITY_NAME) (DOT NAME)* (operator | ASSIGN) var_define
	guess: guess_def_1 | guess_def_2
	guess_def_1: "guess" from_guess where_guess? guess_times? guess_definitions SEMICOLON
	guess_def_2: "guess" from_guess guess_aggregate where_guess? guess_times? guess_definitions SEMICOLON
	from_guess: "from" guess_entity (COMMA guess_entity)*
	guess_entity: NOT? ENTITY_NAME ("as" NAME)?
	where_guess: "where"  where_guess_statement (AND where_guess_statement)*
	where_guess_statement: (NAME | ENTITY_NAME) (DOT NAME)* ((operator | ASSIGN) var_guess)
	guess_times: times (INT| times_value) (AND guess_times)*
	guess_definitions: guess_definition+
	guess_definition: ENTITY_NAME ("as" NAME)? guess_declaration
	guess_declaration: guess_from? guess_where
	guess_from: "from" entity_guess (COMMA entity_guess)*
	entity_guess: NOT? ENTITY_NAME ("as" NAME)?
	guess_where: "where"  guess_where_statement (AND guess_where_statement)*
	guess_where_statement: (NAME | ENTITY_NAME) (DOT NAME)* (operator | ASSIGN) var_guess_2
	assert_: assert_statement SEMICOLON
	deny_: deny SEMICOLON
	assert_statement: assert_1 | assert_2 | assert_3
	assert_1: assert_definition assert_from? where_assert
	assert_2: assert_definition assert_from? aggregate where_assert
	assert_3: assert_definition assert_from? aggregate
	assert_definition: "deny unless" assert_entities (OR assert_entities)*
	assert_entities: ENTITY_NAME ("as" NAME)?
	assert_from: "from" assert_entity (COMMA assert_entity)*
	assert_entity: NOT? ENTITY_NAME ("as" NAME)?
	where_assert: "where" where_assert_statement (AND where_assert_statement)*
	where_assert_statement: (NAME | ENTITY_NAME) (DOT NAME)* (operator | ASSIGN) var
	deny: deny_1 | deny_2
	deny_1: "deny" deny_from aggregate? where_deny
	deny_2: "deny" deny_from aggregate
	deny_from: "from" deny_entity (COMMA deny_entity)*
	deny_entity: NOT? ENTITY_NAME ("as" NAME)?
	where_deny: "where" where_deny_statement (AND where_deny_statement)*
	where_deny_statement: (NAME | ENTITY_NAME) (DOT NAME)* (operator | ASSIGN) var
	try_assert: assert_otherwise "or" pay_statement SEMICOLON
	assert_otherwise: assert_otherwise_1 | assert_otherwise_2 | assert_otherwise_3
	assert_otherwise_1: assert_definition assert_from? where_assert
	assert_otherwise_2: assert_definition assert_from? aggregate where_assert
	assert_otherwise_3: assert_definition assert_from? aggregate
	pay_statement: "pay" (INT | pay | arithmetic_operation) "at" (INT | pay | arithmetic_operation)
	try_deny: deny_otherwise "or" pay_statement SEMICOLON
	deny_otherwise: deny_otherwise_1 | deny_otherwise_2
	deny_otherwise_1: "deny" deny_from aggregate? where_deny
	deny_otherwise_2: "deny" deny_from aggregate
	pay: (NAME | ENTITY_NAME) (DOT NAME)+
	arithmetic_operation: (pay | INT) (SUM | MINUS) (pay | INT)
	guess_aggregate: aggr_def_guess (AND aggr_def_guess)*
	aggr_def_guess: (COUNT | SUM_OF | MIN | MAX) "{" aggr_body_guess (SEMICOLON aggr_body_guess)* "}" operator (aggregate_term_guess | INT)
	aggr_body_guess: aggr_body_guess1 | aggr_body_guess2
	aggr_body_guess1: aggr_entities_guess aggregate_from_guess? aggr_where_guess
	aggr_body_guess2: aggr_entities_guess aggregate_from_guess?
	aggr_entities_guess: (aggregate_entity|INT) (COMMA (aggregate_entity|INT))*
	aggregate_from_guess: "from" aggr_entity_guess (COMMA aggr_entity_guess)*
	aggr_entity_guess: NOT? ENTITY_NAME ("as" NAME)?
	aggr_where_guess: "where" where_aggr_guess (AND where_aggr_guess)*
	where_aggr_guess: (NAME | ENTITY_NAME) (DOT NAME)+ (operator | ASSIGN) var_guess
	aggregate_term_guess: (NAME | ENTITY_NAME) (DOT NAME)*
	aggregate: aggr_def (AND aggr_def)*
	aggr_def: (COUNT | SUM_OF | MIN | MAX) "{" aggr_body (SEMICOLON aggr_body)* "}" operator (aggregate_term | INT)
	aggr_body: aggr_body_1 | aggr_body_2
	aggr_body_1: aggr_entities aggregate_from? aggr_where
	aggr_body_2: aggr_entities aggregate_from?
	aggr_entities: (aggregate_entity|INT) (COMMA (aggregate_entity|INT))*
	aggregate_from: "from" aggr_entity (COMMA aggr_entity)*
	aggr_entity: NOT? ENTITY_NAME ("as" NAME)?
	aggr_where: "where" where_aggr_statement (AND where_aggr_statement)*
	where_aggr_statement: (NAME | ENTITY_NAME) (DOT NAME)* (operator | ASSIGN) var_aggr_define
	aggregate_entity: (NAME | ENTITY_NAME) (DOT NAME)*
	aggregate_term: (NAME | ENTITY_NAME) (DOT NAME)*
	var_guess:  INT | STR | value_guess
	value_guess: (NAME | ENTITY_NAME) (DOT NAME)*
	times_value: (NAME | ENTITY_NAME) (DOT NAME)+
	value: (NAME | ENTITY_NAME) (DOT NAME)*
	var_guess_2:  INT | STR | value_guess_2
	var: INT | STR | value
	value_guess_2: (NAME | ENTITY_NAME) (DOT NAME)*	
	var_define: INT | STR | value_define
	var_aggr_define: INT | STR | value_aggr_define
	value_aggr_define: (NAME | ENTITY_NAME) (DOT NAME)*	
	value_define: (NAME | ENTITY_NAME) (DOT NAME)*	
	operator: EQUALITY | LT | LE | GT | GE | NOTEQUAL
	bool_operator: AND | OR
	times: EXACTLY | ATLEAST | ATMOST
	attr_type: ANY | STRING | INTEGER | ENTITY_NAME | REGEX
	REGEX: "r"/"[^"]+"/
	NAME: /[a-z_][a-z0-9_]*/
	ENTITY_NAME: /[A-Z][a-zA-Z0-9_]*/
	COLON: ":"
	SEMICOLON: ";"
	COMMA: ","
	DOT: "."
	ASSIGN: "="
	SUM: "+"
	MINUS: "-"
	OPEN_BRACKET: "("
	CLOSED_BRACKET: ")"
	EQUALITY: "=="
	NOTEQUAL: "!="
	GE: ">="
	GT: ">"
	LT: "<"
	LE: "<="
	AND: "and"
	NOT: "not"
	OR: "or"
	COUNT: "count of"
	SUM_OF: "sum of"
	EXACTLY: "exactly"
	ATLEAST: "at_least"
	ATMOST: "at_most"
	ANY: "any"
	STRING: "str"
	INTEGER: "int"
	MAX: "max of"
	MIN: "min of"
	STR: /"[^"]*"/
	INT: /[0-9]+/
	%import common.WS
	%ignore WS
"""

class DeclarationTransformer(Transformer):
	def __init__(self):
		self.count_guess=0
		self.count=0
		guess[0]=[]
		guess_alias[0]={}
		guess_entities[0]={}
		guess_alias[0]["number"]=0
	def entity_declaration(self, args):
		entity_name= args[0]
		declarations=args[2].children
		if(entity_name in entities.keys()):
			raise ValueError(f"Entity already defined: {entity_name}")
		entities[entity_name]=[]
		for i in range(0, len(declarations), 2): #per ogni entità dichiarata
			attr=declarations[i].children
			token=attr[2].children
			attr_type=token[0] 
			if(attr_type==entity_name): #si definisce come tipo dell'attributo l'entità stessa
				raise ValueError("Invalid syntax")
			attr[0].type=str(attr_type) #salvo il tipo dell'attributo nel token
			entities[entity_name].append(attr[0]) #aggiungo nella lista degli attributi
		return args
	def guess(self, args):
		self.count_guess+=1
		guess[self.count_guess]=[]
		guess_entities[self.count_guess]={}
		guess_alias[self.count_guess]={}
		guess_alias[self.count_guess]["number"]=0
	def guess_definition(self, args):
		if(len(args)>=3):
			if(args[1] in guess_entities[self.count_guess].keys()):
				raise ValueError(f"Alias already defined: {args[1]}")
			guess_alias[self.count_guess][args[1]]=self.add_number(args[1])
			guess_entities[self.count_guess][args[1]]=args[0]
		else:
			if(args[0] in guess_entities[self.count_guess].keys()):
				raise ValueError(f"Entity already defined: {args[0]}")
			guess_alias[self.count_guess][args[0]]=self.number(args[0])
			guess_entities[self.count_guess][args[0]]=args[0]
		guess_alias[self.count_guess]["number"]+=1
	def guess_entity(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		if(len(args)>index+1):
			if(args[index+1] in guess_entities[self.count_guess].keys()):
				raise ValueError(f"Alias already defined: {args[index+1]}")
			guess_entities[self.count_guess][args[index+1]]=args[index]
			guess[self.count_guess].append(args[index+1])
		else:
			if(args[index] in guess_entities[self.count_guess].keys()):
				raise ValueError(f"Entity already defined: {args[index]}")
			guess_entities[self.count_guess][args[index]]=args[index]
			guess[self.count_guess].append(args[index])
	def entity_guess(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		if(len(args)>index+1):
			if(args[index+1] in guess_entities[self.count_guess].keys()):
				raise ValueError(f"Alias already defined: {args[index+1]}")
		else:
			if(args[index] in guess_entities[self.count_guess].keys()):
				raise ValueError(f"Entity alreaddy defined: {args[index]}")
	def number(self, args):
		letter=args[0].lower()
		letter+="_"+f"{self.count}"
		self.count+=1
		return letter
	def add_number(self, args):
		args=args+"_"+f"{self.count}"
		self.count+=1
		return args


class CheckTransformer(Transformer):
	def __init__(self):
		self.declared_alias={} #dizionario degli alias dichiarati nel from di ogni define e con valore l'entità
		self.defined_entities=set() #entità definite nel from di ogni define
		self.attributes={} #dizionario con chiave l'entità/l'alias e valore la lista degli attributi, inizializzato ad ogni define
		self.defined_entity=set() #entità definita nella define
		self.redefined_entity={} #alias dell'entità definita nella define
		self.new_define_alias={} #nuovi alias del costrutto define con chiave l'alias/entità
		self.new_guess_alias={} #nuovi alias del costrutto guess con chiave l'alias/entità
		self.guess_alias={} #alias del costrutto guess
		self.guess_entities=set() #entità del costrutto guess
		self.count_guess=0 #numero progressivo per gli alias del guess
		self.guess_count=guess_alias[0]["number"] #numero da cui partire per gli alias del guess
		self.count_define=0 #numero progressivo per gli alias della define
		self.dependencies={}
		self.guess_check=[] #per controllare che le entità e alias utlizzati nel secondo where del guess siano quelle previste
		#variabili utilizzate all'interno del with statement
		self.dep={}
		self.all_dependencies=[]
		self.statement=""
		self.condition=""
		self.otherwise_en=[]
		self.guess_condition=[] #condizioni che vanno inserite direttamente nel with
		self.guess_condition_args={}
		self.define_condition=[] #condizioni da inserire nel with
		self.define_condition_args={}
		self.aggregate_entities=set()	
		self.aggr_alias=[] #alias e entità da togliere per non farle riconoscere nel where della define / assert / ecc..
		self.aggr_new_alias={}
		self.aggregate_with=[]
		self.entities_attributes=[]
		self.negated_atoms=[]
		self.problem=random.randint(0,100)
		global number
		number=self.problem
	def start(self, args):
		atoms=[atom for atom in args if atom.startswith("@atom")]
		others=[other for other in args if other not in atoms]
		ordered_atoms = []
		ordered=[]
		ordered.append("from pyspel.pyspel import *\n\n")
		length=len(ordered)
		while len(ordered) - 1 < len(atoms):
			for atom in atoms:
				if atom not in ordered:
					name = atom.split("class ")[1].split(":")[0]
					if not self.dependencies[name]:
						ordered.append(atom)
						ordered_atoms.append(name)
					else:
						all_dependencies_met = all(dep in ordered_atoms for dep in self.dependencies[name])
						if all_dependencies_met:
							ordered.append(atom)
							ordered_atoms.append(name)
			if(len(ordered)==length):
				raise ValueError("Circular dependencies detected between entities")
			else:
				length+=1
		ordered.append(f"\nproblem{self.problem} = Problem()\n\n")
		ordered.extend(others)
		return "".join(ordered)	
	def entity(self, args):	
		self.entities_attributes=[]
		return f"@atom\n{args[0]}\n"
	def entity_declaration(self, args):
		self.dependencies[args[0]]=self.entities_attributes
		return f"class {args[0]}:\n{args[2]}"
	def declarations(self, args):
		statements=""
		for i in range(0, len(args)):
			if(args[i]==","):
				statements+="\n"
			else:
				statements+=f"{args[i]}"
		return statements
	def declaration(self, args):
		if(args[2] in entities.keys()):
			self.entities_attributes.append(args[2])
		return f"	{args[0]}: {args[2]}"
	def attr_type(self, args):
		return args[0]
	def define(self, args):
		return args[0]
	def def_1(self, args):
		when=""
		if(len(args)>2):
			when=self.when_define(args[1])
		self.check_statement(args)
		self.init_define_variables()
		if(len(args)>2):
			return f"with {self.statement}:\n{when}{args[2]}"
		stat=f"	problem{self.problem}+=When("
		stat+=args[1][2:]
		return f"with {self.statement}:\n{stat}"
	def def_2(self, args):
		when=""
		if(len(args)>3):
			when=self.when_define(args[1])
		self.statement=""
		for aggr in self.aggregate_with:
			args[0]+=", "+aggr
		self.find_pattern(args)
		if(self.aggregate_with!=[]):
			self.addEdge(self.aggregate_with)
		self.define_condition=[]
		self.init_define_variables()
		if(len(args)>3):
			return f"with {self.statement}:\n{when}, {args[2]}{args[3]}"
		stat=f"	problem{self.problem}+=When("
		return f"with {self.statement}:\n{stat}{args[1]}{args[2]}"
	def def_3(self, args):
		when=""
		if(len(args)>3):
			when=self.when_define(args[1])
		self.statement=""
		for aggr in self.aggregate_with:
			args[0]+=", "+aggr
		self.find_pattern(args)
		if(self.aggregate_with!=[]):
			self.addEdge(self.aggregate_with)
		self.define_condition=[]
		stat2=""
		for alias in self.new_define_alias.keys():
			stat2=f").define({self.new_define_alias[alias]})\n"
			break
		self.init_define_variables()
		if(len(args)>3):
			return f"with {self.statement}:\n{when}, {args[2]}{stat2}"
		stat=f"	problem{self.problem}+=When("
		return f"with {self.statement}:\n{stat}{args[1]}"+stat2
	def addEdge(self, args):
		pred_define=""
		for alias in self.redefined_entity.values():
			pred_define=alias
		for en in self.defined_entity:
			pred_define=en
		global g, recursive
		self.increment_num(pred_define)
		for arg in args:
			if("()" in arg):
				pred=arg.split("()")[0]
				if(recursive and pred==pred_define):
					raise ValueError("Cyclic dependency detected")
				self.increment_num(pred)
				g.addEdge(num_pred[pred], num_pred[pred_define])
	def addEdge_guess(self, args, pred_guess):
		global g, recursive
		self.increment_num(pred_guess)
		splitted=args.split("()")[:-1]
		for split in splitted:
			en=""
			if("," in split):
				en=split.split(", ")[1]
			else:
				en=split
			if(recursive and en==pred_guess):
				raise ValueError("Cyclic dependency detected")
			self.increment_num(en)
			g.addEdge(num_pred[en], num_pred[pred_guess])
	def define_from(self, args):
		self.addEdge(args)
		return ", "+self.print_stat(args)
	def when_define(self, args):
		statement=f"	problem{self.problem}+=When("
		pattern = r'as\s+([a-zA-Z0-9_]+)(?:,|$)'
		match = re.findall(pattern, args)
		if match:
			for var in match:
				if(var in self.negated_atoms):
					statement+="~"
				statement+=var+", "
		return statement[:-2]
	def define_where(self, args):
		statements=""
		for i in range(len(args)):
			if(not args[i]==";" and not args[i]=="and"):
				statements+=f"{args[i]}"
		for alias in self.new_define_alias.keys():
			return statements + f").define({self.new_define_alias[alias]})\n"
	def define_definition(self, args):
		self.declared_alias={}
		self.defined_entities=set()
		if(not args[0] in entities.keys()):
			 raise ValueError(f"Undefined entity: {args[0]}")
		self.attributes={}
		attr=entities[args[0]]
		all_attr=[]
		for i in range(len(attr)):
			all_attr.append(attr[i]) 
		self.attributes[args[0]]=all_attr
		if(len(args)>1):
			self.redefined_entity[args[1]]=args[0]
			alias=self.add_number(args[1])
			self.new_define_alias[args[1]]=alias
			return f"{args[0]}() as {alias}"
		self.defined_entity.add(args[0])
		alias=self.number(args[0])
		self.new_define_alias[args[0].value]=alias
		return f"{args[0]}() as {alias}"
	def as_statement(self, args):
		return f"{args[0]}"
	def define_entity(self, args):
		negated=False
		if(args[0]=="not"):
			negated=True
			args=args[1:]
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		var=""
		if(len(args)>1): #se è stato definito l'alias aggiungo in declared_alias altrimenti in defined_entities
			if(args[1] in self.declared_alias or args[1] in self.redefined_entity.keys()):
				raise ValueError(f"Alias already defined: {args[1]}")
			self.declared_alias[args[1]]=args[0]
			var=args[1]
		else:
			if(args[0] in self.defined_entities or args[0] in self.defined_entity):
				raise ValueError(f"Entity already defined: {args[0]}")
			self.defined_entities.add(args[0])
			var=args[0]
		attr=entities[args[0]]
		all_attr=[]
		for i in range(len(attr)):
			all_attr.append(attr[i]) 
		self.attributes[var]=all_attr #lista degli attributi dell'entità
		if(len(args)>1):
			alias=self.add_number(args[1])
			self.new_define_alias[args[1].value]=alias
			if(negated):
				self.negated_atoms.append(alias)
			return f"{args[0]}() as {alias}"
		alias=self.number(args[0])
		self.new_define_alias[args[0].value]=alias
		if(negated):
			self.negated_atoms.append(alias)
		return f"{args[0]}() as {alias}"
	def var(self, args):
		if(isinstance(args[0], Token)):
			args[0]+=f"/{args[0].type.lower()}"
		return self.print_stat(args)
	def value(self, args):
		statement=""
		entity=args[0]
		if(not (args[0] in self.defined_entity or args[0] in self.redefined_entity.keys())):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		attribute=self.attributes_check(args)
		if(args[0] in self.new_define_alias.keys()):
			args[0]=self.new_define_alias[args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement + "/" + attribute
	def var_define(self, args):
		if(isinstance(args[0], Token)):
			args[0]+=f"/{args[0].type.lower()}"
		return self.print_stat(args)
	def var_aggr_define(self, args):
		return self.var_define(args)
	def value_def(self, args):
		statement=""
		entity=args[0]
		attribute=self.attributes_check(args)
		if(args[0] in self.new_define_alias.keys()):
			args[0]=self.new_define_alias[args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement + "/" + attribute
	def value_aggr_define(self, args):
		if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		return self.value_def(args)
	def value_define(self, args):
		if(not (args[0] in self.redefined_entity.keys() or args[0] in self.defined_entity)):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		return self.value_def(args)
	def var_guess(self, args):
		if(isinstance(args[0], Token)):
			args[0]+=f"/{args[0].type.lower()}"
		return self.print_stat(args)
	def value_guess(self, args):
		if(not args[0] in guess_entities[self.count_guess].keys()):
			raise ValueError(f"{args[0]} is not defined")
		return self.value_guess_check(args)
	def value_guess_check(self, args):
		statement=""
		attribute=self.attributes_guess_check(args)
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		elif(args[0] in guess_alias[self.count_guess].keys()):
			args[0]=guess_alias[self.count_guess][args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement+ "/" + attribute
	def times_value(self, args):
		statement=""
		if not (args[0] in  guess_entities[self.count_guess].keys()):
				raise ValueError(f"Entity not defined: {args[0]}")
		attribute=self.attributes_guess_check(args)
		if(attribute!="int" and attributes!="any"): #any?
			raise ValueError(f"Expected int, received {attribute}: {statements}")
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		elif(args[0] in guess_alias[self.count_guess].keys()):
			args[0]=guess_alias[self.count_guess][args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement
	def var_guess_2(self, args):
		return self.var_guess(args)
	def value_guess_2(self, args):
		if not (args[0] in self.guess_alias.keys() or args[0] in self.guess_entities or args[0] in guess_entities[self.count_guess].keys()):
			raise ValueError(f"{args[0]} is not defined")
		return self.value_guess_check(args)
	def where_statement_check(self,args):
		attribute=self.attributes_check(args)
		statement=", "
		types=args[-1].split("/")
		if(not types[1]==attribute and attribute!="any"):
			if(args[-2]!="="):
				raise ValueError(f"{types[1]} cannot be compared with type: {attribute}")
			raise ValueError(f"{types[1]} cannot be assigned to type {attribute}")
		if(args[0] in self.new_define_alias.keys()):
			args[0]=self.new_define_alias[args[0]]
		if(len(args)<=3):
			temp_array=[]
			if("." in types[0]):
				splitted=types[0].split(".")
				for split in splitted:
					temp_array.append(split)
					temp_array.append(".")
				temp_array.pop()
			else:
				temp_array.append(types[0])
			temp_array.append(args[-2])
			temp_array.append(args[0])
			args=temp_array
		else:
			args[-1]=types[0]
		if(attribute!="str" and attribute!="int" and attribute!="any"):
			if(args[-2]!="=" or not "." in types[0] and not "." in args):
				raise TypeError(f"Cannot compare objects of these types: {attribute}")
			c=f"{args[2]} {self.print_stat(args[3:])}"
			self.define_condition.append(args[0])
			self.define_condition.append(c)
			self.define_condition.append(args[-1])
			if("." in c.split("=")[0]):
				self.define_condition_args[c]=args
				entity=self.define_condition_args[c][0]
				for k,v in self.new_define_alias.items():
					if(v==entity):	
						if(k in entities.keys()):
							self.define_condition_args[c][0]=k
						else:
							self.define_condition_args[c][0]=self.declared_alias[k]
			return ""
		for i in range(len(args)):
			if(args[i]=="="):
				statement+="=="
			else:
				statement+=f"{args[i]}"
		return statement
	def where_define_statement(self, args):
		entity=args[0]
		if(args[0] in self.aggr_alias):
			raise ValueError(f"{args[0]} is not defined")
		if("." in args[-1]):
			en=args[-1].split(".")[0]
			if(en in self.aggr_new_alias.keys()):
				raise ValueError(f"{self.aggr_new_alias[en]} is not defined")
		else:
			en=args[-1].split("/")[0]
			if(en in self.aggr_new_alias.keys()):
				raise ValueError(f"{self.aggr_new_alias[en]} is not defined")
		if(not (args[0] in self.redefined_entity.keys() or args[0] in self.defined_entity)):
			if(not args[0] in self.declared_alias.keys() and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		return self.where_statement_check(args)	
	def guess_aggregate(self, args):
		return self.aggregate(args)	
	def aggregate(self, args):
		stat=""
		for i in range(len(args)):
			if(args[i]=="and"):
				args[i]=", "
			stat+=f"{args[i]}"
		return stat
	def aggr_where_guess(self, args):
		return self.remove_and(args)
	def aggr_where(self,args):
		return self.remove_and(args)
	def where_aggr_guess(self,args):
		if not (args[0] in self.guess_entities or args[0] in self.guess_alias.keys()):
			raise ValueError(f"{args[0]} is not defined")
		statement=", "
		args=self.guess_where_check(args)
		if(args==""):
			return args
		for i in range(len(args)):
			if(args[i]=="="):
				args[i]="=="
			statement+=f"{args[i]}"
		return statement	
	def where_aggr_statement(self, args):
		entity=args[0]
		if(not (args[0] in self.redefined_entity.keys() or args[0] in self.defined_entity)):
			if not (args[0] in self.declared_alias.keys() or args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		return self.where_statement_check(args)
	def check_sum(self, all_en, declared_alias):
		sum_bool=""
		if(isinstance(all_en,Token) and all_en.type=="INT"):
			sum_bool="True/"
		else:
			sum_bool="False/"+f"{all_en}"
			attribute=""
			if("." in all_en):
				en=all_en.split(".")[0]
				if(en in declared_alias.keys()):
					attribute=declared_alias[en]
				else:
					attribute=en
				temp_array=all_en.split(".")[1:]
				for i in range(len(temp_array)):		
					found=False
					for t in entities[attribute]:
						if(t.value==temp_array[i]):
							attribute=t.type
							found=True
							break
				if(attribute=="int"):
					sum_bool="True/"
		return sum_bool
	def aggregate_body(self, args, new_alias, declared_alias):
		self.aggregate_entities=set()
		sum_bool=self.check_sum(args[0][0][0], declared_alias)
		stat="("
		for attr in args[0][0]:
			if(attr!=","):
				if("." in attr):
					temp=attr
					splitted=temp.split(".")
					alias=splitted[0]
					attr=f"{new_alias[alias]}.{'.'.join(splitted[1:])}"
				elif(attr in new_alias.keys()):
					attr=new_alias[attr]	
				stat+=attr
			else:
				stat+=", "
		if(len(args[0])<=1):
			stat+="):()"
		else:
			stat+="):"
			stat_alias=""
			if(len(args[0])>2 or " as " in args[0][1]):
				comma=[]
				comma=args[0][1].split(",")	
				if(comma==[]):
					alias=args[0][1].split("as ")[1]
					if(alias in self.negated_atoms):
						stat_alias+="~"
					stat_alias+=alias
				else:
					for commas in comma:
						alias=commas.split("as ")[1]
						if(stat_alias!=""):
							stat_alias+=", "
						if(alias in self.negated_atoms):
							stat_alias+="~"
						stat_alias+=alias
			stat+="("+stat_alias
			if(len(args[0])>2):
				stat+=f"{args[0][2]}"
			elif(not " as " in args[0][1]):
				stat+=f"{args[0][1][2:]}"
			stat+=")"
		return stat + "/"+sum_bool
	def aggr_body_guess(self, args):
		return self.aggregate_body(args, self.new_guess_alias, self.guess_alias)
	def aggr_body(self,args):
		return self.aggregate_body(args, self.new_define_alias, self.declared_alias)
	def aggr_body_guess1(self, args):
		if(len(args)<=2):
			self.aggregate_check(args,self.guess_alias, self.guess_entities)
		else:
			length=len(self.aggregate_with)
			self.aggregate_with+=args[1].split(",")
			if(length==len(self.aggregate_with)):
				self.aggregate_with+=args[1]
		return args
	def aggr_body_1(self, args):
		if(len(args)<=2):
			self.aggregate_check(args,self.declared_alias, self.defined_entities)
		else:
			length=len(self.aggregate_with)
			self.aggregate_with+=args[1].split(",")
			if(length==len(self.aggregate_with)):
				self.aggregate_with+=args[1]
		return args
	def aggr_body_guess2(self, args):
		if(len(args)>1):
			length=len(self.aggregate_with)
			self.aggregate_with+=args[1].split(",")
			if(length==len(self.aggregate_with)):
				self.aggregate_with+=args[1]
		else:
			self.aggregate_check(args, self.guess_alias, self.guess_entities)
		return args
	def aggr_body_2(self, args):
		if(len(args)>1):
			length=len(self.aggregate_with)
			self.aggregate_with+=args[1].split(",")
			if(length==len(self.aggregate_with)):
				self.aggregate_with+=args[1]
		else:
			self.aggregate_check(args, self.declared_alias, self.defined_entities)
		return args
	def aggr_entities_guess(self, args):
		return args
	def aggr_entities(self, args):
		return args
	def aggr_def_guess(self, args):
		return self.aggr_def(args)
	def aggr_def(self,args):
		stat=""
		stop=False
		for i in range(1, len(args)-2):
			if(args[i]=="=="):
				stop=True
			if(not stop and args[i]!=";"):
				bool_sum=args[i].split("/")
				if(args[0]!="count of" and bool_sum[1]!="True"):	
					raise ValueError(f"Expected int, received {bool_sum[2]}")
				args[i]=bool_sum[0]
			if(args[i]==";"):
				args[i]=", "
			stat+=args[i]
		stat+="})"+f"{args[-2]}{args[-1]}"
		function=""
		if(args[0]=="count of"):
			function="Count"
		elif(args[0]=="min of"):
			function="Min"
		elif(args[0]=="max of"):
			function="Max"
		else:
			function="Sum"
		return function+"({"+f"{stat}"
	def aggregate_term(self, args):
		return self.pay(args)
	def aggregate_check(self, args, declared_alias, defined_entities):
		for en in self.aggregate_entities:
			all_en=""
			attribute=""
			if("." in en):
				all_en=en
				en=en.split(".")[0]
			if not (en in declared_alias.keys() or en in defined_entities):
				raise ValueError(f"Undefined entity: {en}")
			if(all_en!=""):	
				if(en in declared_alias.keys()):
					attribute=declared_alias[en]
				else:
					attribute=en
				temp_array=all_en.split(".")[1:]
				for i in range(len(temp_array)):
					if(attribute=="str" or attribute=="int"):
						raise ValueError(f"{attribute} object has not attribute {temp_array[i]}")		
					found=False
					for t in entities[attribute]:
						if(t.value==temp_array[i]):
							attribute=t.type
							found=True
							break
					if not found:
						raise ValueError(f"{attribute} object has not attribute {temp_array[i]}")		
	def aggregate_entity(self, args):
		stat="".join(args)
		self.aggregate_entities.add(stat)
		return stat
	def aggregate_from_guess(self, args):
		self.aggregate_check(args, self.guess_alias, self.guess_entities)
		return self.print_stat(args)
	def aggregate_from(self,args):
		self.aggregate_check(args, self.declared_alias, self.defined_entities)
		return self.print_stat(args)
	def aggr_entity_guess(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		global g, recursive
		self.increment_num(args[index])
		for alias in guess_alias[self.count_guess].keys():
			if(alias!="number"):
				en=guess_entities[self.count_guess][alias]
				if(recursive and en==args[index]):
					raise ValueError("Cyclic dependency detected")
				self.increment_num(en)
				g.addEdge(num_pred[args[index]], num_pred[en])
		if(len(args)>index+1):
			self.aggr_alias.append(args[index+1])
		else:
			self.aggr_alias.append(args[index])
		return_value=self.guess_entity(args)
		if(len(args)>index+1):	
			self.aggr_new_alias[self.new_guess_alias[args[index+1]]]=args[index+1]
		else:
			self.aggr_new_alias[self.new_guess_alias[args[index]]]=args[index]
		return return_value
	def aggr_entity(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		if(len(args)>index+1):
			self.aggr_alias.append(args[index+1])
		else:
			self.aggr_alias.append(args[index])
		return_value=self.define_entity(args)
		if(len(args)>index+1):	
			self.aggr_new_alias[self.new_define_alias[args[index+1]]]=args[index+1]
		else:
			self.aggr_new_alias[self.new_define_alias[args[index]]]=args[index]
		return return_value	
	def guess(self,args):
		return args[0]
	def guess_def(self, args, index):
		length=index
		self.statement=""
		self.condition=""
		self.all_condition=[]
		cond=""
		pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
		if(len(args)==length+1):
			index-=1
		elif(len(args)==length):
			index-=2
		self.dep={}
		match = re.findall(pattern, args[0])
		if match:
			for var in match:
				self.with_statement(var, self.guess_condition)
		pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)((.*?)/(.*?))\\'
		match = re.findall(pattern, args[index])
		if match:
			for var in match:
				self.with_statement(var, self.guess_condition)
				cond+=f"{var[2]}:("
				pattern2 = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
				match2 = re.findall(pattern2, var[3])
				if match2:
					for var2 in match2:
						self.with_statement(var2, self.guess_condition)
						if var2[2] in self.negated_atoms:
							cond+="~"
						cond+=var2[2]+", "
					pattern2 = r'/(.*?)$'
					match2 = re.findall(pattern2, var[3])
					if match2:
						for var2 in match2:
							cond+=var2
				else:
					cond+=var[5]
				if(cond[-2]==","):
					cond=cond[:-2]
				cond+="), "
		cond=cond[:-2]
		if(cond.endswith("()")):
			cond=cond[:-3]	
		return cond
	def guess_def_check(self, args):
		pattern = r'(([A-Z]+[a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
		match = re.findall(pattern, args[0])
		length=len(self.all_condition)
		while(len(self.all_condition)>0):
			for c in self.all_condition:
				if(all(d in self.statement for d in self.dep[c])):
					self.statement+=c+", "
					self.all_condition.remove(c)
					break
			if(len(self.all_condition)==length):
				raise ValueError("Circular dependencies detected")
			else:
				length-=1
		self.statement=self.statement[:-2]
		self.statement+=f":\n	problem{self.problem}+=When("
		if match:
			for var in match:
				if var[2] in self.negated_atoms:
					self.statement+="~"
				self.statement+=var[2]+", "
			self.statement=self.statement[:-1]
		self.guess_condition=[]
		self.guess_condition_args={}
		self.count_guess+=1
		self.guess_count=guess_alias[self.count_guess]["number"]
		self.new_guess_alias={} #nuovi alias del costrutto guess con chiave l'alias/entità
		self.guess_alias={}
		self.guess_check=[]
		self.guess_entities=set()
		self.aggregate_entities=set()
		self.aggregate_with=[]
		self.aggr_alias=[]
		self.aggr_new_alias={}
		self.negated_atoms=[]
	def guess_def_1(self, args):
		cond=self.guess_def(args, 3)
		self.guess_def_check(args)
		if(len(args)==4):
			if("exactly" in args[1] or "at_least" in args[1] or "at_most" in args[1]):
				return f"with {self.statement[:-1]}).guess("+"{"+f"{cond}"+"}"+f", {args[1]}"+")"+"\n"
			else:
				substring = args[1].split(" , ")
				args[1] = " ".join(substring)
				if(len(args[1])>2):
					if(args[1][0]==","):
						args[1]=args[1][2:]
					if(args[1][-2]==","):
						args[1]=args[1][:-2]
					return f"with {self.statement[:-1]}, {args[1]}).guess("+"{"+f"{cond}"+"})"+"\n"
				return f"with {self.statement[:-1]}).guess("+"{"+f"{cond}"+"})"+"\n"
		if(len(args)==3):
			return f"with {self.statement[:-1]}).guess("+"{"+f"{cond}"+"})"+"\n"
		substring = args[1].split(" , ")
		args[1] = " ".join(substring)
		if(len(args[1])>2):
			if(args[1][0]==","):
				args[1]=args[1][2:]
			if(args[1][-2]==","):
				args[1]=args[1][:-2]
		return f"with {self.statement} {args[1]}).guess("+"{"+f"{cond}"+"}"+f", {args[2]}"+")"+"\n"
	def guess_def_2(self, args):	
		cond=self.guess_def(args, 4)
		pattern = r'(([A-Z]+[a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
		if(self.aggregate_with!=[]):
			for i in range(len(self.aggregate_with)):
				match = re.findall(pattern, self.aggregate_with[i])
				if match:
					for var in match:
						self.with_statement(var, self.guess_condition)
		self.guess_def_check(args)
		if(len(args)==5):
			if("exactly" in args[2] or "at_least" in args[2] or "at_most" in args[2]):
				return f"with {self.statement[:-1]}, {args[1]}).guess("+"{"+f"{cond}"+"}"+f", {args[2]}"+")"+"\n"
			else:
				substring = args[2].split(" , ")
				args[2] = " ".join(substring)
				if(len(args[2])>2):
					if(args[2][0]==","):
						args[2]=args[2][2:]
					if(args[2][-2]==","):
						args[2]=args[2][:-2]
					return f"with {self.statement[:-1]}, {args[1]}, {args[2]}).guess("+"{"+f"{cond}"+"})"+"\n"
				return f"with {self.statement[:-1]}, {args[1]}).guess("+"{"+f"{cond}"+"})"+"\n"
		if(len(args)==4):
			return f"with {self.statement[:-1]}, {args[1]}).guess("+"{"+f"{cond}"+"})"+"\n"
		substring = args[2].split(" , ")
		args[2] = " ".join(substring)
		if(len(args[2])>2):
			if(args[2][0]==","):
				args[2]=args[2][2:]
			if(args[2][-2]==","):
				args[2]=args[2][:-2]
		return f"with {self.statement} {args[1]}, {args[2]}).guess("+"{"+f"{cond}"+"}"+f", {args[3]}"+")"+"\n"
	def with_statement(self, var, conditions):
		found=False
		dependencies=[]
		already_defined=[]
		for i in range(0, len(conditions)-2, 3):
			if(var[2]==conditions[i]):
				verify=conditions[i+1].split("=")[0]
				if("." in verify): #per trasformare ad es a.user.video=v in Assign(user=User(video=v)))
					if conditions==self.define_condition:
						conditions[i+1]=self.new_define_cond(verify, conditions[i+1])
					else:
						conditions[i+1]=self.new_guess_cond(verify, conditions[i+1]) 
					verify=verify.split(".")[0]
				if(verify.strip() in already_defined):
					raise ValueError(f"Keyword argument repeated: {verify}")
				already_defined.append(verify.strip())
				if("." in conditions[i+2]):
					conditions[i+2]=conditions[i+2].split(".")[0]
				dependencies.append(f"as {conditions[i+2]}")
				if(found):
					self.condition+=", "+conditions[i+1]
				else:
					found=True
					self.condition+=f"{var[1]}({conditions[i+1]}"
		if not found:
			self.statement+=var[0]+", "
		elif(all(dep in self.statement for dep in dependencies)):
			self.statement+=f"{self.condition}) as {var[2]}, "
		else:	
			c=f"{self.condition}) as {var[2]}"
			self.dep[c]=dependencies
			self.all_condition.append(c)
			self.condition=""
		self.condition=""
	def new_guess_cond(self, verify, cond):
		c=3
		new_cond=""
		c2=0
		verify2=verify
		while("." in verify):
			en=verify2.split(".")
			new_cond+=en[c2].strip()+"="+self.attributes_guess_check(self.guess_condition_args[cond][0:c])	+"("	
			c+=2
			c2+=1
			verify=".".join(en[c2:])
		new_cond+=en[-1].strip()+"="+cond.split("=")[1]
		for j in range(len(new_cond)):
			if(new_cond[j]=="("):
				new_cond+=")"
		return new_cond
	def new_define_cond(self, verify, cond):
		c=3
		new_cond=""
		c2=0
		verify2=verify
		while("." in verify):
			en=verify2.split(".")
			new_cond+=en[c2].strip()+"="+self.attributes_check(self.define_condition_args[cond][0:c])	+"("	
			c+=2
			c2+=1
			verify=".".join(en[c2:])
		new_cond+=en[-1].strip()+"="+cond.split("=")[1]
		for j in range(len(new_cond)):
			if(new_cond[j]=="("):
				new_cond+=")"
		return new_cond
	def guess_definitions(self, args):
		return self.print_stat(args)
	def guess_definition(self, args):
		from_guess=args[-1].split("/")[0]
		if(len(from_guess)>0):
			self.addEdge_guess(from_guess, args[0])
		if not(args[0] in entities.keys()):
			raise ValueError(f"{args[0]} is not defined")		
		alias=""
		if(len(args)>2):
			if(args[1] in self.guess_alias):
				raise ValueError(f"Alias already defined: {args[1]}")
			for en in self.guess_check:
				if(en!=args[1]):
					raise ValueError(f"Alias is not defined: {en}")
			self.guess_check=[]
			if(args[1] in guess_alias[self.count_guess].keys()):
				alias=guess_alias[self.count_guess][args[1]]	
			self.guess_alias={}
			self.guess_entities=set()
			return f"{args[0]}() as {alias} {args[2]}"
		elif(args[0] in self.guess_entities):
			raise ValueError(f"Entity already defined: {args[0]}")
		for en in self.guess_check:
			if(en!=args[0]):
				raise ValueError(f"Entity is not defined: {en}")
		self.guess_check=[]
		self.guess_alias={}
		self.guess_entities=set()
		if(args[0] in guess_alias[self.count_guess].keys()):
			alias=guess_alias[self.count_guess][args[0]]
		return  f"{args[0]}() as {alias} {args[1]}"
	def guess_declaration(self, args):
		return self.print_stat(args)
	def from_guess(self, args):
		global g, recursive
		temp=[]
		for alias in guess_alias[self.count_guess].keys():
			if(alias!="number"):
				en=guess_entities[self.count_guess][alias]
				self.increment_num(en)
				temp.append(en)
		for arg in args:
			if(arg!=","):
				arg=arg.split("()")[0]
				self.increment_num(arg)
				for t in temp:
					if(recursive and arg==t):
						raise ValueError("Cyclic dependency detected")
					g.addEdge(num_pred[arg], num_pred[t])
		return self.print_stat(args)
	def increment_num(self, en):
		global num
		if(not en in num_pred.keys()):
			num_pred[en]=num
			num+=1
	def guess_entity(self, args):
		negated=False
		if(args[0]=="not"):
			negated=True
			args=args[1:]
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		if(len(args)>1):
			alias=self.add_number_guess(args[1])
			self.new_guess_alias[args[1]]=alias
			self.guess_alias[args[1]]=args[0]
			if(negated):
				self.negated_atoms.append(alias)
			return f"{args[0]}() as {alias}"
		alias=self.number_guess(args[0])
		self.new_guess_alias[args[0]]=alias
		self.guess_entities.add(args[0])
		if(negated):
			self.negated_atoms.append(alias)
		return f"{args[0]}() as {alias}"
	def guess_times(self, args):
		statements=f""
		for i in range(0, len(args)):
			if(args[i]=="and"):
				args[i]=", "
			if(args[i]=="exactly=" and len(args)>2):
				raise ValueError("exactly is incompatible with at_least and at_most")
			statements+=f"{args[i]}"
		return statements
	def where_guess(self, args):
		statement=""
		for i in range(len(args)):
			if(args[i]=="and"):
				args[i]=", "
			statement+=f"{args[i]}"
		self.guess_check=[]
		return statement
	def where_guess_statement(self, args):
		if(not args[0] in guess_entities[self.count_guess].keys()):
			raise ValueError(f"{args[0]} is not defined")
		statement=""
		args=self.guess_where_check(args)
		if(args==""):
			return args
		for i in range(len(args)):
			if(args[i]=="="):
				args[i]="=="
			statement+=f"{args[i]}"
		return statement		
	def guess_from(self, args):
		return self.print_stat(args)
	def entity_guess(self, args):
		negated=False
		if(args[0]=="not"):
			negated=True
			args=args[1:]
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		if(len(args)>1):
			alias=self.add_number_guess(args[1])
			if(args[1] in self.guess_alias.keys()):
				raise ValueError(f"Alias already defined: {args[1]}")
			self.guess_alias[args[1]]=args[0]
			self.new_guess_alias[args[1]]=alias
			if negated:
				self.negated_atoms.append(alias)
			return f"{args[0]}() as {alias}"
		alias=self.number_guess(args[0])
		if(args[0] in self.guess_entities):
			raise ValueError(f"Entity already defined: {args[0]}")
		self.guess_entities.add(args[0])
		self.new_guess_alias[args[0]]=alias
		if negated:
			self.negated_atoms.append(alias)
		return f"{args[0]}() as {alias}"
	def remove_and(self,args):
		statements=""
		for i in range(len(args)):
			if(args[i]=="and"):
				if(args[i+1]=="" or args[i-1]==""):
					args[i]=""
				else:
					args[i]=","
			if(args[i]!=""):
				statements+=args[i]
		return statements
	def guess_where(self, args):
		statements=self.remove_and(args)
		return "/"+ statements+"\\"
	def guess_where_statement(self, args):
		if(not (args[0] in guess_entities[self.count_guess].keys() or args[0] in self.guess_alias.keys() or args[0] in self.guess_entities)):
			raise ValueError(f"{args[0]} is not defined")
		args=self.guess_where_check(args)
		if(args==""):
			return ""
		stat=""
		for i in range(len(args)):
			if(args[i]=="="):
				args[i]="=="
			stat+=args[i]
		return stat
	def guess_where_check(self, args):
		attribute=self.attributes_guess_check(args)
		types=args[-1].split("/")
		if(not types[1]==attribute and attribute!="any"):
			if(args[-2]!="="):
				raise ValueError(f"{types[1]} cannot be compared with type: {attribute}")
			raise ValueError(f"{types[1]} cannot be assigned to type {attribute}")
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		elif(args[0] in guess_alias[self.count_guess].keys()):
			args[0]=guess_alias[self.count_guess][args[0]]
		if(len(args)<=3):
			temp_array=[]
			if("." in types[0]):
				splitted=types[0].split(".")
				for split in splitted:
					temp_array.append(split)
					temp_array.append(".")
				temp_array.pop()
			else:
				temp_array.append(types[0])
			temp_array.append(args[-2])
			temp_array.append(args[0])
			args=temp_array
		else:
			args[-1]=types[0]
		if(attribute!="str" and attribute!="int" and attribute!="any"):
			if(args[-2]!="=" or (not "." in types[0] and not "." in args)):
				raise TypeError(f"Cannot compare objects of these types: {attribute}")
			self.guess_condition.append(args[0])
			cond=f"{args[2]} {self.print_stat(args[3:])}"
			self.guess_condition.append(cond)
			self.guess_condition.append(args[-1])
			if("." in cond.split("=")[0]):
				self.guess_condition_args[cond]=args
				entity=self.guess_condition_args[cond][0]
				if(entity in guess_alias[self.count_guess].values()):
					for k, v in guess_alias[self.count_guess].items():
						if(v==entity):
							self.guess_condition_args[cond][0]=self.attributes_guess_check(k)
							break
				else:
					for k, v in self.new_guess_alias.items():
						if(v==entity):
							self.guess_condition_args[cond][0]=self.guess_alias[k]
							break
			return ""
		return args
	def assert_statement(self, args):
		return args[0]
	def assert_1(self,args):
		self.check_statement(args)
		self.init_define_variables()
		if(len(args)>2):
			return f"with {self.statement}:\n	problem{self.problem}+={args[2]}"
		return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"
	def assert_2(self, args):
		self.assert_deny_with(args)
		self.init_define_variables()
		if(len(args)>3):
			end_assert=args[3][:-1]
			end_assert+=", "+args[2]+")"
			return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
		end_assert=args[2][:-1]
		end_assert+=", "+args[1]+")"
		return  f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
	def assert_stat(self):
		var=[]
		for alias in self.redefined_entity.keys():
			var.append(self.new_define_alias[alias])
		for entity in self.defined_entity:
			var.append(self.new_define_alias[entity])
		return var
	def assert_3(self, args):
		self.assert_deny_with(args)
		end_assert=""
		var=self.assert_stat()
		var_statement=f"{var[0]}"
		for i in range(1, len(var)):
			var_statement+=f", {var[i]}"
		if(len(args)>2):
			pre_statement=""
			for alias in self.new_define_alias.values():
				if(not alias in var and not alias in self.aggr_new_alias):
					if(alias in self.negated_atoms):
						pre_statement+="~"
					pre_statement+=alias+", "
			self.init_define_variables()
			if(pre_statement!=""):
				pre_statement=pre_statement[:-2]
				end_assert="Assert("+var_statement+").when("+pre_statement+", "+args[2]+")"
			return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
		self.init_define_variables()
		end_assert="Assert("+var_statement+").when("+args[1]+")"
		return  f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
	def assert_(self, args):
		return args[0]+"\n"
	def deny_(self, args):
		return args[0]+"\n"
	def find_pattern(self, args):
		pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
		self.dep={}
		print(args)
		self.condition=""
		self.all_condition=[]
		match = re.findall(pattern, args[0])
		if match:
			for var in match:
				self.with_statement(var, self.define_condition)
		if(len(args)>2):
			print(args[1])
			match = re.findall(pattern, args[1])
			if match:
				for var in match:
					self.with_statement(var, self.define_condition)
		length=len(self.all_condition)
		while(len(self.all_condition)>0):
			for c in self.all_condition:
				if(all(d in self.statement for d in self.dep[c])):
					self.statement+=c+", "
					self.all_condition.remove(c)
					break
			if(len(self.all_condition)==length):
				raise ValueError("Circular dependencies detected")
			else:
				length-=1
		self.statement=self.statement[:-2]
	def check_statement(self, args):
		self.statement=""
		self.find_pattern(args)
		self.define_condition=[]
	def init_define_variables(self):
		self.redefined_entity={}
		self.defined_entity=set()
		self.new_define_alias={}
		self.declared_alias={}
		self.defined_entities=set()
		self.attributes={}
		self.aggregate_entities=set()
		self.aggregate_with=[]
		self.aggr_alias=[]
		self.aggr_new_alias={}
		self.otherwise_en=[]
		self.negated_atoms=[]
		self.count=0
	def assert_deny_with(self, args):
		self.statement=""
		for aggr in self.aggregate_with:
			args[0]+=", "+aggr
		self.find_pattern(args)
		self.define_condition=[]
	def assert_definition(self, args):
		return self.print_stat(args)
	def assert_entities(self,args):
		if(len(args)>1):
			self.redefined_entity[args[1]]=args[0]
			self.otherwise_en.append(args[1])
		else:
			self.otherwise_en.append(args[0])
		return self.define_definition(args)
	def assert_from(self, args):
		return self.print_stat(args)
	def assert_entity(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		if(len(args)>index+1):
			self.otherwise_en.append(args[index+1])
		else:
			self.otherwise_en.append(args[index])
		return self.define_entity(args)
	def where_assert(self, args):
		statement=""
		for i in range(len(args)):
			if(args[i]=="and"):
				args[i]=""
			if(args[i]!=""):
				statement+=args[i]
		var=self.assert_stat()
		var_statement=f"{var[0]}"
		for i in range(1, len(var)):
			var_statement+=f", {var[i]}"
		pre_statement=""
		for alias in self.new_define_alias.values():
			if(not alias in var and not alias in self.aggr_new_alias):
				if(alias in self.negated_atoms):
					pre_statement+="~"
				pre_statement+=alias+", "
		if(len(statement)>1):
			if(statement[-2]==","):
				statement=statement[:-2]
			return "Assert("+var_statement+").when("+pre_statement+statement[2:]+")"
		if(pre_statement!=""):
			pre_statement=pre_statement[:-2]
		return "Assert("+var_statement+").when("+pre_statement+")"
	def where_assert_statement(self, args):
		return self.where_define_statement(args)
	def try_assert(self, args):
		other=""
		for en in self.otherwise_en:
			other+=f"{self.new_define_alias[en]},"
		other=other[:-1]
		self.init_define_variables()
		return args[0] + ".otherwise("+ args[1]+ other +")\n"
	def assert_otherwise(self, args):
		return args[0]
	def assert_otherwise_1(self, args):
		self.check_statement(args)
		if(len(args)>2):
			return f"with {self.statement}:\n	problem{self.problem}+={args[2]}"
		return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"
	def assert_otherwise_2(self, args):
		self.assert_deny_with(args)
		if(len(args)>3):
			end_assert=args[3][:-1]
			end_assert+=", "+args[2]+")"
			return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
		end_assert=args[2][:-1]
		end_assert+=", "+args[1]+")"
		return  f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
	def assert_otherwise_3(self, args):
		self.assert_deny_with(args)
		end_assert=""
		var=self.assert_stat()
		var_statement=f"{var[0]}"
		for i in range(1, len(var)):
			var_statement+=f", {var[i]}"
		if(len(args)>2):
			pre_statement=""
			for alias in self.new_define_alias.values():
				if(not alias in var and not alias in self.aggr_new_alias):
					if(alias in self.negated_atoms):
						pre_statement+="~"
					pre_statement+=alias+", "
			if(pre_statement!=""):
				pre_statement=pre_statement[:-2]
				end_assert="Assert("+var_statement+").when("+pre_statement+", "+args[2]+")"
			return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
		end_assert="Assert("+var_statement+").when("+args[1]+")"
		return  f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
	def pay_statement(self, args):
		return args[0]+","+args[1]+","
	def try_deny(self, args):
		return self.try_assert(args)
	def deny_otherwise(self, args):
		return args[0]
	def deny_otherwise_1(self, args):
		self.assert_deny_with(args)
		if(len(args)>=3):
			end_assert=args[2][:-1]
			end_assert+=", "+args[1]+")"
			return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
		return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"
	def deny_otherwise_2(self, args):
		self.assert_deny_with(args)
		pre_statement=""
		for alias in self.new_define_alias.values():
			if not alias in self.aggr_new_alias:
				if(alias in self.negated_atoms):
					pre_statement+="~"
				pre_statement+=alias+", "
		return f"with {self.statement}:\n	problem{self.problem}+=Assert(False).when("+pre_statement+f"{args[1]})"
	def pay(self, args):
		attribute=self.value_define(args)
		types=attribute.split("/")
		if(not types[1]=="int"):
			raise ValueError(f"Expected int, received {types[1]}: {types[0]}")
		return types[0]
	def arithmetic_operation(self, args):
		return f"{args[0]}{args[1]}{args[2]}"
	def deny(self, args):
		return args[0]
	def deny_1(self, args):
		self.assert_deny_with(args)
		self.init_define_variables()
		if(len(args)>=3):
			end_assert=args[2][:-1]
			end_assert+=", "+args[1]+")"
			return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
		return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"
	def deny_2(self, args):
		self.assert_deny_with(args)
		pre_statement=""
		for alias in self.new_define_alias.values():
			if not alias in self.aggr_new_alias:
				if(alias in self.negated_atoms):
					pre_statement+="~"
				pre_statement+=alias+", "
		self.init_define_variables()
		return f"with {self.statement}:\n	problem{self.problem}+=Assert(False).when("+pre_statement+f"{args[1]})"
	def deny_from(self, args):
		return self.assert_from(args)
	def deny_entity(self, args):
		return self.assert_entity(args)
	def where_deny(self, args):
		statement=""
		for i in range(len(args)):
			if(args[i]=="and"):
				args[i]=""
			if(args[i]!=""):
				statement+=args[i]
		pre_statement=""
		for alias in self.new_define_alias.values():
			if not alias in self.aggr_new_alias:
				if(alias in self.negated_atoms):
					pre_statement+="~"
				pre_statement+=alias+", "
		if(len(statement)>1):
			if(statement[-2]==","):
				statement=statement[:-2]
			return "Assert(False).when("+pre_statement+statement[2:]+")"
		if(pre_statement!=""):
			pre_statement=pre_statement[:-2]
		return "Assert(False).when("+pre_statement+")"
	def where_deny_statement(self, args):
		return self.where_define_statement(args)
	def operator(self, args):
		return self.print_stat(args)
	def times(self, args):
		return args[0]+"="
	def print_stat(self, args):
		statements=f"{args[0]}"
		for i in range(1, len(args)):
			if(args[i]==","):
				statements+=f"{args[i]}"
			else:
				statements+=f" {args[i]}"
		return statements
	def attributes_check(self, args):
		attribute=""
		if(isinstance(args[0], Token)):
			if(args[0].type=="ENTITY_NAME"):
				attribute=args[0]
			if(args[0].type=="NAME"):
				if(args[0] in self.declared_alias.keys()):
					attribute=self.declared_alias[args[0]]
				else:
					attribute=self.redefined_entity[args[0]]
		if(len(args)>=2):	
			for i in range(2, len(args), 2):
				if(args[i-1]=="."):	
					if(attribute=="str" or attribute=="int"):
						raise ValueError(f"{attribute} object has not attribute {args[i]}")		
					found=False
					for t in entities[attribute]:
						if(t.value==args[i]):
							attribute=t.type
							found=True
							break
					if not found:
						raise ValueError(f"{attribute} object has not attribute {args[i]}")
				else:
						break
		return attribute
	def attributes_guess_check(self, args):
		attribute=""
		if(args[0] in self.guess_alias):
			attribute=self.guess_alias[args[0]]
		if(args[0] in self.guess_entities):
			attribute=args[0]
		if(args[0] in guess_entities[self.count_guess]):
			attribute=guess_entities[self.count_guess][args[0]]
			if(not args[0] in guess[self.count_guess]):
				self.guess_check.append(args[0])
		if(args[0] in entities.keys()):	
			attribute=args[0]
		if(len(args)>=2):
			for i in range(2, len(args), 2):
				if(args[i-1]=="."):	
					if(attribute=="str" or attribute=="int"):
						raise ValueError(f"{attribute} object has not attribute {args[i]}")		
					found=False
					for t in entities[attribute]:
						if(t.value==args[i]):
							attribute=t.type
							found=True
							break
					if not found:
						raise ValueError(f"{attribute} object has not attribute {args[i]}")
				else:
						break
		return attribute
	def number(self, args):
		letter=args[0].lower()
		letter+="_"+f"{self.count_define}"
		self.count_define+=1
		return letter
	def add_number(self, args):
		args=args+"_"+f"{self.count_define}"
		self.count_define+=1
		return args
	def number_guess(self, args):
		letter=args[0].lower()
		letter+="_"+f"{self.guess_count}"
		self.guess_count+=1
		return letter
	def add_number_guess(self, args):
		args=args+"_"+f"{self.guess_count}"
		self.guess_count+=1
		return args

def build_tree(code: str) -> ParseTree:
	parser_entities = Lark(grammar, parser='lalr', transformer=DeclarationTransformer())
	parser_entities.parse(code)
	parser_check = Lark(grammar, parser='lalr', transformer=CheckTransformer())
	return parser_check.parse(code)

def check_graph():
	global g
	g.SCC()

def main():
	destination_file = "o.py"
	parser = OptionParser(usage="Usage: %prog [options] [input_files]")
	parser.add_option("-f", "--file", dest="destination_file", help="write output to FILE", metavar="FILE")
	parser.add_option("-v", "--verbose", action="store_true", default=False, dest="verbose", help="print parse tree")
	parser.add_option("-e", "--execute", dest="execute", help="execute the generated code")
	parser.add_option("-r", "--recursive", dest="recursive", help="enable recursive checking")
	(options, args) = parser.parse_args()
	code = ''.join(fileinput.input(args))
	try:
		if(options.recursive):
			global recursive
			recursive=True
		tree = build_tree(code)
		if options.recursive:
			check_graph()
		if options.verbose:
			print(tree)
		if options.destination_file is not None:
			destination_file = options.destination_file
		f = open(f"{destination_file}", "w")
		f.write(str(tree))
		if options.execute is not None:
			execution_string = f"""
solver = SolverWrapper(solver_path="{options.execute}")
res = solver.solve(problem=problem{number}, timeout=10)
if res.status == Result.HAS_SOLUTION:
	print("Has solution")
elif res.status == Result.NO_SOLUTION:
	print("No solution found!")
else:
	print("Unknown")
	"""
			f.write(execution_string)
			f.close()
			subprocess.run(["python", f"{destination_file}"])
		else:
			f.close()
	except exceptions.LarkError as e:
		print(f"Parsing error: {e}")
	except Exception as e:
		print(f"Unexpected error: {e}")


if __name__ == '__main__':
	main()