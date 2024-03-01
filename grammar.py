from lark import Lark, Transformer, exceptions, Token
from optparse import OptionParser
import fileinput
import re, random

entities = {} #dizionario con chiave nome dell'entità e valore la lista dei parametri e rispettivi tipi
guess={} #dizionario di tutti gli alias ed entità definiti nel costrutto guess
guess_alias={} #dizionario degli alias interni al guess
guess_entities={} #dizionario dell'entità interne al guess

grammar = """
	start:  _statement+
	_statement: entity | define | guess | assert_statement | deny
	entity: "@entity" entity_declaration SEMICOLON
	entity_declaration: ENTITY_NAME COLON declarations
	declarations: declaration (COMMA declaration)*
	declaration: NAME COLON attr_type
	define: define_definition define_from? define_where
	define_definition: "define" ENTITY_NAME as_statement?
	as_statement: "as" NAME
	define_from: "from" define_entity (COMMA define_entity)*
	define_entity: ENTITY_NAME ("as" NAME)?
	define_where: "where" where_define_statement (AND where_define_statement)* SEMICOLON
	where_define_statement: (NAME | ENTITY_NAME) (DOT NAME)+ (operator | ASSIGN) var_define
	guess: "guess" from_guess where_guess? guess_times guess_definitions SEMICOLON
	from_guess: "from" guess_entity (COMMA guess_entity)*
	guess_entity: ENTITY_NAME ("as" NAME)?
	where_guess: "where"  where_guess_statement (AND where_guess_statement)*
	where_guess_statement: (NAME | ENTITY_NAME) ((DOT NAME)+ ((operator | ASSIGN) var_guess)?)?
	guess_times: times (INT| times_value) (AND guess_times)*
	guess_definitions: guess_definition+
	guess_definition: ENTITY_NAME ("as" NAME)? guess_declaration
	guess_declaration: guess_from? guess_where
	guess_from: "from" entity_guess (COMMA entity_guess)*
	entity_guess: ENTITY_NAME ("as" NAME)?
	guess_where: "where"  guess_where_statement (AND guess_where_statement)*
	guess_where_statement: (NAME | ENTITY_NAME) (DOT NAME)+ (operator | ASSIGN) var_guess_2
	assert_statement: assert_definition assert_from? where_assert
	assert_definition: "assert" (ENTITY_NAME ("as" NAME)?)?
	assert_from: "from" assert_entity (COMMA assert_entity)*
	assert_entity: ENTITY_NAME ("as" NAME)?
	where_assert: "where" where_assert_statement (AND where_assert_statement)* SEMICOLON
	where_assert_statement: (NAME | ENTITY_NAME) (DOT NAME)+ (operator | ASSIGN) var
	deny: "deny" deny_from? where_deny
	deny_from: "from" deny_entity (COMMA deny_entity)*
	deny_entity: ENTITY_NAME ("as" NAME)?
	where_deny: "where" where_deny_statement (AND where_deny_statement)* SEMICOLON
	where_deny_statement: (NAME | ENTITY_NAME) (DOT NAME)+ (operator | ASSIGN) var
	var_guess:  INT | STR | value_guess
	value_guess: (NAME | ENTITY_NAME) (DOT NAME)+
	times_value: (NAME | ENTITY_NAME) (DOT NAME)+
	value: (NAME | ENTITY_NAME) (DOT NAME)+	
	var_guess_2:  INT | STR | value_guess_2
	var: INT | STR | value
	value_guess_2: (NAME | ENTITY_NAME) (DOT NAME)*	
	var_define: INT | STR | value_define
	value_define: (NAME | ENTITY_NAME) (DOT NAME)*	
	operator: EQUALITY | LT | LE | GT | GE | NOTEQUAL
	bool_operator: AND | OR
	times: EXACTLY | ATLEAST | ATMOST
	attr_type: ANY | STRING | INTEGER | ENTITY_NAME
	NAME: /[a-z_][a-z0-9_]*/
	ENTITY_NAME: /[A-Z][a-z0-9_]*/
	COLON: ":"
	SEMICOLON: ";"
	COMMA: ","
	DOT: "."
	ASSIGN: "="
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
	EXACTLY: "exactly"
	ATLEAST: "at_least"
	ATMOST: "at_most"
	ANY: "any"
	STRING: "str"
	INTEGER: "int"
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
			if(args[1] in guess[self.count_guess]):
				raise ValueError(f"Alias already defined: {args[1]}")
			guess[self.count_guess].append(args[1])
			guess_alias[self.count_guess][args[1]]=self.add_number(args[1])
			guess_entities[self.count_guess][args[1]]=args[0]
		else:
			if(args[0] in guess[self.count_guess]):
				raise ValueError(f"Entity already defined: {args[0]}")
			guess[self.count_guess].append(args[0])
			guess_alias[self.count_guess][args[0]]=self.number(args[0])
			guess_entities[self.count_guess][args[0]]=args[0]
		guess_alias[self.count_guess]["number"]+=1
	def guess_entity(self, args):
		if(len(args)>1):
			if(args[1] in guess[self.count_guess]):
				raise ValueError(f"Alias already defined: {args[1]}")
			guess[self.count_guess].append(args[1])
			guess_entities[self.count_guess][args[1]]=args[0]
		else:
			if(args[0] in guess[self.count_guess]):
				raise ValueError(f"Entity already defined: {args[0]}")
			guess[self.count_guess].append(args[0])
			guess_entities[self.count_guess][args[0]]=args[0]
	def entity_guess(self, args):
		if(len(args)>1):
			if(args[1] in guess[self.count_guess]):
				raise ValueError(f"Alias already defined: {args[1]}")
		else:
			if(args[0] in guess[self.count_guess]):
				raise ValueError(f"Entity already defined: {args[0]}")
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
		self.defined_entity="" #entità definita nella define
		self.redefined_entity="" #alias dell'entità definita nella define
		self.new_define_alias={} #nuovi alias del costrutto define con chiave l'alias/entità
		self.new_guess_alias={} #nuovi alias del costrutto guess con chiave l'alias/entità
		self.guess_alias={} #alias del costrutto guess
		self.guess_entities=set() #entità del costrutto guess
		self.count_guess=0 #numero progressivo per gli alias del guess
		self.guess_count=guess_alias[0]["number"] #numero da cui partire per gli alias del guess
		self.count_define=0 #numero progressivo per gli alias della define
		self.dependencies={}
		self.entities_attributes=[]
		self.problem=random.randint(0,100)
	def start(self, args):
		atoms=[atom for atom in args if atom.startswith("@atom")]
		others=[other for other in args if other not in atoms]
		ordered_atoms = []
		ordered=[]
		ordered.append("from pyspell.L import *\n\n")
		while len(ordered) - 1 < len(atoms):
			for atom in atoms:
				if not atom in ordered:
					name = atom.split("class ")[1].split(":")[0]
					if not self.dependencies[name]:
						ordered.append(atom)
						ordered_atoms.append(name)
					else:
						all_dependencies_met = all(dep in ordered_atoms for dep in self.dependencies[name])
						if all_dependencies_met:
							ordered.append(atom)
							ordered_atoms.append(name)
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
		self.redefined_entity=""
		self.defined_entity=""
		self.new_define_alias={}
		self.count=0
		self.declared_alias={}
		self.defined_entities=set()
		self.attributes={}
		if(len(args)>2):
			return f"with {args[0]}{args[1]}:\n{self.when_define(args[1])}{args[2]}"
		return f"with {args[0]}:\n{args[1]}"
	def define_from(self, args):
		return ", "+self.print_stat(args)
	def when_define(self, args):
		statement=f"	problem{self.problem}+=When("
		pattern = r'as\s+([a-zA-Z0-9_]+)$'
		match = re.findall(pattern, args)
		if match:
			for var in match:
			    statement+=var
		pattern = r'as\s+([a-zA-Z0-9_]+),'
		match = re.findall(pattern, args)
		if match:
			for var in match:
			    statement+=", "+var
		return statement
	def define_where(self, args):
		statements=""
		for i in range(len(args)):
			if(not args[i]==";" and not args[i]=="and"):
				statements+=f"{args[i]}"
		if(self.redefined_entity==""):
			return statements + f").define({self.new_define_alias[self.defined_entity]})\n"
		for alias in self.new_define_alias.keys():
			return statements + f").define({self.new_define_alias[alias]})\n"
	def define_definition(self, args):
		if(not args[0] in entities.keys()):
			 raise ValueError(f"Undefined entity: {args[0]}")
		self.declared_alias={}
		self.defined_entities=set()
		self.attributes={}
		self.defined_entity=args[0]
		attr=entities[args[0]]
		all_attr=[]
		for i in range(len(attr)):
			all_attr.append(attr[i]) 
		self.attributes[self.defined_entity]=all_attr
		if(len(args)>1):
			alias=self.add_number(args[1])
			self.new_define_alias[args[1]]=alias
			return f"{args[0]}() as {alias}"
		alias=self.number(args[0])
		self.new_define_alias[args[0].value]=alias
		return f"{args[0]}() as {alias}"
	def as_statement(self, args):
		self.redefined_entity=args[0]
		return f"{args[0]}"
	def define_entity(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		var=""
		if(len(args)>1): #se è stato definito l'alias aggiungo in declared_alias altrimenti in defined_entities
			if(args[1] in self.declared_alias or args[1]==self.redefined_entity):
				raise ValueError(f"Alias already defined: {args[1]}")
			self.declared_alias[args[1]]=args[0]
			var=args[1]
		else:
			if(args[0] in self.defined_entities or args[0]==self.defined_entity):
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
			return f"{args[0]}() as {alias}"
		alias=self.number(args[0])
		self.new_define_alias[args[0].value]=alias
		return f"{args[0]}() as {alias}"
	def var(self, args):
		if(isinstance(args[0], Token)):
			args[0]+=f"/{args[0].type.lower()}"
		return self.print_stat(args)
	def value(self, args):
		statement=""
		entity=args[0]
		if(not (args[0]==self.redefined_entity or (self.redefined_entity=="" and args[0]==self.defined_entity))):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		else:
			args[0]=self.defined_entity
		attribute=self.attributes_check(args)
		args[0]=entity
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement + "/" + attribute
	def var_define(self, args):
		if(isinstance(args[0], Token)):
			args[0]+=f"/{args[0].type.lower()}"
		return self.print_stat(args)
	def value_define(self, args):
		statement=""
		entity=args[0]
		if(not (args[0]==self.redefined_entity or (self.redefined_entity=="" and args[0]==self.defined_entity))):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		else:
			args[0]=self.defined_entity
		attribute=self.attributes_check(args)
		if(args[0] in self.new_define_alias.keys()):
			args[0]=self.new_define_alias[args[0]]
		if(args[0]==self.defined_entity and self.redefined_entity!=""): #nel caso in cui ci sia l'alias dell'entità della define
			args[0]=self.new_define_alias[entity]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement + "/" + attribute
	def var_guess(self, args):
		if(isinstance(args[0], Token)):
			args[0]+=f"/{args[0].type.lower()}"
		return self.print_stat(args)
	def value_guess(self, args):
		statement=""
		if(not args[0] in guess[self.count_guess]):
			raise ValueError(f"{args[0]} is not defined")
		attribute=self.attributes_guess_check(args)
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		else:
			if(args[0] in guess_alias[self.count_guess].keys()):
				args[0]=guess_alias[self.count_guess][args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement+ "/" + attribute
	def times_value(self, args):
		statement=""
		if not (args[0] in guess[self.count_guess]):
				raise ValueError(f"Entity not defined: {args[0]}")
		attribute=self.attributes_guess_check(args)
		if(attribute!="int"):
			raise ValueError(f"expected int, received {attribute}: {statements}")
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		else:	
			if(args[0] in guess_alias[self.count_guess].keys()):
				args[0]=guess_alias[self.count_guess][args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement
	def var_guess_2(self, args):
		return self.var_guess(args)
	def value_guess_2(self, args):
		statement=""
		if not (args[0] in self.guess_alias.keys() or args[0] in self.guess_entities or args[0] in guess[self.count_guess]):
			raise ValueError(f"{args[0]} is not defined")
		attribute=self.attributes_guess_check(args)
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		else:
			if(args[0] in guess_alias[self.count_guess].keys()):
				args[0]=guess_alias[self.count_guess][args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement+ "/" + attribute
	def where_define_statement(self, args):
		entity=args[0]
		if(not (args[0]==self.redefined_entity or (self.redefined_entity=="" and args[0]==self.defined_entity))):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		else:
			args[0]=self.defined_entity
		attribute=self.attributes_check(args)
		statement=", "
		types=args[-1].split("/")
		if(not types[1]==attribute and attribute!="any"):
			raise ValueError(f"{types[1]} cannot be assigned to type {attribute}")
		args[-1]=types[0]
		if(args[0] in self.new_define_alias.keys()):
			args[0]=self.new_define_alias[args[0]]
		if(args[0]==self.defined_entity and self.redefined_entity!=""): #nel caso in cui ci sia l'alias dell'entità della define
			args[0]=self.new_define_alias[entity]
		for i in range(len(args)):
			if(args[i]=="="):
				statement+="=="
			else:
				statement+=f"{args[i]}"
		return statement
	def guess(self, args):
		self.count_guess+=1
		self.guess_count=guess_alias[self.count_guess]["number"]
		self.new_guess_alias={} #nuovi alias del costrutto guess con chiave l'alias/entità
		self.guess_alias={}
		self.guess_entities=set()
		statement=""
		cond=""
		pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)((.*?)/(.*?))\\'
		index=3
		if(len(args)==4):
			index=2
		match = re.findall(pattern, args[index])
		if match:
			for var in match:
				statement+=var[0]+", "
				cond+=f"{var[2]}:("
				pattern2 = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
				match2 = re.findall(pattern2, var[3])
				if match2:
					for var2 in match2:
						cond+=var2[2]+", "
						statement+=var2[0]+", "
					pattern2 = r'/(.*?)$'
					match2 = re.findall(pattern2, var[3])
					if match2:
						for var2 in match2:
							cond+=var2
				else:
					cond+=var[5]
				
				cond+="), "
		cond=cond[:-2]
		pattern = r'(([A-Z]+[a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
		match = re.findall(pattern, args[0])
		statement=statement[:-2]
		statement+=f":\n	problem{self.problem}+=When("
		if match:
			for var in match:
				statement+=var[2]+", "
			statement=statement[:-1]
		if(len(args)==4):
			return f"with {args[0]}, {statement[:-1]}).guess("+"{"+f"{cond}"+"}"+f", {args[1]}"+")"+"\n"
		return f"with {args[0]}, {statement} {args[1]}).guess("+"{"+f"{cond}"+"}"+f", {args[2]}"+")"+"\n"
	def guess_definitions(self, args):
		return self.print_stat(args)
	def guess_definition(self, args):
		if not(args[0] in entities.keys()):
			raise ValueError(f"{args[0]} is not defined")		
		alias=""
		if(len(args)>2):
			if(args[1] in self.guess_alias):
				raise ValueError(f"Alias already defined: {args[1]}")
			if(args[1] in guess_alias[self.count_guess].keys()):
				alias=guess_alias[self.count_guess][args[1]]
			return f"{args[0]}() as {alias} {args[2]}"
		else:
			if(args[0] in self.guess_entities):
				raise ValueError(f"Entity already defined: {args[0]}")
		self.guess_alias={}
		self.guess_entities=set()
		if(args[0] in guess_alias[self.count_guess].keys()):
			alias=guess_alias[self.count_guess][args[0]]
		return  f"{args[0]}() as {alias} {args[1]}"
	def guess_declaration(self, args):
		return self.print_stat(args)
	def from_guess(self, args):
		return self.print_stat(args)
	def guess_entity(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		if(len(args)>1):
			alias=self.add_number_guess(args[1])
			self.new_guess_alias[args[1]]=alias
			self.guess_alias[args[1]]=args[0]
			return f"{args[0]}() as {alias}"
		alias=self.number_guess(args[0])
		self.new_guess_alias[args[0]]=alias
		self.guess_entities.add(args[0])
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
		return statement
	def where_guess_statement(self, args):
		if(not args[0] in guess[self.count_guess]):
			raise ValueError(f"{args[0]} is not defined")
		statement=""
		attribute=self.attributes_guess_check(args)
		types=args[-1].split("/")
		if(not types[1]==attribute and attribute!="any"):
			raise ValueError(f"{types[1]} cannot be assigned to type {attribute}")
		args[-1]=types[0]
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		else:
			if(args[0] in guess_alias[self.count_guess].keys()):
				args[0]=guess_alias[self.count_guess][args[0]]
		for i in range(len(args)):
			if(args[i]=="="):
				args[i]="=="
			statement+=f"{args[i]}"
		return statement		
	def guess_from(self, args):
		return self.print_stat(args)
	def entity_guess(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		if(len(args)>1):
			alias=self.add_number_guess(args[1])
			if(args[1] in self.guess_alias.keys()):
				raise ValueError(f"Alias already defined: {args[1]}")
			self.guess_alias[args[1]]=args[0]
			self.new_guess_alias[args[1]]=alias
			return f"{args[0]}() as {alias}"
		alias=self.number_guess(args[0])
		if(args[0] in self.guess_entities):
			raise ValueError(f"Entity already defined: {args[0]}")
		self.guess_entities.add(args[0])
		self.new_guess_alias[args[0]]=alias
		return f"{args[0]}() as {alias}"
	def guess_where(self, args):
		for i in range(len(args)):
			if(args[i]=="and"):
				args[i]=","
		return "/"+ self.print_stat(args)+"\\"
	def guess_where_statement(self, args):
		if(not (args[0] in guess[self.count_guess] or args[0] in self.guess_alias.keys() or args[0] in self.guess_entities)):
			raise ValueError(f"{args[0]} is not defined")
		attribute=self.attributes_guess_check(args)
		types=args[-1].split("/")
		if(not types[1]==attribute and attribute!="any"):
			raise ValueError(f"{types[1]} cannot be assigned to type {attribute}")
		args[-1]=types[0]
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		else:
			if(args[0] in guess_alias[self.count_guess].keys()):
				args[0]=guess_alias[self.count_guess][args[0]]
		for i in range(len(args)):
			if(args[i]=="="):
				args[i]="=="
		return f"{args[0]}{args[1]}{args[2]} {args[3]} {args[4]}"
	def assert_statement(self, args):
		self.redefined_entity=""
		self.defined_entity=""
		self.new_define_alias={}
		self.declared_alias={}
		self.defined_entities=set()
		self.attributes={}
		self.count=0
		return "assert " + self.print_stat(args) +"\n"
	def assert_definition(self, args):
		if(not args[0] in entities.keys()):
			 raise ValueError(f"Undefined entity: {args[0]}")
		self.defined_entity=args[0]
		self.attributes={}
		attr=entities[args[0]]
		all_attr=[]
		for i in range(len(attr)):
			all_attr.append(attr[i]) 
		self.attributes[self.defined_entity]=all_attr
		if(len(args)>=2):
			self.redefined_entity=args[1]
			return f"{args[0]} as {args[1]}"
		return self.print_stat(args)
	def assert_from(self, args):
		return "from " + self.print_stat(args)
	def assert_entity(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		var=""
		if(len(args)>1): #se è stato definito l'alias aggiungo in declared_alias altrimenti in defined_entities
			if(args[1] in self.declared_alias or args[1]==self.redefined_entity):
				raise ValueError(f"Alias already defined: {args[1]}")
			self.declared_alias[args[1]]=args[0]
			var=args[1]
		else:
			if(args[0] in self.defined_entities or args[0]==self.defined_entity):
				raise ValueError(f"Entity already defined: {args[0]}")
			self.defined_entities.add(args[0])
			var=args[0]
		attr=entities[args[0]]
		all_attr=[]
		for i in range(len(attr)):
			all_attr.append(attr[i]) 
		self.attributes[var]=all_attr #lista degli attributi dell'entità
		if(len(args)>=2):
			return f"{args[0]} as {args[1]}"
		return self.print_stat(args)
	def where_assert(self, args):
		return "\n	where "+ self.print_stat(args)
	def where_assert_statement(self, args):
		entity=args[0]
		if(not (args[0]==self.redefined_entity or (self.redefined_entity=="" and args[0]==self.defined_entity))):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		else:
			args[0]=self.defined_entity
		attribute=self.attributes_check(args)
		types=args[-1].split("/")
		if(not types[1]==attribute and attribute!="any"):
			raise ValueError(f"{types[1]} cannot be assigned to type {attribute}")
		args[-1]=types[0]
		return self.print_stat(args)
	def deny(self, args):
		self.redefined_entity=""
		self.defined_entity=""
		self.new_define_alias={}
		self.declared_alias={}
		self.defined_entities=set()
		self.attributes={}
		self.count=0
		return "deny "+self.print_stat(args)+"\n"
	def deny_from(self, args):
		return self.assert_from(args)
	def deny_entity(self, args):
		return self.assert_entity(args)
	def where_deny(self, args):
		return self.where_assert(args)
	def where_deny_statement(self, args):
		return self.where_assert_statement(args)
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
		if(args[0].type=="ENTITY_NAME"):
			attribute=args[0]
		if(args[0].type=="NAME"):
			attribute=self.declared_alias[args[0]]
		if(len(args)>=2):
			found=False
			for attr in self.attributes[args[0]]:
				if(attr.value==args[2].value):
					attribute=attr.type
					found=True
					break
			if(not found):
				raise ValueError(f"{args[0]} object has not attribute {args[2]}")	
			for i in range(4, len(args), 2):
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

if __name__ == '__main__':
	parser = OptionParser(usage = "Usage: %prog [options] [input_files]")
	parser.add_option("-f", "--file", dest="destination_file", help="write output to FILE", metavar="FILE")
	parser.add_option("-v", "--verbose", action="store_true", default=False, dest="verbose", help="print parse tree")
	(options, args) = parser.parse_args()
	code=""	
	for line in fileinput.input(args):
		code += line		
	try:
		parser_entities = Lark(grammar, parser='lalr', transformer=DeclarationTransformer())
		parser_entities.parse(code)
		parser_check = Lark(grammar, parser='lalr', transformer=CheckTransformer())
		tree=parser_check.parse(code)		
		if options.verbose:
			print(tree)
	except exceptions.LarkError as e:
		print(f"Parsing error: {e}")
	except Exception as e:
		print(f"Unexpected error: {e}")
	
