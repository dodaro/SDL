from lark import Lark, Transformer, exceptions, Tree

entities = {} #dizionario con chiave nome dell'entità e valore la lista dei parametri e rispettivi tipi
guess={} #dizionario degli alias ed entità definite nel costrutto guess

grammar = """
	start:  _statement+
	_statement: entity | define | guess
	entity: "@entity" entity_declaration SEMICOLON
	entity_declaration: ENTITY_NAME COLON declarations
	declarations: declaration (COMMA declaration)*
	declaration: NAME COLON type
	define: definition from_statement where?
	definition: "define" ENTITY_NAME as_statement?
	as_statement: "as" NAME
	from_statement: "from" single_entity (COMMA single_entity)*
	single_entity: ENTITY_NAME ("as" NAME)?
	where: "where" where_statement (AND where_statement)* SEMICOLON
	where_statement: (NAME | ENTITY_NAME) DOT NAME (operator | ASSIGN) var
	guess: "guess" from_guess where_guess? guess_times guess_definition+ SEMICOLON
	from_guess: "from" guess_entity (COMMA guess_entity)*
	guess_entity: ENTITY_NAME ("as" NAME)?
	where_guess: "where"  where_guess_statement (AND where_guess_statement)*
	where_guess_statement: (NAME | ENTITY_NAME) DOT NAME (operator | ASSIGN) var
	guess_times: times INT (AND times INT)*
	guess_definition: ENTITY_NAME guess_from? guess_where
	guess_from: "from" entity_guess (COMMA guess_entity)*
	entity_guess: ENTITY_NAME ("as" NAME)?
	guess_where: "where"  guess_where_statement (AND guess_where_statement)*
	guess_where_statement: (NAME | ENTITY_NAME) DOT NAME (operator | ASSIGN) var
	
	var:  INT | STR | (NAME | ENTITY_NAME) (DOT NAME)* 		
	operator: EQUALITY | LT | LE | GT | GE | NOTEQUAL
	bool_operator: AND | OR
	times: EXACTLY | ATLEAST | ATMOST
	type: ANY | STRING | INTEGER | ENTITY_NAME
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
	ATLEAST: "at least"
	ATMOST: "at most"
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
		guess[0]=[]
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
	def guess_definition(self, args):
		guess[self.count_guess].append(args[0])
	def guess_entity(self, args):
		if(len(args)>1):
			if(args[1] in guess[self.count_guess]):
				raise ValueError(f"Alias already defined: {args[1]}")
			guess[self.count_guess].append(args[1])
		else:
			if(args[0] in guess[self.count_guess]):
				raise ValueError(f"Entity already defined: {args[0]}")
			guess[self.count_guess].append(args[0])

class CheckTransformer(Transformer):
	def __init__(self):
		self.declared_alias={} #dizionario degli alias dichiarati nel from di ogni define e con valore l'entità
		self.defined_entities=set() #entità definite nel from di ogni define
		self.attributes={} #dizionario con chiave l'entità/l'alias e valore la lista degli attributi, inizializzato ad ogni define
		self.defined_entity="" #entità definita nella define
		self.redefined_entity="" #alias dell'entità definita nella define
		self.guess_alias={}
		self.guess_entities=set()
		self.count_guess=0
	def define(self, args):
		self.redefined_entity=""
		self.defined_entity=""
		return f"{args[0]} {args[1]} {args[2]}"
	def from_statement(self, args):
		return " from "+ self.print_stat(args)+ "\n"
	def where(self, args):
		statements=""
		for i in range(len(args)):
			if(not args[i]==";"):
				statements+=f" {args[i]}"
		return " where"+statements + ";\n"
	def definition(self, args):
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
			return f"define {args[0]} {args[1]} \n"
		return f"define {args[0]} \n"
	def as_statement(self, args):
		if(args[0] in entities.keys()):
			raise ValueError(f"Invalid alias: {args[0]}")
		self.redefined_entity=args[0]
		return f"as {args[0]}"
	def single_entity(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		var=""
		if(len(args)>1): #se è stato definito l'alias aggiungo in declared_alias altrimenti in defined_entities
			if(args[1] in entities.keys()):
				raise ValueError(f"Invalid alias: {args[1]}")
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
			return f"{args[0]} as {args[1]}"
		return f"{args[0]}"
	def var(self, args):
		return self.print_stat(args)
	def args_type(self, args):	
		return args[0]
	def where_statement(self, args):
		entity=args[0]
		if(not (args[0]==self.redefined_entity or (self.redefined_entity=="" and args[0]==self.defined_entity))):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_entities):
					raise ValueError(f"{args[0]} is not defined")
		else:
			args[0]=self.defined_entity
		if(not args[2].value in self.attributes[args[0]]):
			raise ValueError(f"Attribute {args[2]} of entity {args[0]} is not defined")
		args_4=self.args_type(args[4])
		if(len(args[4])>1):
			for i in range(1, len(args[4])):
				args_4+=args[4][i]
		return f"{entity}{args[1]}{args[2]} {args[3]} {args_4}"
	def guess(self, args):
		self.count_guess+=1
		return "guess "+self.print_stat(args)+"\n"
	def guess_definition(self, args):
		if not(args[0] in entities.keys()):
			raise ValueError(f"{args[0]} is not defined")
		if(args[0] in self.guess_entities):
			raise ValueError(f"Entity already defined: {args[0]}")
		self.guess_alias={}
		self.guess_entities=set()
		if(len(args)>2):
			return f"\n  {args[0]}\n  {args[1]} {args[2]}"
		return  f"\n  {args[0]}  {args[1]}"
	def from_guess(self, args):
		return "from " + self.print_stat(args)
	def guess_entity(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		if(len(args)>1):
			return f"{args[0]} as {args[1]}"
		return f"{args[0]}"
	def guess_times(self, args):
		return self.print_stat(args)
	def where_guess(self, args):
		return "\n  where "+ self.print_stat(args)
	def where_guess_statement(self, args):
		if(not args[0] in guess[self.count_guess]):
			raise ValueError(f"{args[0]} is not defined")
		return f"{args[0]}{args[1]}{args[2]} {args[3]} {args[4]}"
	def guess_from(self, args):
		return "from " + self.print_stat(args)
	def entity_guess(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		if(len(args)>1):
			self.guess_alias[args[1]]=args[0]
			return f"{args[0]} as {args[1]}"
		self.guess_entities.add(args[0])
		return f"{args[0]}"
	def guess_where(self, args):
		return "\n  where "+ self.print_stat(args)
	def guess_where_statement(self, args):
		if(not (args[0] in guess[self.count_guess] or args[0] in self.guess_alias.keys() or args[0] in self.guess_entities)):
			raise ValueError(f"{args[0]} is not defined")
		return f"{args[0]}{args[1]}{args[2]} {args[3]} {args[4]}"
	def operator(self, args):
		return self.print_stat(args)
	def times(self, args):
		return "\n  "+ args[0]
	def print_stat(self, args):
		statements=f"{args[0]}"
		for i in range(1, len(args)):
			if(args[i]==","):
				statements+=f"{args[i]}"
			else:
				statements+=f" {args[i]}"
		return statements


if __name__ == '__main__':
	code=""
	with open('examples/example3.txt', 'r') as file:
	    code = file.read()
	try:
		parser_entities = Lark(grammar, parser='lalr', transformer=DeclarationTransformer())
		parser_entities.parse(code)
		parser_check = Lark(grammar, parser='lalr', transformer=CheckTransformer())
		tree=parser_check.parse(code)
		print(tree.pretty())
	except exceptions.LarkError as e:
		print(f"Parsing error: {e}")
	except Exception as e:
		print(f"Unexpected error: {e}")
	
