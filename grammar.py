from lark import Lark, Transformer, exceptions, Tree

entities = {} #dizionario con chiave nome dell'entità e valore la lista dei parametri e rispettivi tipi
guess=[] #lista degli alias ed entità definite nel from e nel with del costrutto guess

grammar = """
	start:  _statement+
	_statement: entity | define | guess
	entity: "@entity" entity_declaration SEMICOLON
	entity_declaration: NAME COLON declarations
	declarations: declaration (COMMA declaration)*
	declaration: NAME COLON type
	define: definition from_statement where?
	definition: "define" NAME as_statement?
	as_statement: "as" NAME
	from_statement: "from" single_entity (COMMA single_entity)*
	single_entity: NAME ("as" NAME)?
	where: "where" where_statement (AND where_statement)* SEMICOLON
	where_statement: (NAME DOT)? NAME EQUALS var
	guess: guess_statement with_guess from_guess where_guess SEMICOLON
	guess_statement: "guess" guess_times guess_definition
	guess_times: times INT (AND times INT)*
	guess_definition: NAME (COLON brackets)? (COMMA guess_definition)*
	brackets: OPEN_BRACKET inside_brackets (COMMA inside_brackets)* CLOSED_BRACKET
	inside_brackets: condition (bool_operator condition)*| value 
	condition: NOT? value ((operator (value | INT | STR)) | in_stat)
	value: NAME (DOT NAME)*
	var:  INT | STR | NAME (DOT NAME)* 
	from_guess: "from" guess_entity (COMMA guess_entity)*
	with_guess: "with" with_statement (COMMA with_statement)* 
	with_statement: NAME OPEN_BRACKET NAME EQUALS var (COMMA NAME EQUALS var)* CLOSED_BRACKET guess_as
	guess_entity: NAME ("as" NAME)?
	guess_as: ("as" NAME)
	where_guess: "where" NAME (COMMA NAME)*
	in_stat: IN /[a-z_][a-z0-9_]*/	
	operator: EQUALITY | LT | LE | GT | GE | NOTEQUAL
	bool_operator: AND | OR
	times: EXACTLY | ATLEAST | ATMOST
	type: ANY | STRING | INTEGER | custom_type
	custom_type: NAME
	NAME: /[a-z_][a-z0-9_]*/
	COLON: ":"
	SEMICOLON: ";"
	COMMA: ","
	DOT: "."
	EQUALS: "="
	OPEN_BRACKET: "("
	CLOSED_BRACKET: ")"
	EQUALITY: "=="
	NOTEQUAL: "!="
	GE: ">="
	GT: ">"
	LT: "<"
	LE: "<="
	IN: "in"
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
			if(isinstance(token[0], Tree)): #nel caso in cui l'attributo sia un custom_type
				custom_type=token[0].children
				attr_type=custom_type[0]
			if(attr_type==entity_name): #si definisce come tipo dell'attributo l'entità stessa
				raise ValueError("Invalid syntax")
			attr[0].type=str(attr_type) #salvo il tipo dell'attributo nel token
			entities[entity_name].append(attr[0]) #aggiungo nella lista degli attributi
		return args
	def guess_as(self, args):
		if(args[0] in guess):
			raise ValueError(f"Alias already defined: {args[0]}")
		guess.append(args[0])
		return args
	def guess_entity(self, args):
		if(len(args)>1):
			if(args[1] in guess):
				raise ValueError(f"Alias already defined: {args[1]}")
			guess.append(args[1])
		else:
			if(args[0] in guess):
				raise ValueError(f"Entity already defined: {args[0]}")
			guess.append(args[0])

class CheckTransformer(Transformer):
	def __init__(self):
		self.declared_alias={} #dizionario degli alias dichiarati nel from di ogni define e con valore l'entità
		self.defined_entities=set() #entità definite nel from di ogni define
		self.attributes={} #dizionario con chiave l'entità/l'alias e valore la lista degli attributi, inizializzato ad ogni define
		self.defined_node="" #entità definita nella define
		self.redefined_node="" #alias dell'entità definita nella define
		self.with_attributes=[] #lista contenente gli attributi delle entità definite nel with
	def custom_type(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Unrecognized custom type: {args[0]}")
		return f"{args[0]}"
	def define(self, args):
		self.redefined_node=""
		self.defined_node=""
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
		self.defined_node=args[0]
		if(len(args)>1):
			return f"define {args[0]} {args[1]} \n"
		return f"define {args[0]} \n"
	def as_statement(self, args):
		if(args[0] in entities.keys()):
			raise ValueError(f"Invalid alias: {args[0]}")
		self.redefined_node=args[0]
		return f"as {args[0]}"
	def single_entity(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		var=""
		if(len(args)>1): #se è stato definito l'alias aggiungo in declared_alias altrimenti in defined_entities
			if(args[1] in entities.keys()):
				raise ValueError(f"Invalid alias: {args[1]}")
			if(args[1] in self.declared_alias or args[1]==self.redefined_node):
				raise ValueError(f"Alias already defined: {args[1]}")
			self.declared_alias[args[1]]=args[0]
			var=args[1]
		else:
			if(args[0] in self.defined_entities or args[0]==self.defined_node):
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
		return args
	def args_type(self, args):	
		return args[0]
	def where_statement(self, args):	
		if(len(args)>3):
			if(not args[0] in self.declared_alias.keys() and not args[0] in self.defined_entities):
				raise ValueError(f"Undefined entity or alias: {args[0]}")
			if(not args[2].value in self.attributes[args[0]]):
				raise ValueError(f"Attribute {args[2]} of entity {args[0]} is not defined")
			args_4=self.args_type(args[4])
			if(len(args[4])>1):
				for i in range(1, len(args[4])):
					args_4+=args[4][i]
			return f"{args[0]}{args[1]}{args[2]} {args[3]} {args_4}"
		else:
			find=False
			for entity in self.defined_entities:
				if any(args[0]==attr.value for attr in self.attributes[entity]):
					if(find):
						raise ValueError(f"The reference to the attribute {args[0]} is ambiguous")
					find=True
			if(not find):
				for alias in self.declared_alias.keys():
					if any(args[0]==attr.value for attr in self.attributes[alias]):
						if(find):
							raise ValueError(f"The reference to the attribute {args[0]} is ambiguous")
						find=True
				if(not find):
					raise ValueError(f"Attribute {args[0]} is not defined")
			args_2=self.args_type(args[2])
			if(len(args[2])>1):
				for i in range(1, len(args[2])):
					args_2+=args[2][i]
			return f"{args[0]} {args[1]} {args_2}"
	def guess(self, args):
		return f"{args[0]} {args[1]}\n{args[2]}\n  {args[3]}{args[4]}\n"
	def guess_statement(self, args):
		return f"guess "+ self.print_stat(args)
	def guess_definition(self, args):
		if not any(args[0]==t.value for t in guess):
			raise ValueError(f"{args[0]} is not defined")
		return self.print_stat(args)
	def from_guess(self, args):
		return "  from " + self.print_stat(args)
	def guess_as(self, args):
		return f"as {args[0]}"
	def guess_entity(self, args):
		if(not args[0] in entities.keys()):
			raise ValueError(f"Undefined entity: {args[0]}")
		if(len(args)>1):
			return f"{args[0]} as {args[1]}"
		return f"{args[0]}"
	def guess_times(self, args):
		return self.print_stat(args)
	def inside_brackets(self, args):
		return self.print_stat(args)
	def value(self, args):
		stat=f"{args[0]}"
		name=True
		if(len(args)>1):
			stat=""
			for i in range(len(args)):
				stat+=f"{args[i]}"
		else:
			if(args[0].type!="NAME"):
				name=False
		if(name and not args[0] in guess):
			raise ValueError(f"{args[0]} is not defined")
		return stat
	def condition(self, args):
		return self.print_stat(args)
	def operator(self, args):
		return self.print_stat(args)
	def bool_operator(self, args):
		return self.print_stat(args)
	def in_stat(self,args):
		return self.print_stat(args)
	def with_guess(self, args):
		return f"with"+ self.print_stat(args)
	def brackets(self, args):
		statements=""
		for i in range(len(args)):
			if(args[i]!="(" and args[i]!=")"):
				statements+=" "+args[i]
		return "(" + statements + " )"
	def with_statement(self, args):
		statements=""
		open_bracket=False
		en=""
		for i in range(len(args)):
			statements+=f" {args[i]}"
			if(open_bracket):
				open_bracket=False
				if not any(args[i]==t.value for t in self.with_attributes):
					raise ValueError(f"{args[i]} is not an attribute of {en}")
			if(args[i]=="("):
				open_bracket=True
				self.with_attributes=[]
				en=args[i-1]
				if(not args[i-1] in entities.keys()):
					raise ValueError(f"{args[i-1]} is not defined")
				else:
					self.with_attributes=entities[args[i-1]]
			if(args[i]=="," or args[i]=="("):
				open_bracket=True
				token=args[i+3]
				if(token[0].type=="NAME"):
					if(not (token[0].value in guess)):
						raise ValueError(f"{token[0].value} is not defined")
				temp=args[i+3]
				args[i+3]=""
				for t in temp:
					args[i+3]+=t.value
				continue			
		return statements
	def where_guess(self, args):
		statements=""
		for i in range(len(args)):
			if(args[i]!=","):
				statements+=args[i]
				if(not args[i] in guess):
					raise ValueError(f"{args[i]} is not defined")
			else:
				statements+=", "
		return f"where {statements}"
	def times(self, args):
		return args[0]
	def print_stat(self, args):
		statements=f"{args[0]}"
		for i in range(1, len(args)):
			if(args[i]==","):
				statements+=f"{args[i]}"
			else:
				statements+=f" {args[i]}"
		return statements


if __name__ == '__main__':
	code="""
@entity color: value: any;
@entity node: value: int;
@entity edge: node1: node, node2: node;
@entity assign: node: node, color: color;

define node as n
    from edge, edge as e2
	where node1=n and e2.node1=n;

define color as c
    from assign, node as n
	where color=c and value=5;


guess exactly 1 a: (c) with assign(node=n, color=c) as a 
	from node as n, color as c
		where n

"""
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
	
