import fileinput
import random
import re
import subprocess
from optparse import OptionParser
from lark import Lark, Transformer, exceptions, Token
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

records = {}
guess={}
guess_alias={}
guess_records={}
number=0
g=Graph()
num_pred={}
num=0
list_show=[]
asp_block=""
recursive=False

grammar = """
	start:  _statement+
	_statement: record | define | guess | assert_ | deny_ | try_assert | try_deny | show | asp_block
	record: "record" record_declaration SEMICOLON
	record_declaration: RECORD_NAME COLON declarations
	declarations: declaration (COMMA declaration)*
	declaration: NAME COLON attr_type
	define: def_1 | def_2 | def_3
	def_1: define_definition define_from? define_where ";"
	def_2: define_definition define_from? define_where aggregate ";"
	def_3: define_definition define_from? aggregate SEMICOLON
	define_definition: "define" RECORD_NAME as_statement?
	as_statement: "as" NAME
	define_from: "from" define_record (COMMA define_record)*
	define_record: NOT? RECORD_NAME ("as" NAME)?
	define_where: "where" where_define_statement (AND where_define_statement)* 
	where_define_statement: define_expression operator define_expression
	guess: guess_def_1 | guess_def_2
	guess_def_1: "guess" from_guess where_guess? guess_times? guess_definitions SEMICOLON
	guess_def_2: "guess" from_guess where_guess? guess_aggregate guess_times? guess_definitions SEMICOLON
	from_guess: "from" guess_record (COMMA guess_record)*
	guess_record: NOT? RECORD_NAME ("as" NAME)?
	where_guess: "where"  where_guess_statement (AND where_guess_statement)*
	where_guess_statement: var_guess_exp (operator var_guess_exp)
	guess_times: times times_exp (AND guess_times)*
	times_exp: (INT| times_value | range2) | times_exp (PLUS | MINUS | TIMES | DIVIDED_BY) times_exp | OB times_exp CB
	guess_definitions: guess_definition+
	guess_definition: RECORD_NAME ("as" NAME)? guess_declaration
	guess_declaration: guess_from? guess_where
	guess_from: "from" record_guess (COMMA record_guess)*
	record_guess: NOT? RECORD_NAME ("as" NAME)?
	guess_where: "where"  guess_where_statement (AND guess_where_statement)*
	guess_where_statement: var_guess_exp_2 operator var_guess_exp_2
	assert_: assert_statement SEMICOLON
	deny_: deny SEMICOLON
	assert_statement: assert_1 | assert_2 | assert_3
	assert_1: assert_definition assert_from? where_assert
	assert_2: assert_definition assert_from? where_assert aggregate
	assert_3: assert_definition assert_from? aggregate
	assert_definition: "deny unless" assert_records (OR assert_records)*
	assert_records: RECORD_NAME ("as" NAME)?
	assert_from: "from" assert_record (COMMA assert_record)*
	assert_record: NOT? RECORD_NAME ("as" NAME)?
	where_assert: "where" where_assert_statement (AND where_assert_statement)*
	where_assert_statement: var_expression operator var_expression
	deny: deny_1 | deny_2
	deny_1: "deny" deny_from where_deny aggregate?
	deny_2: "deny" deny_from aggregate
	deny_from: "from" deny_record (COMMA deny_record)*
	deny_record: NOT? RECORD_NAME ("as" NAME)?
	where_deny: "where" where_deny_statement (AND where_deny_statement)*
	where_deny_statement: var_expression operator var_expression
	try_assert: assert_otherwise "otherwise" pay_statement SEMICOLON
	assert_otherwise: assert_otherwise_1 | assert_otherwise_2 | assert_otherwise_3 | assert_otherwise_4
	assert_otherwise_1: assert_definition assert_from? where_assert
	assert_otherwise_2: assert_definition assert_from? where_assert aggregate
	assert_otherwise_3: assert_definition assert_from? aggregate
	assert_otherwise_4: assert_definition
	pay_statement: "pay" arithmetic_operation "at" arithmetic_operation
	try_deny: deny_otherwise "or" pay_statement SEMICOLON
	deny_otherwise: deny_otherwise_1 | deny_otherwise_2 | deny_otherwise_3
	deny_otherwise_1: "deny" deny_from where_deny aggregate?
	deny_otherwise_2: "deny" deny_from aggregate
	deny_otherwise_3: "deny" deny_from
	pay: (NAME | RECORD_NAME) (DOT NAME)+
	arithmetic_operation: (pay | INT | range2) | (PLUS | MINUS | TIMES | DIVIDED_BY) INT | arithmetic_operation (PLUS | MINUS | TIMES | DIVIDED_BY) arithmetic_operation | OB arithmetic_operation CB
	guess_aggregate: "having" aggr_def_guess (AND aggr_def_guess)*
	aggr_def_guess: (COUNT | SUM_OF | MIN | MAX) "{" aggr_body_guess (SEMICOLON aggr_body_guess)* "}" operator aggregate_term_guess_exp
	aggr_body_guess: aggr_body_guess1 | aggr_body_guess2
	aggr_body_guess1: aggr_records_guess aggregate_from_guess? aggr_where_guess
	aggr_body_guess2: aggr_records_guess aggregate_from_guess?
	aggr_records_guess: aggregate_expression (COMMA aggregate_expression)*
	aggregate_from_guess: "from" aggr_record_guess (COMMA aggr_record_guess)*
	aggr_record_guess: NOT? RECORD_NAME ("as" NAME)?
	aggr_where_guess: "where" where_aggr_guess (AND where_aggr_guess)*
	where_aggr_guess: aggr_guess_exp operator aggr_guess_exp
	aggregate_term_guess_exp: aggregate_term_guess  | aggregate_term_guess_exp (PLUS | MINUS | TIMES | DIVIDED_BY) aggregate_term_guess_exp | OB aggregate_term_guess_exp CB
	aggregate_term_guess: ((NAME | RECORD_NAME) (DOT NAME)*)| INT
	aggregate: "having" aggr_def (AND aggr_def)*
	aggr_def: (COUNT | SUM_OF | MIN | MAX) "{" aggr_body (SEMICOLON aggr_body)* "}" operator aggregate_term_exp
	aggr_body: aggr_body_1 | aggr_body_2
	aggr_body_1: aggr_records aggregate_from? aggr_where
	aggr_body_2: aggr_records aggregate_from?
	aggr_records: aggregate_expression (COMMA aggregate_expression)*
	aggregate_from: "from" aggr_record (COMMA aggr_record)*
	aggr_record: NOT? RECORD_NAME ("as" NAME)?
	aggr_where: "where" where_aggr_statement (AND where_aggr_statement)*
	where_aggr_statement: exp_aggr_define operator exp_aggr_define
	show: "show" RECORD_NAME (COMMA RECORD_NAME)* SEMICOLON
	asp_block: "@asp_block" "$" asp "$"
	define_expression: var_define | define_expression (PLUS | MINUS | TIMES | DIVIDED_BY) define_expression | OB define_expression CB
	var_expression: var | var_expression (PLUS | MINUS | TIMES | DIVIDED_BY) var_expression | OB var_expression CB
	aggregate_expression: (aggregate_record|INT) | aggregate_expression (PLUS | MINUS | TIMES | DIVIDED_BY) aggregate_expression | OB aggregate_expression CB
	aggregate_record: (NAME | RECORD_NAME) (DOT NAME)* 
	aggregate_term_exp: aggregate_term | aggregate_term_exp (PLUS | MINUS | TIMES | DIVIDED_BY) aggregate_term_exp | OB aggregate_term_exp CB
	aggregate_term: ((NAME | RECORD_NAME) (DOT NAME)*) | INT | range
	var_guess_exp: var_guess | var_guess_exp (PLUS | MINUS | TIMES | DIVIDED_BY) var_guess_exp | OB var_guess_exp CB
	asp: /[^$]+/
	var_guess:  INT | STR | value_guess | range
	value_guess: (NAME | RECORD_NAME) (DOT NAME)*
	times_value: (NAME | RECORD_NAME) (DOT NAME)+
	value: (NAME | RECORD_NAME) (DOT NAME)*
	var_guess_exp_2: var_guess_2  | var_guess_exp_2 (PLUS | MINUS | TIMES | DIVIDED_BY) var_guess_exp_2 | OB var_guess_exp_2 CB
	var_guess_2:  INT | STR | value_guess_2 | range
	var: INT | STR | value | range
	value_guess_2: (NAME | RECORD_NAME) (DOT NAME)*	
	var_define: INT | STR | value_define | range
	range: INT DOT DOT INT
	range2: range
	aggr_guess_exp: var_aggr_guess | aggr_guess_exp (PLUS | MINUS | TIMES | DIVIDED_BY) aggr_guess_exp | OB aggr_guess_exp CB
	exp_aggr_define: var_aggr_define | exp_aggr_define (PLUS | MINUS | TIMES | DIVIDED_BY) exp_aggr_define | OB exp_aggr_define CB
	var_aggr_define: INT | STR | value_aggr_define | range
	var_aggr_guess: INT | STR | value_aggr_guess | range
	value_aggr_define: (NAME | RECORD_NAME) (DOT NAME)*	
	value_aggr_guess: (NAME | RECORD_NAME) (DOT NAME)*	
	value_define: (NAME | RECORD_NAME) (DOT NAME)*	
	operator: op+
	op:  EQUALITY | LT | LE | GT | GE | NOTEQUAL | ASSIGN
	bool_operator: AND | OR
	times: EXACTLY | ATLEAST | ATMOST
	attr_type: ANY | STRING | INTEGER | RECORD_NAME | REGEX
	REGEX: "r"/"[^"]+"/
	NAME: /[a-z_][a-z0-9_]*/
	RECORD_NAME: /[A-Z][a-zA-Z0-9_]*/
	COLON: ":"
	SEMICOLON: ";"
	COMMA: ","
	DOT: "."
	PLUS: "+"
	MINUS: "-"
	TIMES: "*"
	DIVIDED_BY: "/"
	OB: "("
	CB: ")"
	EQUALITY: "=="
	NOTEQUAL: "!="
	GE: ">="
	GT: ">"
	LT: "<"
	LE: "<="
	ASSIGN: "="
	AND: "and"
	NOT: "not"
	OR: "or"
	COUNT: "count"
	SUM_OF: "sum"
	EXACTLY: "exactly"
	ATLEAST: "at least"
	ATMOST: "at most"
	ANY: "any"
	STRING: "str"
	INTEGER: "int"
	MAX: "max"
	MIN: "min"
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
		guess_records[0]={}
		guess_alias[0]["number"]=0
	def record_declaration(self, args):
		record_name= args[0]
		declarations=args[2].children
		if(record_name in records.keys()):
			raise ValueError(f"Record already defined: {record_name}")
		records[record_name]=[]
		for i in range(0, len(declarations), 2):
			attr=declarations[i].children
			token=attr[2].children
			attr_type=token[0] 
			if(attr_type==record_name):
				raise ValueError("Recursive dependencies between records")
			attr[0].type=str(attr_type)
			records[record_name].append(attr[0])
		return args
	def guess(self, args):
		self.count_guess+=1
		guess[self.count_guess]=[]
		guess_records[self.count_guess]={}
		guess_alias[self.count_guess]={}
		guess_alias[self.count_guess]["number"]=0
	def guess_definition(self, args):
		if(len(args)>=3):
			if(args[1] in guess_records[self.count_guess].keys()):
				raise ValueError(f"Alias already defined: {args[1]}")
			guess_alias[self.count_guess][args[1]]=self.add_number(args[1])
			guess_records[self.count_guess][args[1]]=args[0]
		else:
			if(args[0] in guess_records[self.count_guess].keys()):
				raise ValueError(f"Record already defined: {args[0]}")
			guess_alias[self.count_guess][args[0]]=self.number(args[0])
			guess_records[self.count_guess][args[0]]=args[0]
		guess_alias[self.count_guess]["number"]+=1
	def guess_record(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		if(len(args)>index+1):
			if(args[index+1] in guess_records[self.count_guess].keys()):
				raise ValueError(f"Alias already defined: {args[index+1]}")
			guess_records[self.count_guess][args[index+1]]=args[index]
			guess[self.count_guess].append(args[index+1])
		else:
			if(args[index] in guess_records[self.count_guess].keys()):
				raise ValueError(f"Record already defined: {args[index]}")
			guess_records[self.count_guess][args[index]]=args[index]
			guess[self.count_guess].append(args[index])
	def record_guess(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		if(len(args)>index+1):
			if(args[index+1] in guess_records[self.count_guess].keys()):
				raise ValueError(f"Alias already defined: {args[index+1]}")
		else:
			if(args[index] in guess_records[self.count_guess].keys()):
				raise ValueError(f"Record already defined: {args[index]}")
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
		self.declared_alias={}
		self.defined_records=set()
		self.attributes={}
		self.defined_record=set()
		self.redefined_record={}
		self.new_define_alias={}
		self.new_guess_alias={}
		self.guess_alias={}
		self.guess_records=set()
		self.count_guess=0
		self.guess_count=guess_alias[0]["number"]
		self.count_define=0
		self.dependencies={}
		self.guess_check=[]
		self.statement=""
		self.otherwise_en=[]
		self.aggregate_records=set()	
		self.aggr_guess_record=[]
		self.aggr_alias=[]
		self.aggr_new_alias={}
		self.aggregate_with=[]
		self.records_attributes=[]
		self.negated_atoms=[]
		self.negated={}
		self.define_expressions=[]
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
				raise ValueError("Circular dependencies detected between records")
			else:
				length+=1
		ordered.append(f"\nproblem{self.problem} = Problem()\n\n")
		ordered.extend(others)
		return "".join(ordered)	
	def negated_atoms_check(self, args):
		for neg in self.negated.keys():
			replace_string=""
			keys=self.find_false_keys(self.negated[neg])
			for i in range(len(keys)):
				splitted=keys[i].split(".")
				if(replace_string!=""):
					replace_string+=", "
				replace_string+=f"{splitted[0]}="
				count=0
				fixed =str(neg)
				pattern = re.compile(r'((([A-Z][a-zA-Z0-9_]*))\(\)\s+as\s+{})(?:\s|,|:)'.format(re.escape(fixed)))
				match = pattern.search(args[0])
				term=""
				toReplace=""
				if match:
					term = match.group(2)
					toReplace=match.group(1)
				for split in splitted:
					for attr in records[term]:
						if(split==attr.value):
							count+=1
							replace_string+=f"{attr.type}({splitted[count]}="
				replace_string+="hide()"
				for c in range(count):
					replace_string+=")"
				args[0]=args[0].replace(toReplace, f"{term}({replace_string}) as {neg}")
		self.negated={}
		return args[0]
	def record(self, args):	
		self.records_attributes=[]
		return f"@atom\n{args[0]}\n"
	def record_declaration(self, args):
		self.dependencies[args[0]]=self.records_attributes
		return f"class {args[0]}:\n{args[2]}"
	def declarations(self, args):
		statements=""
		for i in range(0, len(args)):
			if(args[i]==","):
				statements+="\n"
			else:
				statements+=f"{args[i]}"
		return statements
	def recursive_declaration_checking(self, args, verify_list, attr_list):
		for attr in attr_list:
			if(attr.type!="int" and attr.type!="any" and attr.type!="str"):
				if(attr.type==args):
					raise ValueError("Recursive dependencies between records")
				verify_list.append(attr.type)
		return verify_list
	def declaration(self, args):
		if(args[2] in records.keys()):
			self.records_attributes.append(args[2])
		if not(args[2]=="int" or args[2]=="any" or args[2]=="str"):
			verify_list=self.recursive_declaration_checking(args[2], [], records[args[2]])
			while verify_list!=[]:
				verify=records[verify_list.pop()]
				verify_list=self.recursive_declaration_checking(args[2], verify_list, verify)
		return f"	{args[0]}: {args[2]}"
	def attr_type(self, args):
		return args[0]
	def define(self, args):	
		return self.negated_atoms_check(args)
	def def_1(self, args):
		when=""
		if(len(args)>2):
			when=self.when_define(args[1])
		self.statement=""
		self.find_pattern(args)
		self.init_define_variables()
		if(len(args)>2):
			return f"with {self.statement}:\n{when}{args[2]}"
		stat=f"	problem{self.problem}+=When("
		stat+=args[1][2:]
		return f"with {self.statement}:\n{stat}"
	def def_2(self, args):
		when=""
		if(len(args)>3):
			temp=args[2]
			args[2]=args[3]
			args[3]=temp
			when=self.when_define(args[1])
		self.statement=""
		for aggr in self.aggregate_with:
			args[0]+=", "+aggr
		self.find_pattern(args)
		if(self.aggregate_with!=[]):
			self.addEdge(self.aggregate_with)
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
		for alias in self.redefined_record.values():
			pred_define=alias
		for en in self.defined_record:
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
			if(not args[i]=="and"):
				statements+=f"{args[i]}"
		for alias in self.new_define_alias.keys():
			return statements + f").define({self.new_define_alias[alias]})\n"
	def define_definition(self, args):
		self.declared_alias={}
		self.defined_records=set()
		if(not args[0] in records.keys()):
			 raise ValueError(f"Undefined record: {args[0]}")
		self.attributes={}
		attr=records[args[0]]
		all_attr=[]
		for i in range(len(attr)):
			all_attr.append(attr[i]) 
		self.attributes[args[0]]=all_attr
		if(len(args)>1):
			self.redefined_record[args[1]]=args[0]
			alias=self.add_number(args[1])
			self.new_define_alias[args[1]]=alias
			return f"{args[0]}() as {alias}"
		self.defined_record.add(args[0])
		alias=self.number(args[0])
		self.new_define_alias[args[0].value]=alias
		return f"{args[0]}() as {alias}"
	def as_statement(self, args):
		return f"{args[0]}"
	def build_nested_dictionary(self, alias, args, current_dict=None):
		if current_dict is None:
			current_dict = {}
		for attr in records[args[0]]:
			if attr.type in ("int", "str", "any"):
				current_dict[attr.value] = False
			else:
				current_dict[attr.value] = {}
				self.build_nested_dictionary(alias, [attr.type], current_dict[attr.value])
		return current_dict
	def define_record(self, args):
		negated=False
		if(args[0]=="not"):
			negated=True
			args=args[1:]
		if(not args[0] in records.keys()):
			raise ValueError(f"Undefined record: {args[0]}")
		var=""
		if(len(args)>1):
			if(args[1] in self.declared_alias or args[1] in self.redefined_record.keys()):
				raise ValueError(f"Alias already defined: {args[1]}")
			self.declared_alias[args[1]]=args[0]
			var=args[1]
		else:
			if(args[0] in self.defined_records or args[0] in self.defined_record):
				raise ValueError(f"Record already defined: {args[0]}")
			self.defined_records.add(args[0])
			var=args[0]
		attr=records[args[0]]
		all_attr=[]
		for i in range(len(attr)):
			all_attr.append(attr[i]) 
		self.attributes[var]=all_attr
		if(len(args)>1):
			alias=self.add_number(args[1])
			self.new_define_alias[args[1].value]=alias
			if(negated):
				self.negated[alias]={}
				self.negated[alias]=self.build_nested_dictionary(alias, args)
				self.negated_atoms.append(alias)
			return f"{args[0]}() as {alias}"
		alias=self.number(args[0])
		self.new_define_alias[args[0].value]=alias
		if(negated):
			self.negated[alias]={}
			self.negated[alias]=self.build_nested_dictionary(alias, args)
			self.negated_atoms.append(alias)
		return f"{args[0]}() as {alias}"
	def var_expression(self,args):
		return self.define_expression(args)
	def var(self, args):
		return self.var_define(args)
	def value(self, args):
		statement=""
		record=args[0]
		if(not (args[0] in self.defined_record or args[0] in self.redefined_record.keys())):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_records):
					raise ValueError(f"{args[0]} is not defined")
		attribute=self.attributes_check(args)
		if(args[0] in self.new_define_alias.keys()):
			args[0]=self.new_define_alias[args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement + "/" + attribute
	def define_expression(self,args):
		stat=f""
		operators=["*","+","-","$"]
		integer=False
		for o in operators:
			for i in range(len(args)):
				if o in args[i]:
					integer=True
					break	
		if(integer):
			stat=""
			term=""
			for i in range(len(args)):
				if(args[i]=="(" or args[i]==")"):
					stat+=args[i]
					continue
				if(args[i]=="/"):
					args[i]="$"
				if("/" in args[i]):
					types=args[i].split("/")
					if(types[1]!="int" and types[1]!="any"):
						raise ValueError("Unsupported arithmetic operation. Unable to perform the operation on a non-numeric data type.")
					args[i]=types[0]
					self.define_expressions.append(args[i])
					term="/"+types[1]
				stat+=args[i]
			stat+=term
		else:
			types=[]
			self.define_expressions.append(args[0])
			for i in range(len(args)):
				if("/"==args[i]):
					stat+="$"
					continue
				if("/" in args[i]):
					types=args[i].split("/")
					args[i]=types[0]
				if not (args[i]=="(" or args[i]==")"):
					stat+=args[i]
			if(types!=[]):
				stat+="/"+str(types[1])
		return stat
	def var_define(self, args):
		if(isinstance(args[0], Token)):
			type_value=args[0].type.lower()
			if(type_value=="str"):
				args[0]=f"'{args[0]}'"
			args[0]+=f"/{type_value}"
		return self.print_stat(args)
	def exp_aggr_define(self, args):
		stat=""
		operators=["*","+","-","$"]
		integer=False
		for o in operators:
			for i in range(len(args)):
				if o in args[i]:
					integer=True
					break	
		if(integer):
			stat=""
			term=""
			for i in range(len(args)):
				if(args[i]==")" or args[i]=="("):
					stat+=args[i]
					continue
				if(args[i]=="/"):
					args[i]="$"
				if("/" in args[i]):
					types=args[i].split("/")
					if(types[1]!="int" and types[1]!="any"):
						raise ValueError("Unsupported arithmetic operation. Unable to perform the operation on a non-numeric data type.")
					args[i]=types[0]
					term="/"+types[1]
				stat+=args[i]
			stat+=term
		else:
			types=[]
			for i in range(len(args)):
				if("/"==args[i]):
					stat+="$"
					continue
				if("/" in args[i]):
					types=args[i].split("/")
					args[i]=types[0]
				if not (args[i]=="(" or args[i]==")"):
					stat+=args[i]
			if(types!=[]):
				stat+="/"+str(types[1])
		return stat
	def var_aggr_define(self, args):
		return self.var_define(args)
	def value_def(self, args):
		statement=""
		record=args[0]
		attribute=self.attributes_check(args)
		if(args[0] in self.new_define_alias.keys()):
			args[0]=self.new_define_alias[args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement + "/" + attribute
	def value_aggr_define(self, args):
		if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_records):
					raise ValueError(f"{args[0]} is not defined")
		return self.value_def(args)
	def value_define(self, args):
		if(not (args[0] in self.redefined_record.keys() or args[0] in self.defined_record)):
			if(not args[0] in self.declared_alias.keys()and not args[0] in self.defined_records):
					raise ValueError(f"{args[0]} is not defined")
		return self.value_def(args)
	def range(self, args):
		return f"domain({args[0]}, {args[3]})/int"
	def range2(self, args):
		splitted=args[0].split("/")
		return splitted[0]
	def var_guess_exp(self,args):
		return self.exp_aggr_define(args)
	def aggr_guess_exp(self, args):
		return self.exp_aggr_define(args)
	def var_aggr_guess(self, args):
		return self.var_define(args)
	def value_aggr_guess(self, args):
		if(not args[0] in guess_records[self.count_guess].keys() and not args[0] in self.aggr_guess_record):
			raise ValueError(f"{args[0]} is not defined")
		return self.value_guess_check(args)
	def var_guess(self, args):
		return self.var_define(args)
	def value_guess(self, args):
		if(not args[0] in guess_records[self.count_guess].keys()):
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
	def times_exp(self, args):
		stat=""
		for i in range(len(args)):
			if(args[i]==")" or args[i]=="("):
				stat+=args[i]
				continue
			if(args[i]=="/"):
				args[i]="$"
			stat+=args[i]
		return stat
	def times_value(self, args):
		statement=""
		if not (args[0] in  guess_records[self.count_guess].keys()):
				raise ValueError(f"Record not defined: {args[0]}")
		attribute=self.attributes_guess_check(args)
		if(attribute!="int" and attribute!="any"):
			raise ValueError(f"Expected int, received: {attribute}")
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		elif(args[0] in guess_alias[self.count_guess].keys()):
			args[0]=guess_alias[self.count_guess][args[0]]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement
	def var_guess_exp_2(self, args):
		return self.exp_aggr_define(args)
	def var_guess_2(self, args):
		return self.var_define(args)
	def value_guess_2(self, args):
		if not (args[0] in self.guess_alias.keys() or args[0] in self.guess_records or args[0] in guess_records[self.count_guess].keys()):
			raise ValueError(f"{args[0]} is not defined")
		elif(args[0] in self.aggr_alias):
			raise ValueError(f"{args[0]} is not defined")
		return self.value_guess_check(args)
	def isNum(self,args):
		num=True
		try:
			number=int(args)
		except:
			num=False
		return num
	def access_nested_dict(self, dictionary, keys):
		if not keys:
			return
		curr_keys = keys[0]
		if curr_keys in dictionary:
			nested_dictionary = dictionary[curr_keys]
			if len(keys) == 1:
				dictionary[curr_keys] = True
			else:
				return self.access_nested_dict(nested_dictionary, keys[1:])
		else:
			pass
	def where_stat_check(self, args):
		if(args[-2]=="="):
			raise TypeError("Unexpected operator \"=\". Did you mean to use \"==\" instead?")
		splitted=args[0].split("/")
		attribute=splitted[1]
		statement=", "
		types=args[-1].split("/")
		if(self.isNum(types[0]) and self.isNum(args[0])):
			raise ValueError(f"Unexpected boolean condition: {args[0]}{args[1]}{types[0]}")
		args[0]=splitted[0]
		if(not types[1]==attribute and attribute!="any"):
			if(args[-2]!="=="):
				raise ValueError(f"{types[1]} cannot be compared with type: {attribute}")
			raise ValueError(f"{types[1]} cannot be assigned to type {attribute}")
		if(self.negated_atoms!=[]):
			self.check_negated_atoms(args)	
		if(attribute!="str" and attribute!="int" and attribute!="any"):
			return ", Literal(Atom(Predicate(f\"{"+f"{args[0]}"+"}"+f"{args[-2]}"+"{"+f"{types[0]}"+"}\")), True)"
		args[-1]=types[0]
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement
	def where_define_statement(self, args):
		for exp in self.define_expressions:
			if("." in exp):
				rec=exp.split(".")[0]
				if(rec in self.aggr_new_alias.keys()):
					raise ValueError(f"{self.aggr_new_alias[rec]} is not defined")
			else:
				rec=exp.split("/")[0]
				if(rec in self.aggr_new_alias.keys()):
					raise ValueError(f"{self.aggr_new_alias[rec]} is not defined")
		self.define_expressions=[]
		return self.where_stat_check(args).replace("$","/")	
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
		statement=", "
		args=self.guess_where_check_(args)
		if(args==""):
			return args
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement	
	def where_aggr_statement(self, args):
		return self.where_stat_check(args)
	def check_sum(self, all_en, declared_alias):
		sum_bool=""
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
				for t in records[attribute]:
					if(t.value==temp_array[i]):
						attribute=t.type
						found=True
						break
			if(attribute=="int"):
				sum_bool="True/"
		return sum_bool
	def aggregate_body(self, args, new_alias, declared_alias):
		self.aggregate_records=set()
		var = re.findall(r'\b(?:\w+(?:\.\w+)*|\S+)\b', args[0][0][0])
		sum_bool="True/"
		sum_array=[]
		for v in var:
			num=True
			try:
   				n=int(v)
			except ValueError:
				num=False
			if(not num):
				sum_bool=self.check_sum(v, declared_alias)
				if("False/" in sum_bool):
					sum_array.append(False)
				else:
					sum_array.append(True)
			else:
				sum_array.append(True)	
		if(len(var)>1 and False in sum_array):
			raise ValueError("Unsupported arithmetic operation. Unable to perform the operation on a non-numeric data type.")
		stat="("
		for attr in args[0][0]:
			if(attr!=","):
				var = re.findall(r'[\w.]+|\S', attr)
				for v in var:
					if("." in v):
						temp=v
						splitted=temp.split(".")
						alias=splitted[0]
						v=f"{new_alias[alias]}.{'.'.join(splitted[1:])}"
					elif(v in new_alias.keys()):
						v=new_alias[v]	
					stat+=v
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
		self.aggr_guess_record=[]
		return self.aggregate_body(args, self.new_guess_alias, self.guess_alias)
	def aggr_body(self,args):
		return self.aggregate_body(args, self.new_define_alias, self.declared_alias)
	def aggr_body_guess1(self, args):
		if(len(args)<=2):
			self.aggregate_check(args,self.guess_alias, self.guess_records)
		else:
			length=len(self.aggregate_with)
			self.aggregate_with+=args[1].split(",")
			if(length==len(self.aggregate_with)):
				self.aggregate_with+=args[1]
		return args
	def aggr_body_1(self, args):
		if(len(args)<=2):
			self.aggregate_check(args,self.declared_alias, self.defined_records)
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
			self.aggregate_check(args, self.guess_alias, self.guess_records)
		return args
	def aggr_body_2(self, args):
		if(len(args)>1):
			length=len(self.aggregate_with)
			self.aggregate_with+=args[1].split(",")
			if(length==len(self.aggregate_with)):
				self.aggregate_with+=args[1]
		else:
			self.aggregate_check(args, self.declared_alias, self.defined_records)
		return args
	def aggr_records_guess(self, args):
		return args
	def aggr_records(self, args):
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
				if(not ":" in bool_sum[0]):
					bool_sum[1]=bool_sum[0]+"/"+bool_sum[1]
					bool_sum=bool_sum[1:]
				if(args[0]!="count" and bool_sum[1]!="True"):	
					raise ValueError(f"Expected int, received {bool_sum[2]}")
				args[i]=bool_sum[0]
			if(args[i]==";"):
				args[i]=", "
			stat+=args[i]
		stat+="})"+f"{args[-2]}{args[-1]}"
		function=""
		if(args[0]=="count"):
			function="Count"
		elif(args[0]=="min"):
			function="Min"
		elif(args[0]=="max"):
			function="Max"
		else:
			function="Sum"
		return function+"({"+f"{stat.replace('$','/')}"
	def aggregate_term_exp(self, args):
		return self.exp_aggr_define(args)
	def aggregate_term_guess_exp(self, args):
		return self.exp_aggr_define(args)
	def aggregate_term_guess(self, args):
		if(args[0].type=="INT"):
			return args[0]
		if(args[0] in self.aggr_alias):
			raise ValueError(f"{args[0]} is not defined")
		attribute=self.value_guess(args)
		types=attribute.split("/")
		if(not types[1]=="int"):
			raise ValueError(f"Expected int, received {types[1]}: {types[0]}")
		return types[0]
	def aggregate_term(self, args):	
		splitted=args[0].split("/")
		if(len(splitted)>1):
			return splitted[0]
		if(args[0].type=="INT"):
			return args[0]
		return self.pay(args)
	def aggregate_check(self, args, declared_alias, defined_records):
		for en in self.aggregate_records:
			all_en=""
			attribute=""
			if("." in en):
				all_en=en
				en=en.split(".")[0]
			if not (en in declared_alias.keys() or en in defined_records):
				raise ValueError(f"Undefined record: {en}")
			if(all_en!=""):	
				if(en in declared_alias.keys()):
					attribute=declared_alias[en]
				else:
					attribute=en
				temp_array=all_en.split(".")[1:]
				for i in range(len(temp_array)):
					if(attribute=="str" or attribute=="int"):
						raise ValueError(f"{attribute} object has no attribute {temp_array[i]}")		
					found=False
					for t in records[attribute]:
						if(t.value==temp_array[i]):
							attribute=t.type
							found=True
							break
					if not found:
						raise ValueError(f"{attribute} object has no attribute {temp_array[i]}")
	def aggregate_expression(self, args):	
		return self.print_stat(args)		
	def aggregate_record(self, args):
		stat="".join(args)
		self.aggregate_records.add(stat)
		return stat
	def aggregate_from_guess(self, args):
		self.aggregate_check(args, self.guess_alias, self.guess_records)
		return self.print_stat(args)
	def aggregate_from(self,args):
		self.aggregate_check(args, self.declared_alias, self.defined_records)
		return self.print_stat(args)
	def aggr_record_guess(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		global g, recursive
		self.increment_num(args[index])
		check=index	
		if(len(args)-index>1):
			check=index+1
		if(args[check] in self.aggr_alias or args[check] in guess_records[self.count_guess].keys()):
			if(check!=index):
				raise ValueError(f"Alias already defined: {args[check]}")
			raise ValueError(f"Record already defined: {args[check]}")
		for alias in guess_alias[self.count_guess].keys():
			if(alias!="number"):
				en=guess_records[self.count_guess][alias]
				if(recursive and en==args[index]):
					raise ValueError("Cyclic dependency detected")
				self.increment_num(en)
				g.addEdge(num_pred[args[index]], num_pred[en])
		if(len(args)>index+1):
			self.aggr_guess_record.append(args[index+1])
			self.aggr_alias.append(args[index+1])
		else:
			self.aggr_guess_record.append(args[index])
			self.aggr_alias.append(args[index])
		return_value=self.guess_record(args)
		if(len(args)>index+1):	
			self.aggr_new_alias[self.new_guess_alias[args[index+1]]]=args[index+1]
		else:
			self.aggr_new_alias[self.new_guess_alias[args[index]]]=args[index]
		return return_value
	def aggr_record(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		if(len(args)>index+1):
			self.aggr_alias.append(args[index+1])
		else:
			self.aggr_alias.append(args[index])
		return_value=self.define_record(args)
		if(len(args)>index+1):	
			self.aggr_new_alias[self.new_define_alias[args[index+1]]]=args[index+1]
		else:
			self.aggr_new_alias[self.new_define_alias[args[index]]]=args[index]
		return return_value	
	def guess(self,args):
		return self.negated_atoms_check(args).replace("$","/")
	def guess_def(self, args, index):
		length=index
		self.statement=""
		cond=""
		pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
		if(len(args)==length+1):
			index-=1
		elif(len(args)==length):
			index-=2
		match = re.findall(pattern, args[0])
		if match:
			for var in match:
				self.statement+=var[0]+", "
		pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)((.*?)/(.*?))\\'
		match = re.findall(pattern, args[index])
		if match:
			for var in match:
				self.statement+=var[0]+", "
				cond+=f"{var[2]}:("
				pattern2 = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
				match2 = re.findall(pattern2, var[3])
				if match2:
					for var2 in match2:
						self.statement+=var2[0]+", "
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
		self.statement=self.statement[:-2]
		self.statement+=f":\n	problem{self.problem}+=When("
		if match:
			for var in match:
				if var[2] in self.negated_atoms:
					self.statement+="~"
				self.statement+=var[2]+", "
			self.statement=self.statement[:-1]
		self.count_guess+=1
		self.guess_count=guess_alias[self.count_guess]["number"]
		self.new_guess_alias={}
		self.guess_alias={}
		self.guess_check=[]
		self.guess_records=set()
		self.aggregate_records=set()
		self.aggregate_with=[]
		self.aggr_alias=[]
		self.aggr_new_alias={}
		self.negated_atoms=[]
	def guess_def_1(self, args):
		cond=self.guess_def(args, 3)
		self.guess_def_check(args)
		if(len(args)==4):
			if("exactly" in args[1] or "at least" in args[1] or "at most" in args[1]):
				args[1]=args[1].replace("at least", "at_least")
				args[1]=args[1].replace("at most", "at_most")
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
		args[2]=args[2].replace("at least", "at_least")
		args[2]=args[2].replace("at most", "at_most")
		substring = args[1].split(" , ")
		args[1] = " ".join(substring)
		if(len(args[1])>2):
			if(args[1][0]==","):
				args[1]=args[1][2:]
			if(args[1][-2]==","):
				args[1]=args[1][:-2]
		return f"with {self.statement} {args[1]}).guess("+"{"+f"{cond}"+"}"+f", {args[2]}"+")"+"\n"
	def guess_def_2(self, args):	
		if (len(args)==5 and not ("exactly" in args[2] or "at least" in args[2] or "at most" in args[2])) or len(args)==6:
			temp=args[1]
			args[1]=args[2]
			args[2]=temp
		cond=self.guess_def(args, 4)
		pattern = r'(([A-Z]+[a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
		if(self.aggregate_with!=[]):
			for i in range(len(self.aggregate_with)):
				match = re.findall(pattern, self.aggregate_with[i])
				if match:
					for var in match:
						self.statement+=var[0]+", "
		self.guess_def_check(args)
		if(len(args)==5):
			if("exactly" in args[2] or "at least" in args[2] or "at most" in args[2]):
				args[2]=args[2].replace("at least", "at_least")
				args[2]=args[2].replace("at most", "at_most")
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
		args[3]=args[3].replace("at least", "at_least")
		args[3]=args[3].replace("at most", "at_most")
		substring = args[2].split(" , ")
		args[2] = " ".join(substring)
		if(len(args[2])>2):
			if(args[2][0]==","):
				args[2]=args[2][2:]
			if(args[2][-2]==","):
				args[2]=args[2][:-2]
		return f"with {self.statement} {args[1]}, {args[2]}).guess("+"{"+f"{cond}"+"}"+f", {args[3]}"+")"+"\n"
	def guess_definitions(self, args):
		return self.print_stat(args)
	def guess_definition(self, args):
		from_guess=args[-1].split("/")[0]
		if(len(from_guess)>0):
			self.addEdge_guess(from_guess, args[0])
		if not(args[0] in records.keys()):
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
			self.guess_records=set()
			return f"{args[0]}() as {alias} {args[2]}"
		elif(args[0] in self.guess_records):
			raise ValueError(f"Record already defined: {args[0]}")
		for en in self.guess_check:
			if(en!=args[0]):
				raise ValueError(f"Record is not defined: {en}")
		self.guess_check=[]
		self.guess_alias={}
		self.guess_records=set()
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
				en=guess_records[self.count_guess][alias]
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
	def guess_record(self, args):
		negated=False
		if(args[0]=="not"):
			negated=True
			args=args[1:]
		if(not args[0] in records.keys()):
			raise ValueError(f"Undefined record: {args[0]}")
		if(len(args)>1):
			alias=self.add_number_guess(args[1])
			self.new_guess_alias[args[1]]=alias
			self.guess_alias[args[1]]=args[0]
			if(negated):	
				self.negated[alias]={}
				self.negated[alias]=self.build_nested_dictionary(alias, args)
				self.negated_atoms.append(alias)
			return f"{args[0]}() as {alias}"
		alias=self.number_guess(args[0])
		self.new_guess_alias[args[0]]=alias
		self.guess_records.add(args[0])
		if(negated):
			self.negated[alias]={}
			self.negated[alias]=self.build_nested_dictionary(alias, args)
			self.negated_atoms.append(alias)
		return f"{args[0]}() as {alias}"
	def guess_times(self, args):
		statements=f""
		for i in range(0, len(args)):
			if(args[i]=="and"):
				args[i]=", "
			if(args[i]=="exactly=" and len(args)>2):
				raise ValueError("exactly is incompatible with at least and at most")
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
		statement=""
		args=self.guess_where_check_(args)
		if(args==""):
			return args
		for i in range(len(args)):
			statement+=f"{args[i]}"
		return statement		
	def guess_from(self, args):
		return self.print_stat(args)
	def record_guess(self, args):
		negated=False
		if(args[0]=="not"):
			negated=True
			args=args[1:]
		if(not args[0] in records.keys()):
			raise ValueError(f"Undefined record: {args[0]}")
		if(len(args)>1):
			alias=self.add_number_guess(args[1])
			if(args[1] in self.guess_alias.keys()):
				raise ValueError(f"Alias already defined: {args[1]}")
			self.guess_alias[args[1]]=args[0]
			self.new_guess_alias[args[1]]=alias
			if negated:
				self.negated[alias]={}
				self.negated[alias]=self.build_nested_dictionary(alias, args)
				self.negated_atoms.append(alias)
			return f"{args[0]}() as {alias}"
		alias=self.number_guess(args[0])
		if(args[0] in self.guess_records):
			raise ValueError(f"Record already defined: {args[0]}")
		self.guess_records.add(args[0])
		self.new_guess_alias[args[0]]=alias
		if negated:
			self.negated[alias]={}
			self.negated[alias]=self.build_nested_dictionary(alias, args)
			self.negated_atoms.append(alias)
		return f"{args[0]}() as {alias}"
	def remove_and(self,args):
		statements=""
		for i in range(len(args)):
			if(args[i]=="and"):
				if(args[i+1]=="" or args[i-1]==""):
					args[i]=""
				else:
					if(args[i+1].startswith(",")):
						args[i+1]=args[i+1][1:]
					args[i]=","
			if(args[i]!=""):
				statements+=args[i]
		return statements
	def check_negated_atoms(self, args):
		for neg in self.negated_atoms:
			arg=""
			if(neg in args[0]):
				arg=args[0]
			elif(neg in args[-1]):
				arg=args[-1]
			if(arg!=""): 
				pattern=re.compile(r'{}((?:\.[a-zA-Z0-9_]+)+)'.format(re.escape(neg)))
				match = pattern.search(arg)
				if match:
					terms = match.group(1).split('.')
					self.access_nested_dict(self.negated[neg], terms[1:])
	def guess_where(self, args):
		statements=self.remove_and(args)
		return "/"+ statements+"\\"
	def guess_where_statement(self, args):
		args=self.guess_where_check_(args)
		if(args==""):
			return ""
		stat=""
		for i in range(len(args)):
			stat+=args[i]
		return stat
	def guess_where_check_(self, args):
		if(args[-2]=="="):
			raise TypeError("Unexpected operator \"=\". Did you mean to use \"==\" instead?")
		splitted=args[0].split("/")
		attribute=splitted[1]
		args[0]=splitted[0]
		statement=", "
		types=args[-1].split("/")
		if(self.isNum(types[0]) and self.isNum(args[0])):
			raise ValueError(f"Unexpected boolean condition: {args[0]}{args[1]}{types[0]}")
		if(not types[1]==attribute and attribute!="any"):
			if(args[-2]!="=="):
				raise ValueError(f"{types[1]} cannot be compared with type: {attribute}")
			raise ValueError(f"{types[1]} cannot be assigned to type {attribute}")
		if(args[0] in self.new_guess_alias.keys()):
			args[0]=self.new_guess_alias[args[0]]
		elif(args[0] in guess_alias[self.count_guess].keys()):
			args[0]=guess_alias[self.count_guess][args[0]]
		if(self.negated_atoms!=[]):
			self.check_negated_atoms(args)
		if(attribute!="str" and attribute!="int" and attribute!="any"):
			return "Literal(Atom(Predicate(f\"{"+f"{args[0]}"+"}"+f"{args[-2]}"+"{"+f"{types[0]}"+"}\")), True)"
		args[-1]=types[0]
		return args		
	def assert_statement(self, args):
		return args[0]
	def assert_1(self,args):
		self.statement=""
		self.find_pattern(args)
		self.init_define_variables()
		if(len(args)>2):
			return f"with {self.statement}:\n	problem{self.problem}+={args[2]}"
		return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"
	def assert_2(self, args):
		if(len(args)==4):
			temp=args[2]
			args[2]=args[3]
			args[3]=temp
		else:
			temp=args[1]
			args[1]=args[2]
			args[2]=temp
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
		for alias in self.redefined_record.keys():
			var.append(self.new_define_alias[alias])
		for record in self.defined_record:
			var.append(self.new_define_alias[record])
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
		return self.negated_atoms_check(args)+"\n"
	def deny_(self, args):
		return self.negated_atoms_check(args)+"\n"
	def find_pattern(self, args):
		pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
		match = re.findall(pattern, args[0])
		if match:
			for var in match:
				self.statement+=var[0]+", "
		if(len(args)>2):
			match = re.findall(pattern, args[1])
			if match:
				for var in match:
					self.statement+=var[0]+", "
		self.statement=self.statement[:-2]
	def init_define_variables(self):
		self.redefined_record={}
		self.defined_record=set()
		self.new_define_alias={}
		self.declared_alias={}
		self.defined_records=set()
		self.attributes={}
		self.aggregate_records=set()
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
	def assert_definition(self, args):
		return self.print_stat(args)
	def assert_records(self,args):
		if(len(args)>1):
			self.redefined_record[args[1]]=args[0]
			self.otherwise_en.append(args[1])
		else:
			self.otherwise_en.append(args[0])
		return self.define_definition(args)
	def assert_from(self, args):
		return self.print_stat(args)
	def assert_record(self, args):
		index=0
		if(args[0]=="not"):
			index=1
		if(len(args)>index+1):
			self.otherwise_en.append(args[index+1])
		else:
			self.otherwise_en.append(args[index])
		return self.define_record(args)
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
		self.statement=""
		self.find_pattern(args)
		if(len(args)>2):
			return f"with {self.statement}:\n	problem{self.problem}+={args[2]}"
		return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"
	def assert_otherwise_2(self, args):	
		index=0
		if(len(args)==4):
			index=1
		temp=args[1+index]
		args[1+index]=args[2+index]
		args[2+index]=temp
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
	def assert_otherwise_4(self, args):
		self.assert_deny_with(args)
		end_assert=""
		var=self.assert_stat()
		var_statement=f"{var[0]}"
		for i in range(1, len(var)):
			var_statement+=f", {var[i]}"
		end_assert="Assert("+var_statement+")"
		return  f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
	def pay_statement(self, args):
		return args[0]+","+args[1]+","
	def try_deny(self, args):
		return self.try_assert(args)
	def deny_otherwise(self, args):
		return args[0]
	def deny_otherwise_1(self, args):
		if(len(args)==3):
			temp=args[2]
			args[2]=args[1]
			args[1]=temp
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
	def deny_otherwise_3(self, args):
		self.assert_deny_with(args)
		pre_statement=""
		for alias in self.new_define_alias.values():
			if not alias in self.aggr_new_alias:
				if(alias in self.negated_atoms):
					pre_statement+="~"
				pre_statement+=alias+", "
		if(pre_statement[-2]==","):
			pre_statement=pre_statement[:-2]
		return f"with {self.statement}:\n	problem{self.problem}+=Assert(False).when("+pre_statement+")"
	def pay(self, args):
		if(args[0] in self.aggr_alias):
			raise ValueError(f"{args[0]} is not defined")
		attribute=self.value_define(args)
		types=attribute.split("/")
		if(not types[1]=="int"):
			raise ValueError(f"Expected int, received {types[1]}: {types[0]}")
		return types[0]
	def arithmetic_operation(self, args):
		stat=""
		for i in range(len(args)):
			stat+=args[i]
		return stat
	def find_false_keys(self, dictionary, prefisso=''):
		keys_false = []
		for chiave, valore in dictionary.items():
			if isinstance(valore, dict):
				keys_false.extend(self.find_false_keys(valore, prefisso + chiave + '.'))
			elif valore is False:
				keys_false.append(prefisso + chiave)
		return keys_false
	def deny(self, args):
		return self.negated_atoms_check(args)
	def deny_1(self, args):
		if(len(args)==3):
			temp=args[2]
			args[2]=args[1]
			args[1]=temp
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
	def deny_record(self, args):
		return self.assert_record(args)
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
	def show(self, args):
		for i in range(len(args)):
			if(args[i]!="," and args[i]!=";"):
				if not args[i] in records.keys():
					raise ValueError(f"Undefined record: {args[i]}")
				global list_show
				list_show.append(args[i].value)
		return ""
	def asp_block(self, args):
		global asp_block
		asp_block=str(args[0])
		return ""
	def asp(self, args):
		return args[0]
	def operator(self, args):
		if(len(args)>1):
			raise ValueError(f"Operator {"".join(args)} is not supported.")
		return "".join(args)
	def op(self, args):
		if(args[0]=="="):
			args[0]="=="
		return args[0]
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
			if(args[0].type=="RECORD_NAME"):
				attribute=args[0]
			if(args[0].type=="NAME"):
				if(args[0] in self.declared_alias.keys()):
					attribute=self.declared_alias[args[0]]
				else:
					attribute=self.redefined_record[args[0]]
		if(len(args)>=2):	
			for i in range(2, len(args), 2):
				if(args[i-1]=="."):	
					if(attribute=="str" or attribute=="int"):
						raise ValueError(f"{attribute} object has no attribute {args[i]}")		
					found=False
					for t in records[attribute]:
						if(t.value==args[i]):
							attribute=t.type
							found=True
							break
					if not found:
						raise ValueError(f"{attribute} object has no attribute {args[i]}")
				else:
						break
		return attribute
	def attributes_guess_check(self, args):
		attribute=""
		if(args[0] in self.guess_alias):
			attribute=self.guess_alias[args[0]]
		if(args[0] in self.guess_records):
			attribute=args[0]
		if(args[0] in guess_records[self.count_guess]):
			attribute=guess_records[self.count_guess][args[0]]
			if(not args[0] in guess[self.count_guess]):
				self.guess_check.append(args[0])
		if(args[0] in records.keys()):	
			attribute=args[0]
		if(len(args)>=2):
			for i in range(2, len(args), 2):
				if(args[i-1]=="."):	
					if(attribute=="str" or attribute=="int"):
						raise ValueError(f"{attribute} object has no attribute {args[i]}")		
					found=False
					for t in records[attribute]:
						if(t.value==args[i]):
							attribute=t.type
							found=True
							break
					if not found:
						raise ValueError(f"{attribute} object has no attribute {args[i]}")
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

def build_tree(code: str):
	parser_records = Lark(grammar, parser='lalr', transformer=DeclarationTransformer())
	parser_records.parse(code)
	parser_check = Lark(grammar, parser='lalr', transformer=CheckTransformer())
	return parser_check.parse(code)

def check_graph():
	global g
	g.SCC()

def print_program(asp):
	asp+=f"\nprint(problem{number})\n"
	return asp

def execute(solver_path, asp):
	execution_string = asp+f"""
solver = SolverWrapper(solver_path="{solver_path}")
res = solver.solve(problem=problem{number}, timeout=10)
if res.status == Result.HAS_SOLUTION:"""
	if(list_show!=[]):
		execution_string+="""
	num = 0
	for answer in res.answers:
		num += 1
		print("Solution #"+str(num)+": ", end="")"""
		for atom in list_show:
			execution_string+=f"""
		result = answer.get_atom_occurrences({atom}())
		result_str = [str(x) for x in result]
		print(" ".join(result_str))"""
	else:
		execution_string+="""print("SAT")"""
	execution_string+="""
elif res.status == Result.NO_SOLUTION:
	print("UNSAT")
else:
	print("Unknown")
	"""
	return execution_string

def main():
	destination_file = "o.py"
	parser = OptionParser(usage="Usage: %prog [options] [input_files]")
	parser.add_option("-f", "--file", dest="destination_file", help="write output to FILE", metavar="FILE")
	parser.add_option("-v", "--verbose", action="store_true", default=False, dest="verbose", help="print parse tree")
	parser.add_option("-e", "--execute", dest="execute", help="execute the generated code")
	parser.add_option("-r", "--disable-recursive-check", dest="recursive", default=False, help="disable recursive checking", action="store_true")
	parser.add_option("-p", "--print-program", dest="print_program", default=False, help="print ASP program", action="store_true")
	(options, args) = parser.parse_args()
	code = ''.join(fileinput.input(args))
	try:
		global recursive
		if options.recursive:
			recursive = True
		tree = build_tree(code)
		if recursive:
			check_graph()
		asp=""
		if(asp_block!=""):
			asp+=f"""problem{number}.add(\"\"\"{asp_block}\"\"\")"""
		if options.verbose:
			print(tree)
			if(asp!=""):
				print(asp)
		if options.destination_file is not None:
			destination_file = options.destination_file
		f = open(f"{destination_file}", "w")
		f.write(str(tree))
		has_to_close = True
		if options.print_program:
			f.write(print_program(asp))
			if options.execute is None:
				f.close()
				subprocess.run(["python", f"{destination_file}"])
		if options.execute is not None:
			if options.print_program:
				asp=""
			execution_string=execute(str(options.execute), asp)
			f.write(execution_string)
			f.close()
			subprocess.run(["python", f"{destination_file}"])	
		f.close()
	except exceptions.LarkError as e:
		print(f"Parsing error: {e}")
	except Exception as e:
		print(f"Unexpected error: {e}")

if __name__ == '__main__':
	main()