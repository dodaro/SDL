import random
import re
from lark import Token, Transformer

records_global = {}
pyspel_guess_alias = {}
guess_alias = {}
guess = {}
guess_records = set()
list_show = []
asp_block = ""

class PyspelTransformer(Transformer):
    def __init__(self, shared_state):
        self.shared_state = shared_state
        globals()['records_global'] = shared_state.get('records_global', {})
        globals()['pyspel_guess_alias'] = shared_state.get('pyspel_guess_alias', {})
        globals()['guess_alias'] = shared_state.get('guess_alias', {})
        globals()['guess_records'] = shared_state.get('guess_records', {})
        globals()['guess'] = shared_state.get('guess', {})
        
        self.declared_alias = {}
        self.defined_records = set()
        self.attributes = {}
        self.defined_record = set()
        self.redefined_record = {}
        self.new_define_alias = {}
        self.new_guess_alias = {}
        self.guess_alias = {}
        self.guess_records = set()
        self.count_guess = 0
        self.guess_count = self.shared_state.get('pyspel_guess_alias', {0: {"number": 0}})[0]["number"]
        self.count_define = 0
        self.dependencies = {}
        self.guess_check = []
        self.statement = ""
        self.otherwise_en = []
        self.aggregate_records = set()
        self.aggr_guess_record = []
        self.aggr_alias = []
        self.aggr_new_alias = {}
        self.aggregate_with = []
        self.records_attributes = []
        self.negated_atoms = []
        self.negated = {}
        self.define_expressions = []
        self.problem = random.randint(0, 100)
        self.shared_state["number"] = self.problem

    def start(self, args):
        atoms = [atom for atom in args if atom.startswith("@atom")]
        others = [other for other in args if other not in atoms]
        ordered_atoms = []
        ordered = ["from pyspel.pyspel import *\n\n"]
        length = len(ordered)
        
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
            if len(ordered) == length:
                # Questo caso non dovrebbe più accadere grazie al Validator, 
                # ma lo lasciamo come fallback di sicurezza per la stampa
                break 
            else:
                length += 1
                
        ordered.append(f"\nproblem{self.problem} = Problem()\n\n")
        ordered.extend(others)
        return "".join(ordered)

    def record(self, args):
        self.records_attributes = []
        return f"@atom\n{args[0]}\n"

    def record_declaration(self, args):
        self.dependencies[args[0]] = self.records_attributes
        return f"class {args[0]}:\n{args[2]}"

    def declarations(self, args):
        statements = ""
        for i in range(0, len(args)):
            if args[i] == ",":
                statements += "\n"
            else:
                statements += f"{args[i]}"
        return statements

    def declaration(self, args):
        # Niente più controlli sui tipi o dipendenze ricorsive, ci fidiamo del Validator!
        if args[2] in records_global.keys():
            self.records_attributes.append(args[2])
        return f"	{args[0]}: {args[2]}"

    def attr_type(self, args):
        return args[0]
    
    def check_negated_atoms(self, args):
        for neg in self.negated_atoms:
            arg = ""
            if neg in args[0]:
                arg = args[0]
            elif neg in args[-1]:
                arg = args[-1]
            if arg != "":
                pattern = re.compile(r'{}((?:\.[a-zA-Z0-9_]+)+)'.format(re.escape(neg)))
                match = pattern.search(arg)
                if match:
                    terms = match.group(1).split('.')
                    self.access_nested_dict(self.negated[neg], terms[1:])

    def where_stat_check(self, args):
        # Rimossi tutti i TypeError/ValueError (es. "Unexpected boolean condition")
        splitted = args[0].split("/")
        attribute = splitted[1] if len(splitted) > 1 else "any"
        
        # Pulizia argomenti
        args[0] = splitted[0]
        types = args[-1].split("/")
        args[-1] = types[0]
        
        # Controllo negazioni
        if self.negated_atoms:
            self.check_negated_atoms(args)
            
        # Formattazione speciale per predicati ASP se non è str, int o any
        if attribute != "str" and attribute != "int" and attribute != "any":
            return ", Literal(Atom(Predicate(f\"{" + f"{args[0]}" + "}" + f"{args[-2]}" + "{" + f"{args[-1]}" + "}\")), True)"
            
        # Formattazione normale
        statement = ", "
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement

    def where_define_statement(self, args):
        statement = ""
        args = self.where_stat_check(args)
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement

    def guess_where_statement(self, args):
        args = self.guess_where_check_(args)
        if args == "":
            return ""
        stat = ""
        for i in range(len(args)):
            stat += args[i]
        return stat
    
    def define(self, args):
        return self.negated_atoms_check(args)

    def aggr_record(self, args):
        index = 0
        if args[0] == "not":
            index = 1
        if len(args) > index + 1:
            self.aggr_alias.append(args[index + 1])
        else:
            self.aggr_alias.append(args[index])
        return_value = self.define_record(args)
        if len(args) > index + 1:
            self.aggr_new_alias[self.new_define_alias[args[index + 1]]] = args[index + 1]
        else:
            self.aggr_new_alias[self.new_define_alias[args[index]]] = args[index]
        return return_value
    
    def var_expression(self, args):
        # Si appoggia all'espressione matematica sicura vista precedentemente
        return self.exp_aggr_define(args)

    def var_aggr_define(self, args):
        return self.var_define(args)

    def abs_aggr_define(self, args):
        return self.abs_define(args)

    def negated_atoms_check(self, args):
        for neg in self.negated.keys():
            replace_string = ""
            keys = self.find_false_keys(self.negated[neg])
            for i in range(len(keys)):
                splitted = keys[i].split(".")
                if replace_string != "":
                    replace_string += ", "
                replace_string += f"{splitted[0]}="
                count = 0
                fixed = str(neg)
                pattern = re.compile(r'((([A-Z][a-zA-Z0-9_]*))\(\)\s+as\s+{})(?:\s|,|:)'.format(re.escape(fixed)))
                match = pattern.search(args[0])
                term = ""
                toReplace = ""
                if match:
                    term = match.group(2)
                    toReplace = match.group(1)
                for split in splitted:
                    for attr in records_global[term]:
                        if split == attr.value:
                            count += 1
                            replace_string += f"{attr.type}({splitted[count]}="
                replace_string += "hide()"
                for c in range(count):
                    replace_string += ")"
                args[0] = args[0].replace(toReplace, f"{term}({replace_string}) as {neg}")
        self.negated = {}
        return args[0]

    def find_pattern(self, args):
        for i in range(len(args)):
            pattern = r'(([A-Z]+[a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
            match = re.findall(pattern, str(args[i]))
            if match:
                for var in match:
                    if not var[0] in self.statement:
                        self.statement += var[0] + ", "
        if self.statement.endswith(", "):
            self.statement = self.statement[:-2]

    def init_define_variables(self):
        self.redefined_record = {}
        self.defined_record = set()
        self.new_define_alias = {}
        self.declared_alias = {}
        self.defined_records = set()
        self.attributes = {}
        self.aggregate_records = set()
        self.aggregate_with = []
        self.aggr_alias = []
        self.aggr_new_alias = {}
        self.otherwise_en = []
        self.negated_atoms = []
        self.count = 0
        
    def attributes_check(self, args):
        attribute = ""
        if isinstance(args[0], Token):
            if args[0].type == "RECORD_NAME":
                attribute = args[0]
            if args[0].type == "NAME":
                if args[0] in self.declared_alias.keys():
                    attribute = self.declared_alias[args[0]]
                else:
                    attribute = self.redefined_record[args[0]]
        if len(args) >= 2:
            for i in range(2, len(args), 2):
                if args[i - 1] == ".":
                    for t in records_global[attribute]:
                        if t.value == args[i]:
                            attribute = t.type
                            break
                else:
                    break
        return attribute
    
    def var_define(self, args):
        if isinstance(args[0], Token):
            type_value = args[0].type.lower()
            if type_value == "str":
                args[0] = f"'{args[0]}'/str"
            elif type_value == "minus":
                return args[0]+args[1]+f"/int"
            else:
                args[0] += f"/{type_value}"
        return self.print_stat(args)
        
    def define_expression(self, args):
        stat = f""
        operators = ["*", "+", "-", "$"]
        integer = False
        
        for o in operators:
            for i in range(len(args)):
                if o in args[i]:
                    integer = True
                    break
                    
        if integer:
            stat = ""
            term = ""
            for i in range(len(args)):
                # Manteniamo le parentesi per le espressioni matematiche
                if args[i] == "(" or args[i] == ")":
                    stat += args[i]
                    continue
                # Sostituiamo il simbolo di divisione
                if args[i] == "/":
                    args[i] = "$"
                # Estraiamo i tipi e li teniamo da parte
                if "/" in args[i]:
                    types = args[i].split("/")
                    args[i] = types[0]
                    term = "/" + types[1]
                stat += args[i]
            # Attacchiamo il tipo alla fine (es. /int)
            stat += term
        else:
            types = []
            for i in range(len(args)):
                if "/" == args[i]:
                    stat += "$"
                    continue
                if "/" in args[i]:
                    types = args[i].split("/")
                    args[i] = types[0]
                # Per le non-matematiche, eliminiamo le parentesi
                if not (args[i] == "(" or args[i] == ")"):
                    stat += args[i]
            if types:
                stat += "/" + str(types[1])
                
        return stat
    
    def define_from(self, args):
        # Niente più self.add_edge(args)! I cicli li ha già controllati il Validator.
        return ", " + self.print_stat(args)

    def when_define(self, args):
        statement = f"	problem{self.problem}+=When("
        pattern = r'as\s+([a-zA-Z0-9_]+)(?:,|$)'
        match = re.findall(pattern, args)
        if match:
            for var in match:
                if var in self.negated_atoms:
                    statement += "~"
                statement += var + ", "
        return statement[:-2]

    def define_where(self, args):
        statements = ""
        for i in range(len(args)):
            if not args[i] == "and":
                statements += f"{args[i]}"
        for alias in self.new_define_alias.keys():
            return statements + f").define({self.new_define_alias[alias]})\n"

    def define_definition(self, args):
        self.declared_alias = {}
        self.defined_records = set()
        self.attributes = {}
        attr = records_global[args[0]]
        all_attr = []
        for i in range(len(attr)):
            all_attr.append(attr[i])
        self.attributes[args[0]] = all_attr
        if len(args) > 1:
            self.redefined_record[args[1]] = args[0]
            alias = self.add_number(args[1])
            self.new_define_alias[args[1]] = alias
            return f"{args[0]}() as {alias}"
        self.defined_record.add(args[0])
        alias = self.number(args[0])
        self.new_define_alias[args[0].value] = alias
        return f"{args[0]}() as {alias}"

    def as_statement(self, args):
        return f"{args[0]}"

    def build_nested_dictionary(self, alias, args, current_dict=None):
        if current_dict is None:
            current_dict = {}
        for attr in records_global[args[0]]:
            if attr.type in ("int", "str", "any"):
                current_dict[attr.value] = False
            else:
                current_dict[attr.value] = {}
                self.build_nested_dictionary(alias, [attr.type], current_dict[attr.value])
        return current_dict

    def define_record(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
        if len(args) > 1:
            self.declared_alias[args[1]] = args[0]
            var = args[1]
        else:
            self.defined_records.add(args[0])
            var = args[0]
        attr = records_global[args[0]]
        all_attr = []
        for i in range(len(attr)):
            all_attr.append(attr[i])
        self.attributes[var] = all_attr
        if len(args) > 1:
            alias = self.add_number(args[1])
            self.new_define_alias[args[1].value] = alias
            if negated:
                self.negated[alias] = {}
                self.negated[alias] = self.build_nested_dictionary(alias, args)
                self.negated_atoms.append(alias)
            return f"{args[0]}() as {alias}"
        alias = self.number(args[0])
        self.new_define_alias[args[0].value] = alias
        if negated:
            self.negated[alias] = {}
            self.negated[alias] = self.build_nested_dictionary(alias, args)
            self.negated_atoms.append(alias)
        return f"{args[0]}() as {alias}"

    def def_1(self, args):
        when = ""
        if len(args) > 2:
            when = self.when_define(args[1])
        self.statement = ""
        self.find_pattern(args)
        self.init_define_variables()
        if len(args) > 2:
            return f"with {self.statement}:\n{when}{args[2]}"
        stat = f"	problem{self.problem}+=When("
        stat += args[1][2:]
        return f"with {self.statement}:\n{stat}"

    def def_2(self, args):
        when = ""
        if len(args) > 3:
            temp = args[2]
            args[2] = args[3]
            args[3] = temp
            when = self.when_define(args[1])
        self.statement = ""
        for aggr in self.aggregate_with:
            args[0] += ", " + aggr
        self.find_pattern(args)
        
        # Niente add_edge per i cicli
        self.init_define_variables()
        if len(args) > 3:
            return f"with {self.statement}:\n{when}, {args[2]}{args[3]}"
        stat = f"	problem{self.problem}+=When("
        return f"with {self.statement}:\n{stat}{args[2]}{args[1]}"

    def def_3(self, args):
        when = ""
        if len(args) > 3:
            when = self.when_define(args[1])
        self.statement = ""
        for aggr in self.aggregate_with:
            args[0] += ", " + aggr
        self.find_pattern(args)
        
        # Niente add_edge per i cicli
        stat2 = ""
        for alias in self.new_define_alias.keys():
            stat2 = f").define({self.new_define_alias[alias]})\n"
            break
        self.init_define_variables()
        if len(args) > 3:
            return f"with {self.statement}:\n{when}, {args[2]}{stat2}"
        stat = f"	problem{self.problem}+=When("
        return f"with {self.statement}:\n{stat}{args[1]}" + stat2
    
    def guess(self, args):
        return self.negated_atoms_check(args).replace("$", "/")

    def guess_def(self, args, index):
        length = index
        self.statement = ""
        cond = ""
        pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
        if len(args) == length + 1:
            index -= 1
        elif len(args) == length:
            index -= 2
        match = re.findall(pattern, args[0])
        if match:
            for var in match:
                self.statement += var[0] + ", "
        pattern = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)((.*?)/(.*?))\\'
        match = re.findall(pattern, args[index])
        if match:
            for var in match:
                self.statement += var[0] + ", "
                cond += f"{var[2]}:("
                pattern2 = r'(([A-Z][a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
                match2 = re.findall(pattern2, var[3])
                if match2:
                    for var2 in match2:
                        self.statement += var2[0] + ", "
                        if var2[2] in self.negated_atoms:
                            cond += "~"
                        cond += var2[2] + ", "
                    pattern2 = r'/(.*?)$'
                    match2 = re.findall(pattern2, var[3])
                    if match2:
                        for var2 in match2:
                            cond += var2
                else:
                    cond += var[5]
                if cond[-2] == ",":
                    cond = cond[:-2]
                cond += "), "
        cond = cond[:-2]
        if cond.endswith("()"):
            cond = cond[:-3]
        return cond

    def guess_def_check(self, args):
        pattern = r'(([A-Z]+[a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
        match = re.findall(pattern, args[0])
        self.statement = self.statement[:-2]
        self.statement += f":\n	problem{self.problem}+=When("
        if match:
            for var in match:
                if var[2] in self.negated_atoms:
                    self.statement += "~"
                self.statement += var[2] + ", "
            self.statement = self.statement[:-1]
        self.count_guess += 1
        self.guess_count = pyspel_guess_alias[self.count_guess]["number"]
        self.new_guess_alias = {}
        self.guess_alias = {}
        self.guess_check = []
        self.guess_records = set()
        self.aggregate_records = set()
        self.aggregate_with = []
        self.aggr_alias = []
        self.aggr_new_alias = {}
        self.negated_atoms = []

    def guess_def_1(self, args):
        cond = self.guess_def(args, 3)
        self.guess_def_check(args)
        if("exactly" in args[0] or "at least" in args[0] or "at most" in args[0]):
            args[0] = args[0].replace("at least", "at_least")
            args[0] = args[0].replace("at most", "at_most")
            return f"with {self.statement[:-1]}().guess(" + "{" + f"{cond}" + "}" + f", {args[0]}" + ")" + "\n"
        if len(args) == 4:
            if "exactly" in args[1] or "at least" in args[1] or "at most" in args[1]:
                args[1] = args[1].replace("at least", "at_least")
                args[1] = args[1].replace("at most", "at_most")
                return f"with {self.statement[:-1]}).guess(" + "{" + f"{cond}" + "}" + f", {args[1]}" + ")" + "\n"
            else:
                substring = args[1].split(" , ")
                args[1] = " ".join(substring)
                if len(args[1]) > 2:
                    if args[1][0] == ",":
                        args[1] = args[1][2:]
                    if args[1][-2] == ",":
                        args[1] = args[1][:-2]
                    return f"with {self.statement[:-1]}, {args[1]}).guess(" + "{" + f"{cond}" + "})" + "\n"
                return f"with {self.statement[:-1]}).guess(" + "{" + f"{cond}" + "})" + "\n"
        if len(args) == 3:
            return f"with {self.statement[:-1]}).guess(" + "{" + f"{cond}" + "})" + "\n"
        args[2] = args[2].replace("at least", "at_least")
        args[2] = args[2].replace("at most", "at_most")
        substring = args[1].split(" , ")
        args[1] = " ".join(substring)
        if len(args[1]) > 2:
            if args[1][0] == ",":
                args[1] = args[1][2:]
            if args[1][-2] == ",":
                args[1] = args[1][:-2]
        return f"with {self.statement} {args[1]}).guess(" + "{" + f"{cond}" + "}" + f", {args[2]}" + ")" + "\n"

    def guess_def_2(self, args):
        if (len(args) == 5 and not ("exactly" in args[2] or "at least" in args[2] or "at most" in args[2])) or len(args) == 6:
            temp = args[1]
            args[1] = args[2]
            args[2] = temp
        cond = self.guess_def(args, 4)
        pattern = r'(([A-Z]+[a-zA-Z0-9_]*)\(\) as\s+([a-z_][a-zA-Z0-9_]*))(?:\s|,|$)'
        if self.aggregate_with:
            for i in range(len(self.aggregate_with)):
                match = re.findall(pattern, self.aggregate_with[i])
                if match:
                    for var in match:
                        self.statement += var[0] + ", "
        self.guess_def_check(args)
        if len(args) == 5:
            if "exactly" in args[2] or "at least" in args[2] or "at most" in args[2]:
                args[2] = args[2].replace("at least", "at_least")
                args[2] = args[2].replace("at most", "at_most")
                return f"with {self.statement[:-1]}, {args[1]}).guess(" + "{" + f"{cond}" + "}" + f", {args[2]}" + ")" + "\n"
            else:
                substring = args[2].split(" , ")
                args[2] = " ".join(substring)
                if len(args[2]) > 2:
                    if args[2][0] == ",":
                        args[2] = args[2][2:]
                    if args[2][-2] == ",":
                        args[2] = args[2][:-2]
                    return f"with {self.statement[:-1]}, {args[1]}, {args[2]}).guess(" + "{" + f"{cond}" + "})" + "\n"
                return f"with {self.statement[:-1]}, {args[1]}).guess(" + "{" + f"{cond}" + "})" + "\n"
        if len(args) == 4:
            if("exactly" in args[1] or "at least" in args[1] or "at most" in args[1]):
                args[1] = args[1].replace("at least", "at_least")
                args[1] = args[1].replace("at most", "at_most")
                return f"with {self.statement[:-1]}({args[0]}).guess(" + "{" + f"{cond}" + "}" + f", {args[1]}" + ")" + "\n"
            return f"with {self.statement[:-1]}, {args[1]}).guess(" + "{" + f"{cond}" + "})" + "\n"
        args[3] = args[3].replace("at least", "at_least")
        args[3] = args[3].replace("at most", "at_most")
        substring = args[2].split(" , ")
        args[2] = " ".join(substring)
        if len(args[2]) > 2:
            if args[2][0] == ",":
                args[2] = args[2][2:]
            if args[2][-2] == ",":
                args[2] = args[2][:-2]
        return f"with {self.statement} {args[1]}, {args[2]}).guess(" + "{" + f"{cond}" + "}" + f", {args[3]}" + ")" + "\n"

    def guess_definitions(self, args):
        return self.print_stat(args)

    def guess_definition(self, args):
        # Niente più controlli sui record o alias_defined
        alias = ""
        if len(args) > 2:
            self.guess_check = []
            if args[1] in pyspel_guess_alias[self.count_guess].keys():
                alias = pyspel_guess_alias[self.count_guess][args[1]]
            self.guess_alias = {}
            self.guess_records = set()
            return f"{args[0]}() as {alias} {args[2]}"
            
        self.guess_check = []
        self.guess_alias = {}
        self.guess_records = set()
        if args[0] in pyspel_guess_alias[self.count_guess].keys():
            alias = pyspel_guess_alias[self.count_guess][args[0]]
        return f"{args[0]}() as {alias} {args[1]}"

    def guess_declaration(self, args):
        return self.print_stat(args)

    def from_guess(self, args):
        return self.print_stat(args)

    def guess_record(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
            
        if len(args) > 1:
            alias = self.add_number_guess(args[1])
            self.new_guess_alias[args[1]] = alias
            self.guess_alias[args[1]] = args[0]
            if negated:
                self.negated[alias] = {}
                self.negated[alias] = self.build_nested_dictionary(alias, args)
                self.negated_atoms.append(alias)
            return f"{args[0]}() as {alias}"
            
        alias = self.number_guess(args[0])
        self.new_guess_alias[args[0]] = alias
        self.guess_records.add(args[0])
        if negated:
            self.negated[alias] = {}
            self.negated[alias] = self.build_nested_dictionary(alias, args)
            self.negated_atoms.append(alias)
        return f"{args[0]}() as {alias}"

    def guess_times(self, args):
        statements = f""
        for i in range(0, len(args)):
            if args[i] == "and":
                args[i] = ", "
            statements += f"{args[i]}"
        return statements

    def where_guess(self, args):
        statement = ""
        for i in range(len(args)):
            if args[i] == "and":
                args[i] = ", "
            statement += f"{args[i]}"
        self.guess_check = []
        return statement

    def where_guess_statement(self, args):
        statement = ""
        args = self.guess_where_check_(args)
        if args == "":
            return args
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement

    def guess_from(self, args):
        return self.print_stat(args)

    def record_guess(self, args):
        negated = False
        if args[0] == "not":
            negated = True
            args = args[1:]
            
        if len(args) > 1:
            alias = self.add_number_guess(args[1])
            self.guess_alias[args[1]] = args[0]
            self.new_guess_alias[args[1]] = alias
            pyspel_guess_alias[self.count_guess][args[1]] = alias
            if negated:
                self.negated[alias] = {}
                self.negated[alias] = self.build_nested_dictionary(alias, args)
                self.negated_atoms.append(alias)
            return f"{args[0]}() as {alias}"
            
        alias = self.number_guess(args[0])
        self.guess_records.add(args[0])
        self.new_guess_alias[args[0]] = alias
        if negated:
            self.negated[alias] = {}
            self.negated[alias] = self.build_nested_dictionary(alias, args)
            self.negated_atoms.append(alias)
        return f"{args[0]}() as {alias}"

    def remove_and(self, args):
        statements = ""
        for i in range(len(args)):
            if args[i] == "and":
                if args[i + 1] == "" or args[i - 1] == "":
                    args[i] = ""
                else:
                    if args[i + 1].startswith(","):
                        args[i + 1] = args[i + 1][1:]
                    args[i] = ","
            if args[i] != "":
                statements += args[i]
        return statements

    def guess_where(self, args):
        statements = self.remove_and(args)
        return "/" + statements + "\\"

    def guess_where_check_(self, args):
        splitted = str(args[0]).split("/")
        attribute = splitted[1] if len(splitted) > 1 else "any"
        args[0] = splitted[0]

        types = str(args[-1]).split("/")

        # Ripristino alias corretti
        if args[0] in self.new_guess_alias.keys():
            args[0] = self.new_guess_alias[args[0]]
        elif self.count_guess in guess_alias and args[0] in pyspel_guess_alias[self.count_guess].keys():
            args[0] = pyspel_guess_alias[self.count_guess][args[0]]

        if self.negated_atoms:
            self.check_negated_atoms(args)

        # Formattazione Pyspel per record vs record
        if attribute != "str" and attribute != "int" and attribute != "any":
            return "Literal(Atom(Predicate(f\"{" + f"{args[0]}" + "}" + f"{args[-2]}" + "{" + f"{types[0]}" + "}\")), True)"

        args[-1] = types[0]
        return args

    def value_guess_check(self, args):
        statement = ""
        attribute = self.attributes_guess_check(args)
        if args[0] in self.new_guess_alias.keys():
            args[0] = self.new_guess_alias[args[0]]
        elif args[0] in pyspel_guess_alias[self.count_guess].keys():
            args[0] = pyspel_guess_alias[self.count_guess][args[0]]
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement + "/" + attribute

    def attributes_guess_check(self, args):
        attribute = ""
        if args[0] in self.guess_alias:
            attribute = self.guess_alias[args[0]]
        if args[0] in self.guess_records:
            attribute = args[0]
        if args[0] in guess_records[self.count_guess]:
            attribute = guess_records[self.count_guess][args[0]]
            if not args[0] in guess[self.count_guess]:
                self.guess_check.append(args[0])
        if args[0] in records_global.keys():
            attribute = args[0]
        if len(args) >= 2:
            for i in range(2, len(args), 2):
                if args[i - 1] == ".":
                    # Navigazione sicura
                    for t in records_global.get(attribute, []):
                        if t.value == args[i]:
                            attribute = t.type
                            break
                else:
                    break
        return attribute

    def number(self, args):
        letter = args[0].lower()
        letter += "_" + f"{self.count_define}"
        self.count_define += 1
        return letter

    def add_number(self, args):
        args = args + "_" + f"{self.count_define}"
        self.count_define += 1
        return args

    def number_guess(self, args):
        letter = args[0].lower()
        letter += "_" + f"{self.guess_count}"
        self.guess_count += 1
        return letter

    def add_number_guess(self, args):
        args = args + "_" + f"{self.guess_count}"
        self.guess_count += 1
        return args

    def operator(self, args):
        # Rimosso il controllo che bloccava gli operatori multipli
        return "".join(args)

    def op(self, args):
        # Manteniamo la correzione di "=" in "==" che serve a Pyspel
        if args[0] == "=":
            args[0] = "=="
        return args[0]

    def times(self, args):
        # Manteniamo l'aggiunta di "=" per i keyword arguments di Pyspel (es. exactly=1)
        return args[0] + "="

    def print_stat(self, args):
        # Pura formattazione della stringa (spazi dopo la virgola)
        statements = f"{args[0]}"
        for i in range(1, len(args)):
            if args[i] == ",":
                statements += f"{args[i]}"
            else:
                statements += f" {args[i]}"
        return statements
    
    def guess_aggregate(self, args):
        return self.aggregate(args)

    def aggregate(self, args):
        stat = ""
        for i in range(len(args)):
            if args[i] == "and":
                args[i] = ", "
            stat += f"{args[i]}"
        return stat

    def aggr_where_guess(self, args):
        return self.remove_and(args)

    def aggr_where(self, args):
        return self.remove_and(args)

    def where_aggr_guess(self, args):
        statement = ", "
        args = self.guess_where_check_(args)
        if args == "":
            return args
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement

    def where_aggr_statement(self, args):
        return self.where_stat_check(args)

    def check_sum(self, all_en, declared_alias):
        sum_bool = "False/" + f"{all_en}"
        if "." in all_en:
            en = all_en.split(".")[0]
            if en in declared_alias.keys():
                attribute = declared_alias[en]
            else:
                attribute = en
            temp_array = all_en.split(".")[1:]
            for i in range(len(temp_array)):
                for t in records_global.get(attribute, []):
                    if t.value == temp_array[i]:
                        attribute = t.type
                        break
            if attribute == "int":
                sum_bool = "True/"
        return sum_bool

    def aggregate_body(self, args, new_alias, declared_alias):
        self.aggregate_records = set()
        var = re.findall(r'\b(?:\w+(?:\.\w+)*|\S+)\b', args[0][0][0])
        sum_bool = "True/"
        for v in var:
            num = self.isNum(v)
            if not num:
                sum_bool = self.check_sum(v, declared_alias)
                
        stat = "("
        for attr in args[0][0]:
            if attr != ",":
                var = re.findall(r'[\w.]+|\S', attr)
                for v in var:
                    if "." in v:
                        temp = v
                        splitted = temp.split(".")
                        alias = splitted[0]
                        v = f"{new_alias.get(alias, alias)}.{'.'.join(splitted[1:])}"
                    elif v in new_alias.keys():
                        v = new_alias[v]
                    stat += v
            else:
                stat += ", "
        if len(args[0]) <= 1:
            stat += "):()"
        else:
            stat += "):"
            stat_alias = ""
            if len(args[0]) > 2 or " as " in args[0][1]:
                comma = args[0][1].split(",")
                if not comma:
                    alias = args[0][1].split("as ")[1]
                    if alias in self.negated_atoms:
                        stat_alias += "~"
                    stat_alias += alias
                else:
                    for commas in comma:
                        alias = commas.split("as ")[1]
                        if stat_alias != "":
                            stat_alias += ", "
                        if alias in self.negated_atoms:
                            stat_alias += "~"
                        stat_alias += alias
            stat += "(" + stat_alias
            if len(args[0]) > 2:
                stat += f"{args[0][2]}"
            elif not " as " in args[0][1]:
                stat += f"{args[0][1][2:]}"
            stat += ")"
        return stat + "/" + sum_bool

    def aggr_body_guess(self, args):
        self.aggr_guess_record = []
        return self.aggregate_body(args, self.new_guess_alias, self.guess_alias)

    def aggr_body(self, args):
        return self.aggregate_body(args, self.new_define_alias, self.declared_alias)

    def aggr_body_guess1(self, args):
        if len(args) > 2:
            length = len(self.aggregate_with)
            self.aggregate_with += args[1].split(",")
            if length == len(self.aggregate_with):
                self.aggregate_with += args[1]
        return args

    def aggr_body_1(self, args):
        if len(args) > 2:
            length = len(self.aggregate_with)
            self.aggregate_with += args[1].split(",")
            if length == len(self.aggregate_with):
                self.aggregate_with += args[1]
        return args

    def aggr_body_guess2(self, args):
        if len(args) > 1:
            length = len(self.aggregate_with)
            self.aggregate_with += args[1].split(",")
            if length == len(self.aggregate_with):
                self.aggregate_with += args[1]
        return args

    def aggr_body_2(self, args):
        if len(args) > 1:
            length = len(self.aggregate_with)
            self.aggregate_with += args[1].split(",")
            if length == len(self.aggregate_with):
                self.aggregate_with += args[1]
        return args

    def aggr_records_guess(self, args):
        return args

    def aggr_records(self, args):
        return args

    def aggr_def_guess(self, args):
        return self.aggr_def(args)

    def aggr_def(self, args):
        stat = ""
        stop = False
        for i in range(1, len(args) - 2):
            if args[i] == "==":
                stop = True
            if not stop and args[i] != ";":
                bool_sum = args[i].split("/")
                if not ":" in bool_sum[0]:
                    bool_sum[1] = bool_sum[0] + "/" + bool_sum[1]
                    bool_sum = bool_sum[1:]
                args[i] = bool_sum[0]
            if args[i] == ";":
                args[i] = ", "
            stat += args[i]
        stat += "})" + f"{args[-2]}{args[-1]}"
        
        if args[0] == "count":
            function = "Count"
        elif args[0] == "min":
            function = "Min"
        elif args[0] == "max":
            function = "Max"
        else:
            function = "Sum"
        return function + "({" + f"{stat.replace('$', '/')}"
        
    def aggregate_expression(self, args):
        return self.print_stat(args)

    def aggregate_record(self, args):
        stat = "".join(args)
        self.aggregate_records.add(stat)
        return stat
    
    def aggr_record_guess(self, args):
        index = 0
        if args[0] == "not":
            index = 1
            
        # Rimosso il controllo del grafo (g.add_edge) e le eccezioni alias_defined/record_defined
        if len(args) > index + 1:
            self.aggr_guess_record.append(args[index + 1])
            self.aggr_alias.append(args[index + 1])
        else:
            self.aggr_guess_record.append(args[index])
            self.aggr_alias.append(args[index])
            
        return_value = self.guess_record(args)
        
        # Manteniamo l'aggiornamento degli alias per la formattazione successiva
        if len(args) > index + 1:
            self.aggr_new_alias[self.new_guess_alias[args[index + 1]]] = args[index + 1]
        else:
            self.aggr_new_alias[self.new_guess_alias[args[index]]] = args[index]
            
        return return_value

    def aggregate_from(self, args):
        # Rimossa la chiamata a self.aggregate_check(...)
        return self.print_stat(args)

    def aggregate_from_guess(self, args):
        # Rimossa la chiamata a self.aggregate_check(...)
        return self.print_stat(args)

    def aggregate_term(self, args):
        splitted = args[0].split("/")
        if args[0] == "-" or args[0] == "+":
            return args[0] + args[1]
        if len(splitted) > 1:
            return splitted[0]
        if hasattr(args[0], 'type') and args[0].type == "INT":
            return args[0]
            
        return self.pay(args)

    def aggregate_term_guess(self, args):
        if hasattr(args[0], 'type') and args[0].type == "INT":
            return args[0]
            
        # Rimosso check undefined_element e controllo "Expected int"
        attribute = self.value_guess(args)
        types = attribute.split("/")
        return types[0]
    
    def assert_statement(self, args):
        return args[0]

    def aggregate_term_exp(self, args):
        return self.exp_aggr_define(args)

    def aggregate_term_guess_exp(self, args):
        return self.exp_aggr_define(args)

    def abs_term_guess(self, args):
    	return self.abs_guess(args).split("/")[0]
        
    def aggregate_terms(self, args):
        if len(args) > 1:
            return self.range_times(args)
        return args[0]

    def aggregate_terms_guess(self, args):
        return self.aggregate_terms(args)

    def abs_aggregate_term(self, args):
        return self.abs_guess(args).split("/")[0]

    def assert_1(self, args):
        self.statement = ""
        self.find_pattern(args)
        self.init_define_variables()
        if len(args) > 2:
            return f"with {self.statement}:\n	problem{self.problem}+={args[2]}"
        return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"

    def assert_2(self, args):
        if len(args) == 4:
            temp = args[2]
            args[2] = args[3]
            args[3] = temp
        else:
            temp = args[1]
            args[1] = args[2]
            args[2] = temp
        self.assert_deny_with(args)
        self.init_define_variables()
        if len(args) > 3:
            end_assert = args[3][:-1]
            end_assert += ", " + args[2] + ")"
            return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
        end_assert = args[2][:-1]
        end_assert += ", " + args[1] + ")"
        return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"

    def assert_stat(self):
        var = []
        for alias in self.redefined_record.keys():
            var.append(self.new_define_alias[alias])
        for record in self.defined_record:
            var.append(self.new_define_alias[record])
        return var

    def assert_3(self, args):
        self.assert_deny_with(args)
        end_assert = ""
        var = self.assert_stat()
        var_statement = f"{var[0]}"
        for i in range(1, len(var)):
            var_statement += f", {var[i]}"
        if len(args) > 2:
            pre_statement = ""
            for alias in self.new_define_alias.values():
                if not alias in var and not alias in self.aggr_new_alias:
                    if alias in self.negated_atoms:
                        pre_statement += "~"
                    pre_statement += alias + ", "
            self.init_define_variables()
            if pre_statement != "":
                pre_statement = pre_statement[:-2]
                end_assert = "Assert(" + var_statement + ").when(" + pre_statement + ", " + args[2] + ")"
            return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
        self.init_define_variables()
        end_assert = "Assert(" + var_statement + ").when(" + args[1] + ")"
        return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"

    def assert_(self, args):
        return self.negated_atoms_check(args) + "\n"

    def assert_deny_with(self, args):
        self.statement = ""
        for aggr in self.aggregate_with:
            args[0] += ", " + aggr
        self.find_pattern(args)

    def assert_definition(self, args):
        return self.print_stat(args)

    def assert_records(self, args):
        if len(args) > 1:
            self.redefined_record[args[1]] = args[0]
            self.otherwise_en.append(args[1])
        else:
            self.otherwise_en.append(args[0])
        return self.define_definition(args)

    def assert_from(self, args):
        return self.print_stat(args)

    def assert_record(self, args):
        index = 0
        if args[0] == "not":
            index = 1
        if len(args) > index + 1:
            self.otherwise_en.append(args[index + 1])
        else:
            self.otherwise_en.append(args[index])
        return self.define_record(args)

    def where_assert(self, args):
        statement = ""
        for i in range(len(args)):
            if args[i] == "and":
                args[i] = ""
            if args[i] != "":
                statement += args[i]
        var = self.assert_stat()
        var_statement = f"{var[0]}"
        for i in range(1, len(var)):
            var_statement += f", {var[i]}"
        pre_statement = ""
        for alias in self.new_define_alias.values():
            if not alias in var and not alias in self.aggr_new_alias:
                if alias in self.negated_atoms:
                    pre_statement += "~"
                pre_statement += alias + ", "
        if len(statement) > 1:
            if statement[-2] == ",":
                statement = statement[:-2]
            return "Assert(" + var_statement + ").when(" + pre_statement + statement[2:] + ")"
        if pre_statement != "":
            pre_statement = pre_statement[:-2]
        return "Assert(" + var_statement + ").when(" + pre_statement + ")"

    def where_assert_statement(self, args):
        return self.where_define_statement(args)

    def try_assert(self, args):
        other = ""
        for en in self.otherwise_en:
            other += f"{self.new_define_alias[en]},"
        other = other[:-1]
        self.init_define_variables()
        return args[0] + ".otherwise(" + args[1] + other + ")\n"

    def assert_otherwise(self, args):
        return args[0]

    def assert_otherwise_1(self, args):
        self.statement = ""
        self.find_pattern(args)
        if len(args) > 2:
            return f"with {self.statement}:\n	problem{self.problem}+={args[2]}"
        return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"

    def assert_otherwise_2(self, args):
        index = 0
        if len(args) == 4:
            index = 1
        temp = args[1 + index]
        args[1 + index] = args[2 + index]
        args[2 + index] = temp
        self.assert_deny_with(args)
        if len(args) > 3:
            end_assert = args[3][:-1]
            end_assert += ", " + args[2] + ")"
            return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
        end_assert = args[2][:-1]
        end_assert += ", " + args[1] + ")"
        return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"

    def assert_otherwise_3(self, args):
        self.assert_deny_with(args)
        end_assert = ""
        var = self.assert_stat()
        var_statement = f"{var[0]}"
        for i in range(1, len(var)):
            var_statement += f", {var[i]}"
        if len(args) > 2:
            pre_statement = ""
            for alias in self.new_define_alias.values():
                if not alias in var and not alias in self.aggr_new_alias:
                    if alias in self.negated_atoms:
                        pre_statement += "~"
                    pre_statement += alias + ", "
            if pre_statement != "":
                pre_statement = pre_statement[:-2]
                end_assert = "Assert(" + var_statement + ").when(" + pre_statement + ", " + args[2] + ")"
            return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
        end_assert = "Assert(" + var_statement + ").when(" + args[1] + ")"
        return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"

    def assert_otherwise_4(self, args):
        self.assert_deny_with(args)
        var = self.assert_stat()
        var_statement = f"{var[0]}"
        for i in range(1, len(var)):
            var_statement += f", {var[i]}"
        end_assert = "Assert(" + var_statement + ")"
        return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"

    def pay_statement(self, args):
        return args[0] + "," + args[1] + ","

    def try_deny(self, args):
        return self.try_assert(args)

    def deny_otherwise(self, args):
        return args[0]

    def deny_otherwise_1(self, args):
        if len(args) == 3:
            temp = args[2]
            args[2] = args[1]
            args[1] = temp
        self.assert_deny_with(args)
        if len(args) >= 3:
            end_assert = args[2][:-1]
            end_assert += ", " + args[1] + ")"
            return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
        return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"

    def deny_otherwise_2(self, args):
        self.assert_deny_with(args)
        pre_statement = ""
        for alias in self.new_define_alias.values():
            if not alias in self.aggr_new_alias:
                if alias in self.negated_atoms:
                    pre_statement += "~"
                pre_statement += alias + ", "
        return f"with {self.statement}:\n	problem{self.problem}+=Assert(False).when(" + pre_statement + f"{args[1]})"

    def deny_otherwise_3(self, args):
        self.assert_deny_with(args)
        pre_statement = ""
        for alias in self.new_define_alias.values():
            if not alias in self.aggr_new_alias:
                if alias in self.negated_atoms:
                    pre_statement += "~"
                pre_statement += alias + ", "
        if pre_statement[-2] == ",":
            pre_statement = pre_statement[:-2]
        return f"with {self.statement}:\n	problem{self.problem}+=Assert(False).when(" + pre_statement + ")"

    def pay(self, args):
        attribute = self.value_define(args)
        types = attribute.split("/")
        return types[0]

    def arithmetic_operation(self, args):
        stat = ""
        for i in range(len(args)):
            stat += args[i]
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
        if len(args) == 3:
            temp = args[2]
            args[2] = args[1]
            args[1] = temp
        self.assert_deny_with(args)
        self.init_define_variables()
        if len(args) >= 3:
            end_assert = args[2][:-1]
            end_assert += ", " + args[1] + ")"
            return f"with {self.statement}:\n	problem{self.problem}+={end_assert}"
        return f"with {self.statement}:\n	problem{self.problem}+={args[1]}"

    def deny_2(self, args):
        self.assert_deny_with(args)
        pre_statement = ""
        for alias in self.new_define_alias.values():
            if not alias in self.aggr_new_alias:
                if alias in self.negated_atoms:
                    pre_statement += "~"
                pre_statement += alias + ", "
        self.init_define_variables()
        return f"with {self.statement}:\n	problem{self.problem}+=Assert(False).when(" + pre_statement + f"{args[1]})"

    def deny_from(self, args):
        return self.assert_from(args)

    def deny_record(self, args):
        return self.assert_record(args)

    def where_deny(self, args):
        statement = ""
        for i in range(len(args)):
            if args[i] == "and":
                args[i] = ""
            if args[i] != "":
                statement += args[i]
        pre_statement = ""
        for alias in self.new_define_alias.values():
            if not alias in self.aggr_new_alias:
                if alias in self.negated_atoms:
                    pre_statement += "~"
                pre_statement += alias + ", "
        if len(statement) > 1:
            if statement[-2] == ",":
                statement = statement[:-2]
            return "Assert(False).when(" + pre_statement + statement[2:] + ")"
        if pre_statement != "":
            pre_statement = pre_statement[:-2]
        return "Assert(False).when(" + pre_statement + ")"

    def where_deny_statement(self, args):
        return self.where_define_statement(args)

    def deny_(self, args):
        return self.negated_atoms_check(args) + "\n"
    
    def verify_int(self, arg):
        # Rimosso il raise ValueError("Expected int..."). Estrae solo il valore pulito.
        splitted = str(arg).split("/")
        return splitted[0]

    def isNum(self, args):
        try:
            int(args)
            return True
        except ValueError:
            return False

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


    def range_define(self, args):
        if args[0] == "-" or args[0] == "+":
            args[1] = self.verify_int(args[1])
            if args[3] == "-" or args[3] == "+":
                args[4] = self.verify_int(args[4])
                return f"domain({args[0]}{args[1]}, {args[3]}{args[4]})/int"
            else:
                return f"domain({args[0]}{args[1]}, {args[3]})/int"
        elif args[2] == "-" or args[2] == "+":
            args[3] = self.verify_int(args[3])
            return f"domain({args[0]}, {args[2]}{args[3]})/int"
        
        args[0] = self.verify_int(args[0])
        args[2] = self.verify_int(args[2])
        return f"domain({args[0]}, {args[2]})/int"

    def range2(self, args):
        return self.range_define(args).split("/")[0]

    def range_var(self, args):
        return self.range_define(args)

    def range_aggr_guess(self, args):
        return self.range_define(args)

    def range_aggr_define(self, args):
        return self.range_define(args)

    def range_guess(self, args):
        return self.range_define(args)

    def range_guess_2(self, args):
        return self.range_define(args)

    def range_times(self, args):
        return self.range_define(args).split("/")[0]
    
    def abs_define(self, args):
        arg = self.verify_int(args[1])
        return "abs_v(" + arg + ")/int"

    def abs2(self, args):
        arg = self.verify_int(args[1])
        return "abs_v(" + arg + ")"

    def abs_guess(self, args):
        arg = ""
        if len(args) > 3:
            arg = self.verify_int(args[2])
        else:
            arg = self.verify_int(args[1])
            
        if len(args) > 3:
            return "abs_v(-" + arg + ")/int"
        return "abs_v(" + arg + ")/int"

    def abs_var(self, args):
        return self.abs_guess(args)

    def abs_guess_2(self, args):
        return self.abs_guess(args)

    def abs_aggr_guess(self, args):
        return self.abs_guess(args)

    def abs_times(self, args):
        return self.abs_guess(args).split("/")[0]
    
    def var(self, args):
        return self.var_define(args)

    def var_guess(self, args):
        return self.var_define(args)

    def var_guess_2(self, args):
        return self.var_define(args)

    def var_aggr_guess(self, args):
        return self.var_define(args)

    def value_def(self, args):
        statement = ""
        attribute = self.attributes_check(args)
        if args[0] in self.new_define_alias:
            args[0] = self.new_define_alias[args[0]]
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement + "/" + attribute

    def value(self, args):
        # Rimosso il raise ValueError(undefined_element)
        return self.value_def(args)

    def value_define(self, args):
        return self.value_def(args)

    def value_aggr_define(self, args):
        return self.value_def(args)

    def value_guess(self, args):
        # Rimosso il raise ValueError
        return self.value_guess_check(args)

    def value_guess_2(self, args):
        return self.value_guess_check(args)

    def value_aggr_guess(self, args):
        return self.value_guess_check(args)
    def exp_aggr_define(self, args):
        stat = ""
        operators = ["*", "+", "-", "$"]
        integer = False
        
        # 1. Capisce se è un'operazione matematica
        for o in operators:
            for i in range(len(args)):
                if o in str(args[i]):
                    integer = True
                    break
                    
        # 2. Formattazione se c'è matematica
        if integer:
            stat = ""
            term = ""
            for i in range(len(args)):
                # Mantiene le parentesi
                if args[i] == ")" or args[i] == "(":
                    stat += args[i]
                    continue
                # Protegge la divisione trasformandola in $
                if args[i] == "/":
                    args[i] = "$"
                # Estrae il tipo per metterlo alla fine
                if "/" in str(args[i]):
                    types = str(args[i]).split("/")
                    # Eliminato il controllo: if types[1] != "int" and types[1] != "any": raise ValueError...
                    args[i] = types[0]
                    term = "/" + types[1]
                stat += str(args[i])
            stat += term
            
        # 3. Formattazione se NON c'è matematica
        else:
            types = []
            for i in range(len(args)):
                if "/" == str(args[i]):
                    stat += "$"
                    continue
                if "/" in str(args[i]):
                    types = str(args[i]).split("/")
                    args[i] = types[0]
                # Nelle espressioni non matematiche, rimuove le parentesi
                if not (args[i] == "(" or args[i] == ")"):
                    stat += str(args[i])
            if types:
                stat += "/" + str(types[1])
                
        return stat
    
    def var_guess_exp(self, args):
        return self.exp_aggr_define(args)

    def var_guess_exp_2(self, args):
        return self.exp_aggr_define(args)

    def aggr_guess_exp(self, args):
        return self.exp_aggr_define(args)

    def times_exp(self, args):
        stat = ""
        for i in range(len(args)):
            if args[i] == ")" or args[i] == "(":
                stat += args[i]
                continue
            if args[i] == "/":
                args[i] = "$"
            stat += args[i]
        return stat

    def times_value(self, args):
        statement = ""
        # Rimosso il check undefined_record e "Expected int"
        attribute = self.attributes_guess_check(args)
        if args[0] in self.new_guess_alias:
            args[0] = self.new_guess_alias[args[0]]
        elif self.count_guess in guess_alias and args[0] in pyspel_guess_alias[self.count_guess]:
            args[0] = pyspel_guess_alias[self.count_guess][args[0]]
            
        for i in range(len(args)):
            statement += f"{args[i]}"
        return statement
    
    def show(self, args):
        return ""

    def asp_block(self, args):
        self.shared_state["asp_block"] = str(args[0])
        return ""

    def asp(self, args):
        return args[0]