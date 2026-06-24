from pyspel.pyspel import *

@atom
class Cab:
	id: int
	driver: str

problem30 = Problem()

with Cab() as c_0:
	problem30+=When(c_0.id==1, c_0.driver=='"Alice"').define(c_0)
with Cab() as c_1:
	problem30+=When(c_1.id==2, c_1.driver=='"Bob"').define(c_1)

solver = SolverWrapper(solver_path="C:/Users/Hp/miniconda3/envs/potassco/Library/bin/clingo.exe")
res = solver.solve(problem=problem30, timeout=100)
if res.status == Result.HAS_SOLUTION:
    num = 0
    for answer in res.answers:
        num += 1
        print("Solution #"+str(num)+": ", end="")
        result = answer.get_atom_occurrences(Cab())
        result_str = [str(x) for x in result]
        print(" ".join(result_str))
elif res.status == Result.NO_SOLUTION:
    print("UNSAT")
else:
    print("Unknown")
    