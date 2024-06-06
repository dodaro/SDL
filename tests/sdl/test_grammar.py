import random
import re
from unittest import mock
from unittest.mock import patch

import pytest

from grammar import build_tree


def assert_in_transformation(code: str, content: str):
    def normalize(string):
        res = string.strip().replace("\t", "    ")
        res = re.sub(r"problem(\d+)\+=", "problem+=", res)
        return res
    tree = normalize(str(build_tree(code)))
    assert normalize(content) in tree


def test_build_tree_entity():
    assert_in_transformation("@entity Temperature: value: any;", """
@atom
class Temperature:
    value: any
    """)

def test_build_tree_define():
	assert_in_transformation("""
@entity Color: value: any;
@entity Node: value: int;
@entity Edge: node1: Node, node2: Node;

define Node as n
    from Edge, Edge as e2
	where Edge.node1=n and e2.node1=n;""", 
"""with Node() as n_0, Edge(node1 = n_0) as e_1, Edge(node1 = n_0) as e2_2:
	problem+=When(e_1, e2_2).define(n_0)""")

def test_build_tree_define_2():
	assert_in_transformation("""
@entity Person: name: str, age: int;
@entity Car: brand: str, model: str;
@entity Ownership: owner: Person, car: Car;

define Person as pc
    from Car, Ownership
    	where Ownership.owner = pc and Car.brand="Nissan";""", 
"""with Person() as pc_0, Car() as c_1, Ownership(owner = pc_0) as o_2:
	problem+=When(o_2, c_1, c_1.brand=="Nissan").define(pc_0)""")

def test_build_tree_define_aggregate():
	assert_in_transformation("""
@entity Person: name: str, age: int;
@entity Car: brand: str, model: str;
@entity Ownership: owner: Person, car: Car;

define Person as pc
    from Car
	sum of {1, o from Ownership as o where o.car=Car} > 2;""", 
"""with Person() as pc_0, Car() as c_1, Ownership(car = c_1) as o_2:
	problem+=When(c_1, Sum({(1, o_2):(o_2)})>2).define(pc_0)""")

def test_build_tree_define_not():
	assert_in_transformation("""
@entity Person: name: str, age: int;
@entity Car: brand: str, model: str;
@entity Ownership: owner: Person, car: Car;

define Person as pc
	from not Car as c
	count of {o.owner from Ownership as o} > 2
		where c.brand="Toyota";""", 
"""with Person() as pc_0, Ownership() as o_2, Car() as c_1:
	problem+=When(~c_1, Count({(o_2.owner):(o_2)})>2, c_1.brand=="Toyota").define(pc_0)""")


def test_build_tree_guess():
    assert_in_transformation("""
@entity Digit: value: int;
@entity Cell: row: int, col: int;
@entity BlockType: value: str;
@entity Block: type: BlockType, index: int;
@entity BlockCell: block: Block, cell: Cell;
@entity Assign: cell: Cell, digit: Digit;
guess from Cell
    exactly 1
        Assign
            from Digit
                where Assign.cell = Cell and Assign.digit = Digit
;    
    """, """
with Cell() as c_1, Digit() as d_2, Assign(cell = c_1, digit = d_2) as a_0:
    problem+=When(c_1).guess({a_0:(d_2)}, exactly=1)
    """)
def test_build_tree_guess_1():
    assert_in_transformation("""@entity In_clause: clause: int, literal: int;
@entity Clause: id: int;
@entity Assignment: variable: Vars;
@entity WeightedClause: clause: int, literal: int;
@entity Vars: id: int;

guess from Vars as v
	Assignment
		where Assignment.variable=v;""",
"""with Vars() as v_1, Assignment(variable = v_1) as a_0:
	problem+=When(v_1).guess({a_0})""")

def test_build_tree_guess_2():
	assert_in_transformation("""
@entity Resolution: value: int;
@entity Video: type: str;
@entity F: video: Video, resolution: Resolution, bit_rate: Bit_rate, sat_value: Sat;
@entity Bit_rate: value: int;
@entity Sat: value: int;
@entity User: id: int, video: Video, resolution: Resolution, max_sat: Sat, max_bit: Bit_rate;
@entity Assign_: user:User, bit_rate: Bit_rate, sat_value: Sat;

guess from User as user, Bit_rate as b, Video as v
	where user.max_bit=b and user.max_bit.value=2
		Assign_ as a
			from F as f
				where f.bit_rate.value<=user.max_bit.value and f.video=user.video and f.resolution=user.resolution and a.user=user and a.bit_rate=f.bit_rate and a.sat_value=f.sat_value;""", 
"""with Bit_rate() as b_2, Video() as v_3, User(max_bit = b_2) as user_1, F(video = user_1.video, resolution = user_1.resolution) as f_4, Assign_(user = user_1, bit_rate = f_4.bit_rate, sat_value = f_4.sat_value) as a_0:
	problem+=When(user_1, b_2, v_3, user_1.max_bit.value==2).guess({a_0:(f_4, f_4.bit_rate.value<=user_1.max_bit.value)})""")
	

def test_build_tree_guess_aggregate():
	assert_in_transformation("""
@entity Resolution: value: int;
@entity Video: type: str;
@entity F: video: Video, resolution: Resolution, bit_rate: Bit_rate, sat_value: Sat;
@entity Bit_rate: value: int;
@entity Sat: value: int;
@entity User: id: int, video: Video, resolution: Resolution, max_sat: Sat, max_bit: Bit_rate;
@entity Assign_: user:User, bit_rate: Bit_rate, sat_value: Sat;
guess from F, Resolution as r
	sum of {r2.value from Resolution as r2 where r2.value>r.value; 2} == 2
	where F.resolution.value=1 and F.resolution=r and r.value<=4
		at_most 1 and at_least F.resolution.value
			Bit_rate as b2
				where b2.value=F.resolution.value
			Sat
				from Assign_ as a3
					where a3.sat_value=Sat and a3.sat_value.value=2;""",
"""with Resolution() as r_3, Bit_rate() as b2_0, Sat() as s_1, Assign_(sat_value = s_1) as a3_5, Resolution() as r2_4, F(resolution = r_3) as f_2:
	problem+=When(f_2, r_3, Sum({(r2_4.value):(r2_4, r2_4.value>r_3.value), (2):()})==2, f_2.resolution.value==1, r_3.value<=4).guess({b2_0:(b2_0.value==f_2.resolution.value), s_1:(a3_5, a3_5.sat_value.value==2)}, at_most=1, at_least=f_2.resolution.value)""")

def test_build_tree_guess_not():
	assert_in_transformation("""
@entity Resolution: value: int;
@entity Video: type: str;
@entity F: video: Video, resolution: Resolution, bit_rate: Bit_rate, sat_value: Sat;
@entity Bit_rate: value: int;
@entity Sat: value: int;
@entity User: id: int, video: Video, resolution: Resolution, max_sat: Sat, max_bit: Bit_rate;
@entity Assign_: user:User, bit_rate: Bit_rate, sat_value: Sat;
guess from not Assign_ as a, User
	count of {a2.user from not Assign_ as a2 where a2.user=User} == 2
	where User.id>a.user.id
		F
			from not Resolution as r
				where F.resolution=r;""",
"""with Assign_() as a_1, User() as u_2, Resolution() as r_4, Assign_(user = u_2) as a2_3, F(resolution = r_4) as f_0:
	problem+=When(~a_1, u_2, Count({(a2_3.user):(~a2_3)})==2, u_2.id>a_1.user.id).guess({f_0:(~r_4)})""")
	

def test_build_tree_assert_otherwise():
	assert_in_transformation("""
@entity Book: title: str, author: str, genre: str, publication_year: int;
@entity Reader: name: str, age: int, favorite_genre: str;
@entity Review: book: Book, reader: Reader, rating: int, comment: str;
deny unless Book as b or Reader as r
	from Review as review
		where b.genre="Horror" and r.age=19
			or pay review.rating at 5;""",
"""with Book() as b_0, Reader() as r_1, Review() as review_2:
	problem+=Assert(b_0, r_1).when(review_2, b_0.genre=="Horror", r_1.age==19).otherwise(review_2.rating,5,b_0,r_1,review_2)""")

def test_build_tree_assert_otherwise_aggregate():
	assert_in_transformation("""
@entity Book: title: str, author: str, genre: str, publication_year: int;
@entity Reader: name: str, age: int, favorite_genre: str;
@entity Review: book: Book, reader: Reader, rating: int, comment: str;
deny unless Book as b or Reader as r
	sum of {review.rating from Review as review} == 3
		or pay r.age at 5;""",
"""with Book() as b_0, Reader() as r_1, Review() as review_2:
	problem+=Assert(b_0, r_1).when(Sum({(review_2.rating):(review_2)})==3).otherwise(r_1.age,5,b_0,r_1)""")

def test_build_tree_assert_otherwise_not():
	assert_in_transformation("""
@entity Book: title: str, author: str, genre: str, publication_year: int;
@entity Reader: name: str, age: int, favorite_genre: str;
@entity Review: book: Book, reader: Reader, rating: int, comment: str;
deny unless Book as b
	from not Review as r
		count of {reader from Reader as reader where reader.age>15; r.comment} >= r.rating
		where r.book=b
			or pay b.publication_year at 5;""",
"""with Book() as b_0, Reader() as reader_2, Review(book = b_0) as r_1:
	problem+=Assert(b_0).when(~r_1, Count({(reader_2):(reader_2, reader_2.age>15), (r_1.comment):()})>=r_1.rating).otherwise(b_0.publication_year,5,b_0,r_1)""")

def test_build_tree_deny():
	assert_in_transformation("""
@entity Student: name: str, age: int, grade: str;
@entity Course: name: str, credits: int;
@entity Enrollment: student: Student, course: Course;

deny from Student, Course as c, Enrollment as e
	where e.student=Student and e.course=c and c.credits=2;""",
"""with Student() as s_0, Course() as c_1, Enrollment(student = s_0, course = c_1) as e_2:
	problem+=Assert(False).when(s_0, c_1, e_2, c_1.credits==2)""")

def test_build_tree_deny_aggregate():
	assert_in_transformation("""
@entity Student: name: str, age: int, grade: str;
@entity Course: name: str, credits: int;
@entity Enrollment: student: Student, course: Course;

deny from Student, Course as c
	count of {e.course from Enrollment as e where e.student=Student} > 2;""",
"""with Student() as s_0, Course() as c_1, Enrollment(student = s_0) as e_2:
	problem+=Assert(False).when(s_0, c_1, Count({(e_2.course):(e_2)})>2)""")

def test_build_tree_deny_not():
	assert_in_transformation("""
@entity Student: name: str, age: int, grade: str;
@entity Course: name: str, credits: int;
@entity Enrollment: student: Student, course: Course;

deny from not Student as s, Course as c, Enrollment
	where s.age>c.credits and c=Enrollment.course;""",
"""with Student() as s_0, Course() as c_1, Enrollment(course = c_1) as e_2:
	problem+=Assert(False).when(~s_0, c_1, e_2, s_0.age>c_1.credits)""")

def test_build_tree_assert():
	assert_in_transformation("""
@entity Customer: name: str, email: str, age: int;
@entity Product: name: str, price: int, category: str;
@entity Order: customer: Customer, product: Product, quantity: int, date: str;

deny unless Order as o
	from Product as p, Customer as c
		where o.customer=c and o.product=p and o.quantity=200 and p.price=20;""",
"""with Product() as p_1, Customer() as c_2, Order(customer = c_2, product = p_1) as o_0:
	problem+=Assert(o_0).when(p_1, c_2, o_0.quantity==200, p_1.price==20)""")
	
def test_build_tree_assert_aggregate():
	assert_in_transformation("""
@entity Customer: name: str, email: str, age: int;
@entity Product: name: str, price: int, category: str;
@entity Order: customer: Customer, product: Product, quantity: int, date: str;

deny unless Customer as c
	from Product as p
		count of {o.customer, o.product from Order as o where o.product=p} == 2
			where p.price=20;""",
"""with Customer() as c_0, Product() as p_1, Order(product = p_1) as o_2:
	problem+=Assert(c_0).when(p_1, p_1.price==20, Count({(o_2.customer, o_2.product):(o_2)})==2)""")

def test_build_tree_assert_not():
	assert_in_transformation("""
@entity Customer: name: str, email: str, age: int;
@entity Product: name: str, price: int, category: str;
@entity Order: customer: Customer, product: Product, quantity: int, date: str;

deny unless Customer as c
	from not Order as o
	where c=o.customer;""",
"""with Customer() as c_0, Order(customer = c_0) as o_1:
	problem+=Assert(c_0).when(~o_1)""")

def test_build_tree_deny_otherwise():
	assert_in_transformation("""
@entity Employee: name: str, department: str, position: str, salary: int;
@entity Project: name: str, department: str, deadline: str;
@entity Task: project: Project, assigned_to: Employee, description: str, status: str;
deny from Task as t, Project as p, Employee as e
	where t.project=p and t.assigned_to=e and e.salary<1000
		or pay e.salary at 3;""",
"""with Project() as p_1, Employee() as e_2, Task(project = p_1, assigned_to = e_2) as t_0:
	problem+=Assert(False).when(t_0, p_1, e_2, e_2.salary<1000).otherwise(e_2.salary,3,t_0,p_1,e_2)""")

def test_build_tree_deny_otherwise_aggregate():
	assert_in_transformation("""
@entity Employee: name: str, department: str, position: str, salary: int;
@entity Project: name: str, department: str, deadline: str;
@entity Task: project: Project, assigned_to: Employee, description: str, status: str;
deny from Task as t, Project as p
	count of {t2.project from Task as t2 where t2.project.department=t.project.department; em from Employee as em where em=t.assigned_to} > 1
		or pay t.assigned_to.salary at 3;""",
"""with Project() as p_1, Task() as t2_2, Employee() as em_3, Task(assigned_to = em_3) as t_0:
	problem+=Assert(False).when(t_0, p_1, Count({(t2_2.project):(t2_2, t2_2.project.department==t_0.project.department), (em_3):(em_3)})>1).otherwise(t_0.assigned_to.salary,3,t_0,p_1)""")

def test_build_tree_deny_otherwise_not():
	assert_in_transformation("""
@entity Employee: name: str, department: str, position: str, salary: int;
@entity Project: name: str, department: str, deadline: str;
@entity Task: project: Project, assigned_to: Employee, description: str, status: str;
deny from not Employee as e, Project as p
	sum of {t2.assigned_to.salary from not Task as t2 where e=t2.assigned_to} == e.salary
		or pay 7 at 2;""",
"""with Employee() as e_0, Project() as p_1, Task(assigned_to = e_0) as t2_2:
	problem+=Assert(False).when(~e_0, p_1, Sum({(t2_2.assigned_to.salary):(~t2_2)})==e_0.salary).otherwise(7,2,e_0,p_1)""")