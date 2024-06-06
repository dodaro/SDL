{assign(nurse(X1), shift(X2, X3), day(X4)) : shift(X5, X6), nurse(X1)==nurse(X7), shift(X2, X3)==shift(X5, X6), day(X4)==day(X8)} = 1 :- day(X8); nurse(X7).
:- day(X1); nurseLimits(shift(X2, X3), X4, X5); #count{nurse(X6) : assign(nurse(X6), shift(X7, X8), day(X9)), shift(X7, X8)==shift(X2, X3), day(X9)==day(X1)} > X5.
:- day(X1); nurseLimits(shift(X2, X3), X4, X5); #count{nurse(X6) : assign(nurse(X6), shift(X7, X8), day(X9)), shift(X7, X8)==shift(X2, X3), day(X9)==day(X1)} < X4.
:- nurse(X1); hoursLimits(X2, X3); #sum{X4,day(X5) : assign(nurse(X6), shift(X8, X9), day(X5)), shift(X7, X4), nurse(X6)==nurse(X1), shift(X8, X9)==shift(X7, X4)} > X3.
:- nurse(X1); hoursLimits(X2, X3); #sum{X4,day(X5) : assign(nurse(X6), shift(X7, X9), day(X5)), shift(X8, X4), nurse(X6)==nurse(X1), shift(X7, X9)==shift(X8, X4)} < X2.
:- nurse(X1); #count{day(X2) : assign(nurse(X3), shift(X4, X5), day(X2)), nurse(X3)==nurse(X1), X4 = 6} != 30.
:- nurse(X1); assign(nurse(X2), shift(X3, X4), day(X5)); assign(nurse(X6), shift(X7, X8), day(X9)); nurse(X2)==nurse(X1); nurse(X6)==nurse(X1); X7 < X3; X5 = (X9 + 1); X7 <= 3; X3 <= 3.
:- nurse(X1); day(X2); X2 <= 352; #count{day(X3) : assign(nurse(X4), shift(X5, X6), day(X3)), nurse(X4)==nurse(X1), X5 = 5, X3 >= X2, X3 < (X2 + 14)} < 2.
:- assign(nurse(X1), shift(X2, X3), day(X4)); assign(nurse(X5), shift(X6, X7), day(X8)); assign(nurse(X9), shift(X10, X11), day(X12)); X1 = X5; X1 = X9; X2 = 4; X6 = 3; X10 = 3; X8 = (X4 - 2); X12 = (X4 - 1).
:- assign(nurse(X1), shift(X2, X3), day(X4)); not assign(nurse(X5), shift(X6, _), day(X7)); nurse(X1)==nurse(X5); X2 = 4; X6 = 3; X7 = (X4 - 2).
:- assign(nurse(X1), shift(X2, X3), day(X4)); not assign(nurse(X5), shift(X6, _), day(X7)); nurse(X1)==nurse(X5); X2 = 4; X6 = 3; X7 = (X4 - 1).
