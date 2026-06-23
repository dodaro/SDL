int: nurse_len = 5;
array[1..nurse_len] of int: nurse_id = [1, 2, 3, 4, 5];

int: day_len = 10;
array[1..day_len] of int: day_id = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

int: shift_len = 6;
array[1..shift_len] of int: shift_id = [1, 2, 3, 4, 5, 6];
array[1..shift_len] of int: shift_hours = [7, 7, 10, 0, 0, 0];

int: hourslimits_len = 1;
array[1..hourslimits_len] of int: hourslimits_min = [43];
array[1..hourslimits_len] of int: hourslimits_max = [48];

int: daylimits_len = 3;
array[1..daylimits_len] of int: daylimits_shift_id = [1, 2, 3];
array[1..daylimits_len] of int: daylimits_shift_hours = [7, 7, 10];
array[1..daylimits_len] of int: daylimits_min = [2, 2, 1];
array[1..daylimits_len] of int: daylimits_max = [3, 3, 2];

int: nurselimits_len = 3;
array[1..nurselimits_len] of int: nurselimits_shift_id = [1, 2, 3];
array[1..nurselimits_len] of int: nurselimits_shift_hours = [7, 7, 10];
array[1..nurselimits_len] of int: nurselimits_min = [1, 1, 0];
array[1..nurselimits_len] of int: nurselimits_max = [2, 2, 1];

int: nurselimits_min_len = 2;
array[1..nurselimits_min_len] of int: nurselimits_min_value = [0, 1];

int: nurselimits_max_len = 2;
array[1..nurselimits_max_len] of int: nurselimits_max_value = [1, 2];

int: daylimits_min_len = 2;
array[1..daylimits_min_len] of int: daylimits_min_value = [1, 2];

int: daylimits_max_len = 2;
array[1..daylimits_max_len] of int: daylimits_max_value = [2, 3];

array[1..day_len, 1..nurse_len] of var 1..shift_len: assign;
array[1..day_len] of var bool: day;
array[1..nurse_len] of var bool: nurse;
array[1..shift_len] of var bool: shift;
array[1..hourslimits_len] of var bool: hourslimits;
array[1..shift_len, 1..nurselimits_min_len, 1..nurselimits_max_len] of var bool: nurselimits;
array[1..shift_len, 1..daylimits_min_len, 1..daylimits_max_len] of var bool: daylimits;
constraint forall(day_base in 1..day_len)(
    day[day_base] <-> (
      (day_id[day_base] in 1..10)
    )
);

constraint forall(nurse_base in 1..nurse_len)(
    nurse[nurse_base] <-> (
      (nurse_id[nurse_base] in 1..5)
    )
);

constraint forall(shift_base in 1..shift_len)(
    shift[shift_base] <-> (
      (shift_id[shift_base] == 1 /\ shift_hours[shift_base] == 7)
      \/ (shift_id[shift_base] == 2 /\ shift_hours[shift_base] == 7)
      \/ (shift_id[shift_base] == 3 /\ shift_hours[shift_base] == 10)
      \/ (shift_id[shift_base] == 4 /\ shift_hours[shift_base] == 0)
      \/ (shift_id[shift_base] == 5 /\ shift_hours[shift_base] == 0)
      \/ (shift_id[shift_base] == 6 /\ shift_hours[shift_base] == 0)
    )
);

constraint forall(hourslimits_base in 1..hourslimits_len)(
    hourslimits[hourslimits_base] <-> (
      (hourslimits_min[hourslimits_base] == 43 /\ hourslimits_max[hourslimits_base] == 48)
    )
);

constraint forall(nurselimits_shift in 1..shift_len, nurselimits_min in 1..nurselimits_min_len, nurselimits_max in 1..nurselimits_max_len)(
    nurselimits[nurselimits_shift, nurselimits_min, nurselimits_max] <-> (
      (shift_id[nurselimits_shift] == 1 /\ shift_hours[nurselimits_shift] == 7 /\ nurselimits_min_value[nurselimits_min] == 1 /\ nurselimits_max_value[nurselimits_max] == 2)
      \/ (shift_id[nurselimits_shift] == 2 /\ shift_hours[nurselimits_shift] == 7 /\ nurselimits_min_value[nurselimits_min] == 1 /\ nurselimits_max_value[nurselimits_max] == 2)
      \/ (shift_id[nurselimits_shift] == 3 /\ shift_hours[nurselimits_shift] == 10 /\ nurselimits_min_value[nurselimits_min] == 0 /\ nurselimits_max_value[nurselimits_max] == 1)
    )
);

constraint forall(daylimits_shift in 1..shift_len, daylimits_min in 1..daylimits_min_len, daylimits_max in 1..daylimits_max_len)(
    daylimits[daylimits_shift, daylimits_min, daylimits_max] <-> (
      (shift_id[daylimits_shift] == 1 /\ shift_hours[daylimits_shift] == 7 /\ daylimits_min_value[daylimits_min] == 2 /\ daylimits_max_value[daylimits_max] == 3)
      \/ (shift_id[daylimits_shift] == 2 /\ shift_hours[daylimits_shift] == 7 /\ daylimits_min_value[daylimits_min] == 2 /\ daylimits_max_value[daylimits_max] == 3)
      \/ (shift_id[daylimits_shift] == 3 /\ shift_hours[daylimits_shift] == 10 /\ daylimits_min_value[daylimits_min] == 1 /\ daylimits_max_value[daylimits_max] == 2)
    )
);

constraint forall(Day_base in 1..day_len, NurseLimits_base in 1..nurselimits_len)(
    not ((sum(Assign_day_aggr in 1..day_len, Assign_nurse_aggr in 1..nurse_len)(bool2int(shift_id[assign[Assign_day_aggr, Assign_nurse_aggr]] == nurselimits_shift_id[NurseLimits_base] /\ day_id[Assign_day_aggr] == day_id[Day_base]))) > nurselimits_max[NurseLimits_base])
);
constraint forall(Day_base in 1..day_len, NurseLimits_base in 1..nurselimits_len)(
    not ((sum(Assign_day_aggr in 1..day_len, Assign_nurse_aggr in 1..nurse_len)(bool2int(shift_id[assign[Assign_day_aggr, Assign_nurse_aggr]] == nurselimits_shift_id[NurseLimits_base] /\ day_id[Assign_day_aggr] == day_id[Day_base]))) < nurselimits_min[NurseLimits_base])
);
constraint forall(Nurse_base in 1..nurse_len, HoursLimits_base in 1..hourslimits_len)(
    not ((sum(Shift_aggr in 1..shift_len, Assign_day_aggr in 1..day_len, Assign_nurse_aggr in 1..nurse_len)(if nurse_id[Assign_nurse_aggr] == nurse_id[Nurse_base] /\ shift_id[assign[Assign_day_aggr, Assign_nurse_aggr]] == shift_id[Shift_aggr] /\ shift_hours[assign[Assign_day_aggr, Assign_nurse_aggr]] == shift_hours[Shift_aggr] then shift_hours[Shift_aggr] else 0 endif)) > hourslimits_max[HoursLimits_base])
);
constraint forall(Nurse_base in 1..nurse_len, HoursLimits_base in 1..hourslimits_len)(
    not ((sum(Shift_aggr in 1..shift_len, Assign_day_aggr in 1..day_len, Assign_nurse_aggr in 1..nurse_len)(if nurse_id[Assign_nurse_aggr] == nurse_id[Nurse_base] /\ shift_id[assign[Assign_day_aggr, Assign_nurse_aggr]] == shift_id[Shift_aggr] /\ shift_hours[assign[Assign_day_aggr, Assign_nurse_aggr]] == shift_hours[Shift_aggr] then shift_hours[Shift_aggr] else 0 endif)) < hourslimits_min[HoursLimits_base])
);
constraint forall(Nurse_base in 1..nurse_len)(
    not ((sum(Assign_day_aggr in 1..day_len, Assign_nurse_aggr in 1..nurse_len)(bool2int(nurse_id[Assign_nurse_aggr] == nurse_id[Nurse_base] /\ shift_id[assign[Assign_day_aggr, Assign_nurse_aggr]] == 6))) != 2)
);
constraint forall(Nurse_base in 1..nurse_len, a1_day_base in 1..day_len, a2_day_base in 1..day_len where day_id[a1_day_base]+1 == day_id[a2_day_base])(
    not (shift_id[assign[a2_day_base, Nurse_base]] < shift_id[assign[a1_day_base, Nurse_base]] /\ shift_id[assign[a2_day_base, Nurse_base]] <= 3 /\ shift_id[assign[a1_day_base, Nurse_base]] <= 3)
);
constraint forall(Nurse_base in 1..nurse_len, Day_base in 1..day_len where day_id[Day_base] <= 3)(
    not ((sum(Assign_day_aggr in 1..day_len, Assign_nurse_aggr in 1..nurse_len)(bool2int(nurse_id[Assign_nurse_aggr] == nurse_id[Nurse_base] /\ shift_id[assign[Assign_day_aggr, Assign_nurse_aggr]] == 5 /\ day_id[Assign_day_aggr] in day_id[Day_base]..day_id[Day_base]+6))) < 2)
);
constraint forall(a2_day_base in 1..day_len, a2_nurse_base in 1..nurse_len, a3_day_base in 1..day_len where day_id[a3_day_base] == day_id[a2_day_base]+1)(
    not (shift_id[assign[a2_day_base, a2_nurse_base]] == 3 /\ shift_id[assign[a3_day_base, a2_nurse_base]] == 3 /\ not exists(a1_day_base in 1..day_len)(
        day_id[a1_day_base] == day_id[a3_day_base]+1 /\ shift_id[assign[a1_day_base, a2_nurse_base]] == 4
    ))
);
constraint forall(a1_day_base in 1..day_len, a1_nurse_base in 1..nurse_len)(
    not (shift_id[assign[a1_day_base, a1_nurse_base]] == 4 /\ not exists(a2_day_base in 1..day_len)(
        day_id[a2_day_base] == day_id[a1_day_base]-2 /\ shift_id[assign[a2_day_base, a1_nurse_base]] == 3
    ))
);
constraint forall(a1_day_base in 1..day_len, a1_nurse_base in 1..nurse_len)(
    not (shift_id[assign[a1_day_base, a1_nurse_base]] == 4 /\ not exists(a2_day_base in 1..day_len)(
        day_id[a2_day_base] == day_id[a1_day_base]-1 /\ shift_id[assign[a2_day_base, a1_nurse_base]] == 3
    ))
);
constraint forall(Nurse_base in 1..nurse_len, DayLimits_base in 1..daylimits_len)(
    not ((sum(Assign_day_aggr in 1..day_len, Assign_nurse_aggr in 1..nurse_len)(bool2int(shift_id[assign[Assign_day_aggr, Assign_nurse_aggr]] == daylimits_shift_id[DayLimits_base] /\ nurse_id[Assign_nurse_aggr] == nurse_id[Nurse_base]))) > daylimits_max[DayLimits_base])
);
constraint forall(Nurse_base in 1..nurse_len, DayLimits_base in 1..daylimits_len)(
    not ((sum(Assign_day_aggr in 1..day_len, Assign_nurse_aggr in 1..nurse_len)(bool2int(shift_id[assign[Assign_day_aggr, Assign_nurse_aggr]] == daylimits_shift_id[DayLimits_base] /\ nurse_id[Assign_nurse_aggr] == nurse_id[Nurse_base]))) < daylimits_min[DayLimits_base])
);
output [
    "Assign(Day(\(day_id[i_1])), Nurse(\(nurse_id[i_2]))) -> Shift(\(shift_id[fix(assign[i_1, i_2])]), \(shift_hours[fix(assign[i_1, i_2])]))\n"
    | i_1 in 1..day_len, i_2 in 1..nurse_len where fix(assign[i_1, i_2]) > 0
];

solve satisfy;
