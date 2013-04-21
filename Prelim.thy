theory Prelim
imports NonFreeInput
begin

type_synonym var = nat

fun neq where "neq x y = (x \<noteq> y)"
hide_const app hide_const App hide_const Var


end
