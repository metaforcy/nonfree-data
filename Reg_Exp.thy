theory Reg_Exp
imports NonFree
uses "input.ML"
begin

nonfreedata 'a exp = Eps | Let 'a | Plus "'a exp" "'a exp" |
                     Times "'a exp" "'a exp" | Star "'a exp"
where
   Plus_Assoc: "Plus (Plus e1 e2) e3 = Plus e1 (Plus e2 e3)"
 | Plus_Comm: "Plus e1 e2 = Plus e2 e1"
 | Plus_Idem: "Plus e e = e"
 | Plus_Eps: "Plus Eps e = e"
 | Times_Eps: "Times Eps e = Eps"
 | Distr: "Times e1 (Plus e2 e3) = Plus (Times e1 e2) (Times e1 e3)"

nonfreeiter lang :: "'a exp \<Rightarrow> 'a list set"
where
  "lang Eps = {}"
| "lang (Let a) = {[a]}"
| "lang (Plus e1 e2) = lang e1 \<union> lang e2"
| "lang (Times e1 e2) = { w1 @ w2 | w1 w2. w1 \<in> lang e1 \<and> w2 \<in> lang e2}"
| "lang (Star e) = { List.concat ws | ws. set ws \<subseteq> lang e}"
by auto



end