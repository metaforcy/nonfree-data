header {* Preliminaries *}

(* author: Andrei Popescu *)


theory Preliminaries imports Main

begin


text {* Thus section discusses preliminaries on families of items (technically, 
partial functions from a type of {\em indexes}) 
that we call {\em inputs} because they will be inputs to the binding operations.  
For inputs, we define some monad-like lifting operators. 
We also define simple infinitely branching trees (with no info attached 
to the nodes and with branching given by partial functions from 
indexes) -- these will be used as ``skeletons" for terms, giving a size on which we can induct. 
 *}



subsection {* Trivia  *}


types 'a pair = "'a * 'a"

types 'a triple = "'a * 'a *'a"

types 'a rel = "'a pair set"


(* Selectors for triples *)

definition fst3 where "fst3 == fst"
definition snd3 where "snd3 == fst o snd"
definition trd3 where "trd3 == snd o snd"


lemma fst3_simp[simp]: "fst3 (a,b,c) = a"
unfolding fst3_def by simp


lemma snd3_simp[simp]: "snd3 (a,b,c) = b"
unfolding snd3_def by simp


lemma trd3_simp[simp]: "trd3 (a,b,c) = c"
unfolding trd3_def by simp


lemma fst3_snd3_trd3: "abc = (fst3 abc, snd3 abc, trd3 abc)"
unfolding fst3_def snd3_def trd3_def by auto


lemma fst3_snd3_trd3_rev[simp]:
"(fst3 abc, snd3 abc, trd3 abc) = abc"
using fst3_snd3_trd3[of abc] by simp


lemma map_id[simp]: "map id l = l"
unfolding id_def by simp


abbreviation max3 where 
"max3 x y z == max (max x y) z"


lemma map_id_cong:
assumes "!! x. x : set L \<Longrightarrow> f x = x"
shows "map f L = L"
proof-
  have "map f L = map id L"
  apply(rule map_cong)
  using assms by auto
  thus ?thesis by simp
qed


lemma ext2: 
"(f \<noteq> g) = (\<exists> x. f x \<noteq> g x)"
proof-
  have "(f = g) = (\<forall> x. f x = g x)"
  by(auto simp add: ext)
  thus ?thesis by blast
qed


lemma not_equals_and_not_equals_not_in:
"(y \<noteq> x \<and> y \<noteq> x' \<and> phi) = 
 (y \<notin> {x,x'} \<and> phi)"
by simp


lemma mp2: 
assumes "!! x y. phi x y \<Longrightarrow> chi x y" and "phi x y"
shows "chi x y"
using assms by simp


lemma mp3: 
assumes "!! x y z. phi x y z \<Longrightarrow> chi x y z" and "phi x y z"
shows "chi x y z"
using assms by simp


lemma all_lt_Suc: 
"(\<forall> i < Suc n. phi i) = 
 ((\<forall> i < n. phi i) \<and> phi n)"
apply auto
by (case_tac "i = n", auto)


lemma hd_map[simp]:
assumes "L \<noteq> []"
shows "hd (map f L) = f (hd L)"
using assms apply - by(induct L, auto)


lemma tl_map[simp]:
assumes "L \<noteq> []"
shows "tl (map f L) = map f (tl L)"
using assms apply - by(induct L, auto)


lemma last_map[simp]:
assumes "L \<noteq> []"
shows "last (map f L) = f (last L)"
using assms apply - by(induct L, auto)


lemma tl_last[simp]:
assumes "tl L \<noteq> []"
shows "last (tl L) = last L"
using assms apply - by(induct L, auto)


lemma tl_last_hd:
assumes "L \<noteq> []" and "tl L = []"
shows "last L = hd L"
using assms apply - by(induct L, auto)



subsection {* Lexicographic induction *}


definition lt2 where 
"lt2 == less_than <*lex*> less_than"


definition lt3 where 
"lt3 == less_than <*lex*> lt2"


lemma wf_lt2:
"wf lt2"
unfolding lt2_def by auto 


lemma wf_lt3:
"wf lt3"
unfolding lt3_def by (auto simp add: wf_lt2)


lemma lt2[intro]:
"!! k1 k2 j1 j2. k1 < j1 \<Longrightarrow> ((k1,k2),(j1,j2)) \<in> lt2"
"!! k1 k2 j1 j2. \<lbrakk>k1 \<le> j1; k2 < j2\<rbrakk> \<Longrightarrow> ((k1,k2),(j1,j2)) \<in> lt2"
unfolding lt2_def by auto


lemma lt3[intro]:
"!! k1 k2 k3 j1 j2 j3. k1 < j1 \<Longrightarrow> ((k1,k2,k3),(j1,j2,j3)) \<in> lt3"
"!! k1 k2 k3 j1 j2 j3. \<lbrakk>k1 \<le> j1; k2 < j2\<rbrakk> \<Longrightarrow> ((k1,k2,k3),(j1,j2,j3)) \<in> lt3"
"!! k1 k2 k3 j1 j2 j3. \<lbrakk>k1 \<le> j1; k2 \<le> j2; k3 < j3\<rbrakk> \<Longrightarrow> ((k1,k2,k3),(j1,j2,j3)) \<in> lt3"
unfolding lt3_def by auto


lemma measure_lex2_induct:
fixes h1 :: "'a1 \<Rightarrow> nat" and h2 :: "'a2 \<Rightarrow> nat"
assumes 
"!! x1 x2. 
  \<lbrakk>(!! y1 y2. h1 y1 < h1 x1 \<Longrightarrow> phi y1 y2);
   (!! y1 y2. \<lbrakk>h1 y1 \<le> h1 x1; h2 y2 < h2 x2\<rbrakk> \<Longrightarrow> phi y1 y2)\<rbrakk> 
  \<Longrightarrow> phi x1 x2" 
shows "phi x1 x2"
proof-
  let ?chi = "%(n1,n2). ALL x1 x2. h1 x1 = n1 \<and> h2 x2 = n2 \<longrightarrow> phi x1 x2"
  {fix n1 n2 
   have "?chi (n1,n2)"
   apply(rule wf_induct[of lt2 ?chi]) using wf_lt2 assms by blast+
  }
  thus ?thesis by blast 
qed


lemma measure_lex3_induct:
fixes h1 :: "'a1 \<Rightarrow> nat" and h2 :: "'a2 \<Rightarrow> nat" and h3 :: "'a3 \<Rightarrow> nat"
assumes 
"!! x1 x2 x3. 
  \<lbrakk>(!! y1 y2 y3. h1 y1 < h1 x1 \<Longrightarrow> phi y1 y2 y3);
   (!! y1 y2 y3. \<lbrakk>h1 y1 \<le> h1 x1; h2 y2 < h2 x2\<rbrakk> \<Longrightarrow> phi y1 y2 y3); 
   (!! y1 y2 y3. \<lbrakk>h1 y1 \<le> h1 x1; h2 y2 \<le> h2 x2; h3 y3 < h3 x3\<rbrakk> \<Longrightarrow> phi y1 y2 y3)\<rbrakk> 
  \<Longrightarrow> phi x1 x2 x3" 
shows "phi x1 x2 x3"
proof-
  let ?chi = "%(n1,n2,n3). ALL x1 x2 x3. h1 x1 = n1 \<and> h2 x2 = n2 \<and> h3 x3 = n3 \<longrightarrow> phi x1 x2 x3"
  {fix n1 n2 n3
   have "?chi (n1,n2,n3)"
   apply(rule wf_induct[of lt3 ?chi]) using wf_lt3 assms by blast+
  }
  thus ?thesis by blast 
qed



subsection {* Inputs and lifting operators  *}


types ('index,'val)input = "'index \<Rightarrow> 'val option" 


definition  
lift :: "('val1 \<Rightarrow> 'val2) \<Rightarrow> ('index,'val1)input \<Rightarrow> ('index,'val2)input"
where 
"lift h inp == \<lambda>i. case inp i of None \<Rightarrow> None 
                                |Some v \<Rightarrow> Some (h v)"


definition  
liftAll :: "('val \<Rightarrow> bool) \<Rightarrow> ('index,'val)input \<Rightarrow> bool"
where 
"liftAll phi inp == \<forall> i v. inp i = Some v \<longrightarrow> phi v"


definition  
lift2 :: 
"('val1' \<Rightarrow> 'val1 \<Rightarrow> 'val2) \<Rightarrow> ('index,'val1')input \<Rightarrow> ('index,'val1)input \<Rightarrow> ('index,'val2)input"
where 
"lift2 h inp' inp == 
 \<lambda>i. case (inp' i, inp i) of 
   (Some v',Some v) \<Rightarrow> Some (h v' v)
  |_ \<Rightarrow> None"


definition 
sameDom ::  "('index,'val1)input \<Rightarrow> ('index,'val2)input \<Rightarrow> bool"
where "sameDom inp1 inp2 == \<forall> i. (inp1 i = None) = (inp2 i = None)"


definition  
liftAll2 :: "('val1 \<Rightarrow> 'val2 \<Rightarrow> bool) \<Rightarrow> ('index,'val1)input \<Rightarrow> ('index,'val2)input \<Rightarrow> bool"
where 
"liftAll2 phi inp1 inp2 == (\<forall> i v1 v2. inp1 i = Some v1 \<and> inp2 i = Some v2 \<longrightarrow> phi v1 v2)"
  

lemma lift_None: "(lift h inp i = None) = (inp i = None)"
unfolding lift_def by (cases "inp i", auto)


lemma lift_Some: 
"(\<exists> v. lift h inp i = Some v) = (\<exists> v'. inp i = Some v')"
using lift_None[of h inp i] by force 
    
        
lemma lift_cong[fundef_cong]:
assumes "\<And> i v. inp i = Some v \<Longrightarrow>  h v = h' v"
shows "lift h inp = lift h' inp"
unfolding lift_def apply(rule ext)+
using assms by (case_tac "inp i", auto)


lemma lift_preserves_inj:
assumes "inj f"
shows "inj (lift f)"
unfolding inj_on_def apply auto proof(rule ext)
  fix inp inp' i assume *: "lift f inp = lift f inp'"
  show "inp i = inp' i"
  proof(cases "inp i")
    assume inp: "inp i = None"
    hence "lift f inp i = None" unfolding lift_def by simp
    hence "lift f inp' i = None" using * by simp
    hence "inp' i = None" by(auto simp add: lift_None)
    thus ?thesis using inp by simp
  next
    fix v assume inp: "inp i = Some v"
    hence "lift f inp i = Some (f v)" unfolding lift_def by simp 
    hence "lift f inp' i = Some (f v)" using * by simp
    then obtain v' where inp': "inp' i = Some v'" and "f v' = f v"
    unfolding lift_def by(case_tac "inp' i", auto)
    hence "v = v'" using assms unfolding inj_on_def by simp
    thus ?thesis using inp inp' by simp
  qed
qed


lemma liftAll_cong[fundef_cong]:
assumes "\<And> i v. inp i = Some v \<Longrightarrow> phi v = phi' v"
shows "liftAll phi inp = liftAll phi' inp"
unfolding liftAll_def apply((rule iff_allI)+) using assms by simp


lemma sameDom_cong[fundef_cong]:
assumes "\<And> i. (inp1 i = None) = (inp2 i = None)"
shows "sameDom inp1 inp2 = sameDom inp1 inp2"
unfolding sameDom_def apply((rule iff_allI)+) using assms by blast


lemma liftAll2_cong[fundef_cong]:
assumes "\<And> i v1 v2. \<lbrakk>inp1 i = Some v1; inp2 i = Some v2\<rbrakk> \<Longrightarrow> phi v1 v2 = phi' v1 v2"
shows "liftAll2 phi inp1 inp2 = liftAll2 phi' inp1 inp2"
unfolding liftAll2_def apply((rule iff_allI)+) using assms by blast


lemma lift_ident: "lift (\<lambda>v. v) inp = inp"
by(unfold lift_def, rule ext, case_tac "inp i", auto)


lemma lift_id[simp]: 
"lift id inp = inp" 
unfolding lift_def apply (rule ext) by(case_tac "inp i", auto)


lemma lift_comp: "lift g (lift f inp) = lift (g o f) inp"
by(unfold lift_def o_def, rule ext, case_tac "inp i", auto)


lemma liftAll_mono:
assumes "\<And> v. phi v \<Longrightarrow> chi v" and "liftAll phi inp"
shows "liftAll chi inp"
using assms unfolding liftAll_def by blast


lemma liftAll_True: "liftAll (\<lambda>v. True) inp"
unfolding liftAll_def by auto


lemma liftAll_lift_comp:  "liftAll phi (lift f inp) = liftAll (phi o f) inp"
unfolding liftAll_def o_def
apply (rule iff_allI)
proof(auto)
  fix i v
  assume 1: "\<forall>w. lift f inp i = Some w \<longrightarrow> phi w" and 2: "inp i = Some v"
  thus "phi (f v)" unfolding lift_def by force
next
  fix i w
  assume 1: "\<forall>v. inp i = Some v \<longrightarrow> phi (f v)" and "lift f inp i = Some w"
  then obtain v where "inp i = Some v" and 2: "w = f v" 
  unfolding lift_def by (cases "inp i", auto)
  thus "phi w" unfolding 2 using 1 by simp
qed


lemma liftAll_lift_ext:
"liftAll (\<lambda> x. f x = g x) inp = (lift f inp = lift g inp)"
unfolding lift_def liftAll_def
apply auto
apply(rule ext)  apply (case_tac "inp i", auto)
by(drule_tac x = i in fun_cong, auto)


lemma liftAll_and:
"liftAll (\<lambda> x. phi x \<and> chi x) inp = (liftAll phi inp \<and> liftAll chi inp)"
using assms unfolding liftAll_def by blast


lemma liftAll_mp:
assumes "liftAll (\<lambda> v. phi v \<longrightarrow> chi v) inp" and "liftAll phi inp"
shows "liftAll chi inp"
using assms unfolding liftAll_def by auto


lemma sameDom_refl: "sameDom inp inp"
unfolding sameDom_def by auto


lemma sameDom_sym:
"sameDom inp inp' = sameDom inp' inp"
unfolding sameDom_def by auto


lemma sameDom_trans: 
"\<lbrakk>sameDom inp inp'; sameDom inp' inp''\<rbrakk> \<Longrightarrow> sameDom inp inp''"
unfolding sameDom_def by auto


lemma sameDom_lift1:
"sameDom inp (lift f inp)"
unfolding sameDom_def lift_def 
apply clarify by(case_tac "inp i", auto)


lemma sameDom_lift2:
"sameDom (lift f inp) inp"
unfolding sameDom_def lift_def 
apply clarify by(case_tac "inp i", auto)


lemma sameDom_lift_simp1[simp]: 
"sameDom inp (lift f inp') = sameDom inp inp'"
proof
  assume "sameDom inp (lift f inp')"
  hence "sameDom (lift f inp') inp" using sameDom_sym by auto
  moreover have "sameDom inp' (lift f inp')" using sameDom_lift1 by auto
  ultimately have "sameDom inp' inp" using sameDom_trans by blast
  thus "sameDom inp inp'" using sameDom_sym by auto
next
  assume "sameDom inp inp'"
  moreover have "sameDom inp' (lift f inp')" using sameDom_lift1 by auto
  ultimately show "sameDom inp (lift f inp')" using sameDom_trans by blast
qed


lemma sameDom_lift_simp2[simp]: 
"sameDom (lift f inp) inp' = sameDom inp inp'"
proof-
  have "sameDom (lift f inp) inp' = sameDom inp' (lift f inp)"
  using sameDom_sym by blast
  also have "\<dots> = sameDom inp' inp" by simp
  also have "\<dots> = sameDom inp inp'" using sameDom_sym by auto
  finally show ?thesis .
qed


lemma lift_preserves_sameDom:
assumes "sameDom inp inp'"
shows "sameDom (lift f inp) (lift g inp')"
proof-
  have "sameDom (lift f inp) inp" using sameDom_lift2 by auto
  moreover have "sameDom inp' (lift g inp')" using sameDom_lift1 by auto
  ultimately show ?thesis 
  using assms sameDom_trans[of "lift f inp" inp] 
              sameDom_trans[of "lift f inp" inp'] by blast
qed


definition comp2 :: 
"('b1 \<Rightarrow> 'b2 \<Rightarrow> 'c) \<Rightarrow> ('a1 \<Rightarrow> 'b1) \<Rightarrow> ('a2 \<Rightarrow> 'b2) \<Rightarrow> ('a1 \<Rightarrow> 'a2 \<Rightarrow> 'c)" 
("_ o2 '(_,_')" 55)
where "h o2 (f,g) == \<lambda> x y. h (f x) (g y)"

term "comp2 h f g"


lemma comp2_simp[simp]:
"(h o2 (f,g)) x y = h (f x) (g y)"
unfolding comp2_def by simp


lemma comp2_comp:
"((h o2 (f,g)) o2 (f',g')) = (h o2 (f o f', g o g'))"
unfolding comp_def_raw comp2_def_raw by(rule ext, auto)


lemma liftAll_imp_liftAll2:
assumes "liftAll (\<lambda>v. \<forall> v'. phi v v') inp"
shows "liftAll2 phi inp inp'"
using assms unfolding liftAll_def liftAll2_def by auto


lemma liftAll2_mono:
assumes "\<And> v v'. phi v v' \<Longrightarrow> chi v v'" and "liftAll2 phi inp inp'"
shows "liftAll2 chi inp inp'"
using assms unfolding liftAll2_def by blast


lemma liftAll2_True: "liftAll2 (\<lambda> v v'. True) inp inp'"
unfolding liftAll2_def by auto


lemma liftAll2_lift_comp2:  
"liftAll2 phi (lift f1 inp1) (lift f2 inp2) = 
 liftAll2 (phi o2 (f1,f2)) inp1 inp2"
unfolding liftAll2_def comp2_def_raw 
proof(rule iff_allI,auto)
  fix i v1 v2 assume "inp1 i = Some v1" and "inp2 i = Some v2" and 
  "\<forall>w1 w2. lift f1 inp1 i = Some w1 \<and> lift f2 inp2 i = Some w2 \<longrightarrow> phi w1 w2"
  thus "phi (f1 v1) (f2 v2)" unfolding lift_def by auto
next
  fix i w1 w2
  assume 1: "\<forall>v1 v2. inp1 i = Some v1 \<and> inp2 i = Some v2 \<longrightarrow> phi (f1 v1) (f2 v2)" and 
  "lift f1 inp1 i = Some w1" and 2: "lift f2 inp2 i = Some w2"
  then obtain v1 where inp1: "inp1 i = Some v1" and w1: "w1 = f1 v1" 
  unfolding lift_def by (cases "inp1 i", auto)
  obtain v2 where inp2: "inp2 i = Some v2" and w2: "w2 = f2 v2" 
  using 1 2 unfolding lift_def by (cases "inp2 i", auto)
  show "phi w1 w2" using 1 unfolding inp1 inp2 w1 w2 by simp
qed


lemma lift_imp_sameDom: 
"lift f inp = lift f inp' \<Longrightarrow> sameDom inp inp'"
unfolding lift_def sameDom_def
apply clarify
apply(drule_tac x = i in fun_cong)
by(case_tac "inp i", (case_tac "inp' i", auto)+)


lemma lift_lift2:
"lift f (lift2 g inp' inp) = 
 lift2 (\<lambda> v' v. f (g v' v)) inp' inp"
unfolding lift_def lift2_def 
apply(rule ext) apply simp
apply(case_tac "inp' i", auto)
by(case_tac "inp i", auto)


lemma lift2_left[simp]:
assumes "sameDom inp' inp"
shows "lift2 (\<lambda> v' v. v') inp' inp = inp'"
unfolding lift2_def apply(rule ext)
apply(case_tac "inp' i", auto)
apply(case_tac "inp i", auto)
using assms unfolding sameDom_sym[of inp' inp]
unfolding sameDom_def by simp


lemma lift2_right[simp]:
assumes "sameDom inp' inp"
shows "lift2 (\<lambda> v' v. v) inp' inp = inp"
unfolding lift2_def apply(rule ext)
apply(case_tac "inp i", auto)
apply(case_tac "inp' i", auto) apply(case_tac "inp' i", auto)
using assms 
unfolding sameDom_def by simp


lemma lift2_preserves_sameDom: 
assumes *: "sameDom inp' inp1'" and **: "sameDom inp inp1"
shows "sameDom (lift2 f inp' inp) (lift2 g inp1' inp1)"
proof-
  let ?finp = "lift2 f inp' inp"
  let ?ginp = "lift2 g inp1' inp1"
  show ?thesis
  unfolding sameDom_def apply clarify
  proof-
    fix i 
    have "?finp i = None = (inp' i = None \<or> inp i = None)"
    unfolding lift2_def apply(cases "inp' i", simp_all)
    by(cases "inp i", auto)
    also have "\<dots> = (inp1' i = None \<or> inp1 i = None)"
    using assms unfolding sameDom_def by simp
    also have "\<dots> = (?ginp i = None)" 
    unfolding lift2_def apply(cases "inp1' i", simp_all)
    by(cases "inp1 i", auto)
    finally show "(?finp i = None) = (?ginp i = None)" .
  qed
qed


lemma sameDom_lift2_1: 
assumes "sameDom inp' inp"
shows 
"sameDom inp' (lift2 f inp' inp) \<and> 
 sameDom inp (lift2 f inp' inp)"
proof-
  let ?finp = "lift2 f inp' inp"
  have 1: "sameDom inp' (lift2 f inp' inp)"
  unfolding sameDom_def lift2_def apply clarsimp
  apply(case_tac "inp' i", auto)  apply(case_tac "inp i", auto)
  using assms unfolding sameDom_sym[of inp' inp]
  unfolding sameDom_def by simp
  hence "sameDom inp (lift2 f inp' inp)"
  using assms sameDom_sym sameDom_trans by blast
  thus ?thesis using 1 by simp
qed


lemma sameDom_lift2_2: 
assumes "sameDom inp' inp"
shows 
"sameDom (lift2 f inp' inp) inp' \<and> 
 sameDom (lift2 f inp' inp) inp"
using assms 
apply - apply(drule sameDom_lift2_1[of _ _ f])
apply auto using sameDom_sym by blast+


lemma sameDom_lift2_simp1[simp]: 
assumes "sameDom inp1' inp1"
shows "sameDom inp (lift2 f inp1' inp1) = sameDom inp inp1'"
proof
  assume "sameDom inp (lift2 f inp1' inp1)"
  hence "sameDom (lift2 f inp1' inp1) inp" using sameDom_sym by auto
  moreover have "sameDom inp1' (lift2 f inp1' inp1)"
  using assms sameDom_lift2_1 by auto
  ultimately have "sameDom inp1' inp" using sameDom_trans by blast
  thus "sameDom inp inp1'" using sameDom_sym by auto
next
  assume "sameDom inp inp1'"
  moreover have "sameDom inp1' (lift2 f inp1' inp1)" 
  using assms sameDom_lift2_1 by auto
  ultimately show "sameDom inp (lift2 f inp1' inp1)"
  using sameDom_trans by blast
qed


lemma sameDom_lift2_simp2[simp]:
assumes "sameDom inp' inp" 
shows "sameDom (lift2 f inp' inp) inp1 = sameDom inp' inp1"
proof-
  have "sameDom (lift2 f inp' inp) inp1 = sameDom inp1 (lift2 f inp' inp)"
  using sameDom_sym by blast
  also have "\<dots> = sameDom inp1 inp'" using assms by simp
  also have "\<dots> = sameDom inp' inp1" using sameDom_sym by auto
  finally show ?thesis .
qed 


lemma liftAll2_lift_ext:
"(sameDom inp inp' \<and> liftAll2 (\<lambda> v v'. f v = f v') inp inp') = 
 (lift f inp = lift f inp')"
apply (auto simp add: lift_imp_sameDom)
unfolding lift_def liftAll2_def 
apply auto
  apply(rule ext)+  
  apply(case_tac "inp i") 
    apply(case_tac "inp' i")
      apply simp
      apply(simp add: sameDom_def)
    apply(case_tac "inp' i")
      apply (auto simp add: sameDom_def) 
      apply force
by(drule_tac x = i in fun_cong, auto)


lemma liftAll2_and:
"liftAll2 (\<lambda> v v'. phi v v' \<and> chi v v') inp inp' = 
(liftAll2 phi inp inp' \<and> liftAll2 chi inp inp')"
using assms unfolding liftAll2_def by force


lemma liftAll2_mp:
assumes "liftAll2 (\<lambda> v v'. phi v v' \<longrightarrow> chi v v') inp inp'" and "liftAll2 phi inp inp'"
shows "liftAll2 chi inp inp'"
using assms unfolding liftAll2_def by auto


lemma sameDom_and_liftAll2_iff:
"(sameDom inp inp' \<and> liftAll2 phi inp inp') = 
 (\<forall> i. (inp i = None \<and> inp' i = None) \<or> 
         (\<exists> v v'. inp i = Some v \<and> inp' i = Some v' \<and> phi v v'))"
proof-
  let ?Left = "sameDom inp inp' \<and> liftAll2 phi inp inp'"
  let ?None = "\<lambda>i. (inp i = None \<and> inp' i = None)"
  let ?Some = "\<lambda>i. (\<exists> v v'. inp i = Some v \<and> inp' i = Some v' \<and> phi v v')"
  {fix i
   assume ?Left and "\<not> ?None i"
   then obtain v v' where "inp i = Some v \<and> inp' i = Some v'"
   unfolding sameDom_def by fastsimp
   hence "?Some i" using `?Left` unfolding liftAll2_def by blast
  }
  moreover
  {
   have "\<forall> i. ?None i \<or> ?Some i \<Longrightarrow> sameDom inp inp'" 
   unfolding sameDom_def by auto
   moreover 
   {fix i A A' assume "inp i = Some A" and "inp' i = Some A'"
    and "?None i \<or> ?Some i"
    hence "phi A A'" by auto
   }
   ultimately have "\<forall> i. ?None i \<or> ?Some i \<Longrightarrow> ?Left" unfolding liftAll2_def by blast
  }
  ultimately show ?thesis by blast
qed



subsection {* Doubly infinitely-branching trees *}

(* These simple infinitary trees shall be used for measuring the sizes 
  of possibly infinitary terms. *)

datatype ('index,'bindex)tree = 
  Branch "('index,('index,'bindex)tree) input" "('bindex,('index,'bindex)tree) input"


(* The natural induction principle for (infinitary) trees:  *)

lemma tree_induct: 
fixes phi::"('index,'bindex)tree \<Rightarrow> bool" and T::"('index,'bindex)tree"
assumes 
  "\<And> inp binp. \<lbrakk>liftAll phi inp; liftAll phi binp\<rbrakk> \<Longrightarrow> phi (Branch inp binp)"
shows "phi T"
proof-
  let ?phio = 
  "\<lambda> To::('index,'bindex)tree option. case To of None \<Rightarrow> True |Some T \<Rightarrow> phi T"
  {fix To 
   have "phi T \<and> ?phio To \<and> ?phio To"
   proof(rule tree.induct, simp_all)
     fix inp::"('index,('index,'bindex)tree)input" 
     and binp::"('bindex,('index,'bindex)tree)input"
     assume *: "\<And>i. ?phio (inp i)" and **:  "\<And>i. ?phio (binp i)"
     have "liftAll phi inp"
     unfolding liftAll_def proof clarify
       fix i T
       assume "inp i = Some T"
       with *[of i] show "phi T" by simp
     qed
     moreover have "liftAll phi binp"
     unfolding liftAll_def proof clarify
       fix i T
       assume "binp i = Some T"
       with **[of i] show "phi T" by simp
     qed
     ultimately show "phi (Branch inp binp)" using assms by simp
  qed
  }
  thus ?thesis by simp
qed


definition treeLess :: "('index,'bindex)tree rel"
where 
"treeLess == 
 {(T,T'). \<exists> inp binp i j. T' = Branch inp binp \<and> (inp i = Some T \<or> binp j = Some T)}"


lemma treeLess_induct:
fixes phi::"('index,'bindex)tree \<Rightarrow> bool" and 
      T::"('index,'bindex)tree"
assumes "\<And> T'. (\<And> T. (T,T') \<in> treeLess \<Longrightarrow> phi T) \<Longrightarrow> phi T'"
shows "phi T"
proof(rule tree_induct)
  fix inp::"('index,('index,'bindex) tree)input" 
  and binp::"('bindex,('index,'bindex)tree)input"
  assume *: "liftAll phi inp" and **: "liftAll phi binp"
  have "\<And> T. (T, Branch inp binp) \<in> treeLess \<Longrightarrow> phi T"
  proof-
    fix T assume "(T, Branch inp binp) \<in> treeLess"
    then obtain i j where "inp i = Some T \<or> binp j = Some T" 
    unfolding treeLess_def by auto
    with * ** show "phi T" unfolding liftAll_def by auto
  qed
  thus "phi (Branch inp binp)" using assms by blast
qed


lemma treeLess_wf: "wf treeLess"
(* this is a mere rephrazing of treeLess_induct  *)
proof(simp only: wf_def, clarify)
  fix phi T
  assume As: "\<forall>T'. (\<forall>T. (T, T') \<in> treeLess \<longrightarrow> phi T) \<longrightarrow> phi T'"
  thus "phi T" using treeLess_induct[of phi T] by blast
qed



subsection {* Facts about order relations *}


lemma Least_Max:
assumes phi: "phi (n::nat)" and fin: "finite {n. phi n}"
shows "(LEAST m. ALL n. phi n \<longrightarrow> n <= m) = 
       Max {n. phi n}"
proof-
  let ?chi = "%m. ALL n. phi n \<longrightarrow> n <= m"
  let ?L = "LEAST m. ?chi m"
  let ?M = "Max {n. phi n}"
  show "?L = ?M"
  proof(rule Least_equality, auto)
    fix n assume "phi n"
    thus "n \<le> Max {n. phi n}"
    using fin Max_ge[of "{n. phi n}"] by simp
  next
    fix y assume "\<forall>n. phi n \<longrightarrow> n \<le> y"
    thus "Max {n. phi n} \<le> y"
    using assms Max_le_iff[of "{n. phi n}" y] by fastsimp
  qed
qed



end

