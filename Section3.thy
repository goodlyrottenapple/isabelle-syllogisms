(*header {* Section 3 --- All, Some, No *}*)

theory Section3
imports Main "~~/src/HOL/Library/Order_Relation"

begin

subsection {* Basic definitions *}

text {* \begin{tcolor} The set of atomic propositions is formalized as a
  type. \end{tcolor} *}
typedecl atProp

text {* The inductively defined set of formulas is formalised as a datatype *}
datatype formula = 
    All atProp atProp ("All _ are _ ") 
  | Some atProp atProp ("Some _ are _") 
  | No atProp atProp ("No _ are _")

text {* The carrier of a model can be any type, written as alpha or 
  @{typ 'a}.
  A model then is a function that assigns to each atomic proposition 
  a subset of @{typ 'a} (its extension, ie, the subset where it is true).*}
type_synonym 'a model = "(atProp \<Rightarrow>'a set)"

text {* \begin{tcolor}The satisfiability relation is formalized as a Boolean valued
  function. The notation (@{text "_ \<Turnstile> _"}) allows us to use the usual
  mathematical notation \begin{qcolor}$M\models\phi$\end{qcolor} in Isabelle.\end{tcolor}*}
fun M_satisfies :: "'a model \<Rightarrow> formula \<Rightarrow> bool" ("_ \<Turnstile> _")
where
   "M_satisfies MM (All x are y) = (MM x \<subseteq> MM y)"
 | "M_satisfies MM (Some x are y) = (\<exists>e. e \<in> MM x \<inter> MM y)"
 | "M_satisfies MM (No x are y) = (MM x \<inter> MM y = {})"

thm M_satisfies.simps

(* model satisfies theory *)
definition M_satisfies_G :: "'a model \<Rightarrow> formula set \<Rightarrow> bool" ("_ \<Turnstile>M _")
where
  "M_satisfies_G M G  \<equiv> \<forall>f. f \<in> G \<longrightarrow> (M \<Turnstile> f)"

(* some useful rewrites for simplification, thanks to Thomas Tuerk *)
lemma M_satisfies_G_I [intro!]:
 "(\<And>f. f \<in> G \<Longrightarrow> M \<Turnstile> f) \<Longrightarrow> (M \<Turnstile>M G)"
unfolding M_satisfies_G_def by auto

lemma M_satisfies_G_rewrites [simp] :
  "(M \<Turnstile>M {})" (is ?g1) (* ak *)
  "(M \<Turnstile>M (insert g G)) \<longleftrightarrow> ((M \<Turnstile> g) \<and> (M \<Turnstile>M G))" (is ?g2)
  "(M \<Turnstile>M (G1 \<union> G2)) \<longleftrightarrow> ((M \<Turnstile>M G1) \<and> (M \<Turnstile>M G2))" (is ?g3)
proof -
  show ?g1 by auto (* thanks to intro-rule above *)
next
  show ?g2 unfolding M_satisfies_G_def by auto
next
  show ?g3 unfolding M_satisfies_G_def by auto
qed

lemma M_satisfies_G_mono :
assumes "G' \<subseteq> G"
    and "M \<Turnstile>M G"
  shows "M \<Turnstile>M G'"
using assms
  by (metis M_satisfies_G_def in_mono)

(* semantic consequence *)
definition G_satisfies :: "formula set \<Rightarrow> formula \<Rightarrow> 'a itself \<Rightarrow> bool" ("_ \<Turnstile>G _ _")
(* TT: use itself types, passing types around (and nothing else) is what they are for) *)
where
  "G_satisfies G f (ty :: 'a itself) \<equiv> \<forall> (M::'a model). (M \<Turnstile>M G) \<longrightarrow> (M \<Turnstile> f)"

lemma G_satisfies_I [intro]:
 "(\<And>(M::'a model). M \<Turnstile>M G \<Longrightarrow> M \<Turnstile> f) \<Longrightarrow> (G \<Turnstile>G f (ty :: 'a itself))"
unfolding G_satisfies_def by auto

(* Example 9 *)
lemma example_9: "{(All p are q), (Some p are r)} \<Turnstile>G (Some q are r) (TYPE (atProp))"
apply (rule G_satisfies_I)
apply (auto)
done

(* Example 10 *)
lemma example_10: "{(All p are v), (All q are w), (No v are w)} \<Turnstile>G (No p are q) (TYPE(atProp))"
apply (rule G_satisfies_I)
apply (auto)
done


(* Figure 3. The logical system for S *)
inductive der :: "formula \<Rightarrow> bool" ("\<turnstile>X _")
  where
    initA: "\<turnstile>X All X are X"
  | initS2: "\<turnstile>X Some X are Y \<Longrightarrow> \<turnstile>X Some X are X"
  | initN: "\<turnstile>X No X are X \<Longrightarrow> \<turnstile>X No X are Y"
  | initN2: "\<turnstile>X No X are X \<Longrightarrow> \<turnstile>X All X are Y"
  | transA: "\<lbrakk>\<turnstile>X All X are Y; \<turnstile>X All Y are Z\<rbrakk> \<Longrightarrow> \<turnstile>X All X are Z"
  | transS: "\<lbrakk>\<turnstile>X All Y are Z; \<turnstile>X Some X are Y\<rbrakk> \<Longrightarrow> \<turnstile>X Some X are Z"
  | transN: "\<lbrakk>\<turnstile>X All X are Y; \<turnstile>X No Y are Z\<rbrakk> \<Longrightarrow> \<turnstile>X No X are Z"
  | reflS: "\<turnstile>X Some X are Y \<Longrightarrow> \<turnstile>X Some Y are X"
  | reflN: "\<turnstile>X No X are Y \<Longrightarrow> \<turnstile>X No Y are X"
  | any: "\<lbrakk>\<turnstile>X Some X are Y; \<turnstile>X No X are Y\<rbrakk>  \<Longrightarrow> \<turnstile>X _"

inductive derarg :: "formula set \<Rightarrow> formula \<Rightarrow> bool" (" _ \<turnstile> _")
  for hs
  where
    initA: "hs \<turnstile> All X are X"
  | initS2: "hs \<turnstile> Some X are Y \<Longrightarrow> hs \<turnstile> Some X are X"
  | initN: "hs \<turnstile> No X are X \<Longrightarrow> hs \<turnstile> No X are Y"
  | initN2: "hs \<turnstile> No X are X \<Longrightarrow> hs \<turnstile> All X are Y"
  | transA: "\<lbrakk>hs \<turnstile> All X are Y; hs \<turnstile> All Y are Z\<rbrakk> \<Longrightarrow> hs \<turnstile> All X are Z"
  | transS: "\<lbrakk>hs \<turnstile> All Y are Z; hs \<turnstile> Some X are Y\<rbrakk> \<Longrightarrow> hs \<turnstile> Some X are Z"
  | transN: "\<lbrakk>hs \<turnstile> All X are Y; hs \<turnstile> No Y are Z\<rbrakk> \<Longrightarrow> hs \<turnstile> No X are Z"
  | reflS: "hs \<turnstile> Some X are Y \<Longrightarrow> hs \<turnstile> Some Y are X"
  | reflN: "hs \<turnstile> No X are Y \<Longrightarrow> hs \<turnstile> No Y are X"
  | any: "\<lbrakk>hs \<turnstile> Some X are Y; hs \<turnstile> No X are Y\<rbrakk>  \<Longrightarrow> hs \<turnstile> _"
  | ass: "f \<in> hs \<Longrightarrow>  hs \<turnstile> f"

(* ak: how to prove this for a generic G? *)
lemma G_derives_mono :
assumes "hs \<turnstile> f"
    and "hs \<subseteq> hs'"
shows "hs' \<turnstile> f"
(* apply (rule derarg.induct)
apply (rule assms)
apply (rule initA)
apply (rule initS2)
ak *)
using assms
proof (induct rule: derarg.induct)
  case (initA X)
  show ?case
  by (rule derarg.initA)
next
  case (initS2 X Y)
  from derarg.initS2[OF initS2(2)] initS2(3)
  show ?case .
next
  case (initN X Y)
  from derarg.initN[OF initN(2)] initN(3)
  show ?case .
next
  case (initN2 X Y)
  from derarg.initN2[OF initN2(2)] initN2(3)
  show ?case .
next
  case (transA X Y Z)
  from derarg.transA[OF transA(2) transA(4)] transA(5)
  show ?case by simp
next
  case(transS X Y Z)
  from derarg.transS[OF transS(2) transS(4)] transS(5)
  show ?case by simp
next
  case(transN X Y Z)
  from derarg.transN[OF transN(2) transN(4)] transN(5)
  show ?case by simp
next
  case(reflS X Y)
  from derarg.reflS[OF reflS(2)] reflS(3)
  show ?case .
next
  case(reflN X Y)
  from derarg.reflN[OF reflN(2)] reflN(3)
  show ?case .
next
  case(any X Y)
  from derarg.any[OF any(2) any(4)] any(5)
  show ?case by simp
next
  case(ass f)
  hence "f \<in> hs'" by auto
  from derarg.ass[OF this]
  show ?case .
print_cases
thm derarg.induct
qed

(* Example 14 *)
lemma example_14 : "{All p are v, All q are w, No v are w} \<turnstile> No p are q" (is "?hs \<turnstile> _")
proof -
  have p1: "?hs \<turnstile> All p are v" by (rule ass, simp)
  have p2: "?hs \<turnstile> All q are w" by (rule ass, simp)
  have p3: "?hs \<turnstile> No v are w" by (rule ass, simp)

  have p4: "?hs \<turnstile> No p are w" using transN [OF p1 p3] .
  have p5: "?hs \<turnstile> No w are p" using reflN [OF p4] .
  have p6: "?hs \<turnstile> No q are p" using transN [OF p2 p5] .
  show ?thesis using reflN [OF p6] .
qed


(* Section 3.3 *)

(* !!! from section 2 !!! *)

(* order induced on atomic propositions by a theory *)
definition less_equal_prop:: 
  "atProp \<Rightarrow> formula set \<Rightarrow> atProp \<Rightarrow> bool" ("_ \<lesssim> _ _")  where
  "less_equal_prop x G y \<equiv> G \<turnstile> All x are y"

(* TT: export the theorems for trans and refl, since they are useful in the following *)
lemma less_equal_prop_refl [simp]:
  "\<And>G x. x \<lesssim>G x"
unfolding less_equal_prop_def 
  by (simp add: derarg.initA)

lemma less_equal_prop_trans:
  "\<And>G x y z. x \<lesssim>G y \<Longrightarrow> y \<lesssim>G z \<Longrightarrow> x \<lesssim>G z"
unfolding less_equal_prop_def 
by (metis derarg.transA)

lemma less_equal_prop_ass [simp] :
  "(All u are v) \<in> G \<Longrightarrow> less_equal_prop u G v"
unfolding less_equal_prop_def by (rule ass) (* ak what does ass refer to ? *)

(* Proposition 2.1 *)
lemma prop_2_1:
  fixes G 
  defines R_def: "R \<equiv> { (x,y). less_equal_prop x G y }"
  shows "preorder_on UNIV R" (* ak explain preorder_on UNIV *)
proof -
  have "refl R"
    by (simp add: refl_on_def R_def)
  have "trans R"
    by (metis assms less_equal_prop_trans mem_Collect_eq old.prod.case trans_converse trans_def)
  with `refl R` show ?thesis by (simp add: preorder_on_def)
qed

(* TT: use top-level pattern matching, since it gives nicer rewrites ak *)

(* the set of all All formulas *)
fun form_all :: "formula \<Rightarrow> bool" where
    "form_all (All _ are _) = True"
  | "form_all _ = False"

lemma form_all_alt_def :
  "form_all f \<longleftrightarrow> (\<exists>p q. (f = All p are q))"
by (cases f) auto

(* the set of all Some formulas *)
fun form_some :: "formula \<Rightarrow> bool" where
    "form_some (Some _ are _) = True"
  | "form_some _ = False"

lemma form_some_alt_def :
  "form_some f \<longleftrightarrow> (\<exists>p q. (f = Some p are q))"
by (cases f) auto

(* the set of all No formulas *)
fun form_no :: "formula \<Rightarrow> bool" where
    "form_no (No _ are _) = True"
  | "form_no _ = False"

lemma form_no_alt_def :
  "form_no f \<longleftrightarrow> (\<exists>p q. (f = No p are q))"
by (cases f) auto

lemma forms_complete :
  "form_all f \<or> form_some f \<or> form_no f"
by (cases f) simp_all

lemma forms_distinct :
  "\<not>(form_all f) \<or> \<not>(form_some f)"
  "\<not>(form_all f) \<or> \<not>(form_no f)"
  "\<not>(form_some f) \<or> \<not>(form_no f)"
by (cases f, simp_all)+


definition "all_formulas = {x. x \<in> (UNIV::formula set) \<and> (form_all x) }"
definition "some_formulas = {x. x \<in> (UNIV::formula set) \<and> (form_some x) }"

(* TT: add useful rewrite early to simplifier *)
lemma in_all_formulas [simp] :
  "f \<in> all_formulas \<longleftrightarrow> form_all f" 
unfolding all_formulas_def by simp

lemma in_some_formulas [simp] :
  "f \<in> some_formulas \<longleftrightarrow> form_some f" 
unfolding some_formulas_def by simp

(* TT: now this is trivial *)

lemma "(All x are y) \<in> all_formulas" by simp
lemma "(No x are y) \<notin> some_formulas" by simp

definition "all_gamma G = G \<inter> all_formulas"
definition "some_gamma G = G \<inter> some_formulas"

definition "all_some_formulas = {x. x \<in> (UNIV::formula set) \<and> (form_all x \<or> form_some x) }"
definition "all_some_gamma G = G \<inter> all_some_formulas"

(* TT: often it is useful to establish connections to existing constructs *)
lemma all_some_formulas_alt_def :
  "all_some_formulas = all_formulas \<union> some_formulas"
unfolding all_some_formulas_def all_formulas_def some_formulas_def by auto

lemma in_all_some_formulas [simp] :
  "f \<in> all_some_formulas \<longleftrightarrow> \<not>(form_no f)"
unfolding all_some_formulas_alt_def
by (cases f) simp_all

lemma all_some_gamma_alt_def :
  "all_some_gamma G = all_gamma G \<union> some_gamma G"
unfolding all_some_gamma_def all_some_formulas_alt_def all_gamma_def some_gamma_def
by auto

(* TT: I prefer this definition, since it introduces less cases and looks clearer.
       Due to less cases better for automation *)

definition char_model_ex6 :: "formula set \<Rightarrow> formula model" ("_ \<lbrakk>_\<rbrakk>") where
  "char_model_ex6 G u = {Some x are y | x y. ((Some x are y) \<in> G) \<and> 
     (less_equal_prop x G u \<or> less_equal_prop y G u)}"
thm char_model_ex6_def

lemma exercise_6_1: 
  fixes G 
  defines "M \<equiv> char_model_ex6 G"
  assumes G_sub: "G \<subseteq> all_some_formulas"
  shows "M \<Turnstile>M G"
proof (rule M_satisfies_G_I)
  fix g
  assume "g \<in> G"
  show "M \<Turnstile> g"
  proof (cases g)
    case (No x y)
    with `g \<in> G` G_sub have False by auto
    thus ?thesis ..
  next
    case (All x y)
    note g_is_All = All
    
    from `g \<in> G` g_is_All
    have "less_equal_prop x G y" 
      by auto
 
    thus ?thesis
      unfolding g_is_All M_def
      by (auto simp add: char_model_ex6_def)
         (metis less_equal_prop_trans)+
  next
    case (Some x y)
    note g_is_Some = Some

    have "g \<in> char_model_ex6 G x" "g \<in> char_model_ex6 G y"
      using `g \<in> G`
      unfolding g_is_Some char_model_ex6_def
      by simp_all
    thus ?thesis
      unfolding M_def g_is_Some
      by simp blast
  qed
qed


lemma exercise_6_2: 
  fixes G
  defines "M \<equiv> char_model_ex6 G"
  assumes G_sub: "G \<subseteq> all_some_formulas"
  assumes M_sat: "M \<Turnstile> Some p are q"
  shows "G \<turnstile> Some p are q"
proof -
  have "\<exists>x y. (Some x are y) \<in> (M p \<inter> M q)"
  proof -
    from M_sat have "M p \<inter> M q \<noteq> {}" by auto
    then obtain e where "e \<in> M p" and "e \<in> M q" by auto

    from `e \<in> M p` have "form_some e"
      unfolding M_def by (auto simp add: char_model_ex6_def)

    from `form_some e` `e \<in> M p` `e \<in> M q`
    show ?thesis unfolding form_some_alt_def by auto
  qed
  then obtain x y where in_Mp: "(Some x are y) \<in> M p" 
                    and in_Mq: "(Some x are y) \<in> M q" by auto

  from in_Mp have in_G: "(Some x are y) \<in> G"
    unfolding M_def char_model_ex6_def by simp

  from in_Mp in_Mq have some_x_y_p_q : "((x \<lesssim>G p) \<or> (y \<lesssim>G p))" "((x \<lesssim>G q) \<or> (y \<lesssim>G q))"
    unfolding M_def char_model_ex6_def by simp_all
  thus ?thesis
    by (metis ass derarg.initS2 derarg.reflS derarg.transS in_G less_equal_prop_def)
qed

(*declare [[show_types]]*)

lemma exercise_7_1: 
  fixes G
  defines "G' \<equiv> G \<inter> all_some_formulas"  
  defines "M \<equiv> char_model_ex6 G'"
  assumes G_sat: "G \<Turnstile>G Some p are q (TYPE(formula))"
  assumes M_sat_G: "M \<Turnstile>M G"
  shows "G \<turnstile> Some p are q"
proof -

  have 1: "G' \<subseteq> all_some_formulas" 
    by (metis G'_def Int_lower2)
 (* have 2: "M \<Turnstile>M G'" 
    by (metis G'_def M_sat_G M_satisfies_G_rewrites(3) sup_inf_absorb)
  *)
  have 2: "M \<Turnstile> Some p are q"
    using G_sat M_sat_G
    unfolding G_satisfies_def
    by simp
 
  from 1 2 have "G' \<turnstile> Some p are q"
    using exercise_6_2[of G'] 
    unfolding M_def
    by metis
  thus ?thesis
    by (metis G'_def G_derives_mono Int_lower1)
qed

lemma exercise_7_2: 
  fixes G
  defines "G' \<equiv> G \<inter> all_some_formulas"  
  defines "M \<equiv> char_model_ex6 G'"
  assumes G_sat: "G \<Turnstile>G Some p are q (TYPE(formula))"
  assumes not_M_sat_G: "\<not>(M \<Turnstile>M G)"
  shows "G \<turnstile> Some p are q"
proof -
  from not_M_sat_G have 1: "\<exists> f \<in> G. \<not>(M \<Turnstile> f)"
    by (metis M_satisfies_G_def)

  then obtain x y where "(No x are y) \<in> G" and  "\<not>(M \<Turnstile> No x are y)"
    by (metis G'_def IntI Int_lower2 M_def M_satisfies_G_def exercise_6_1 form_no.elims(2) in_all_some_formulas)
  
  then have "M x \<inter> M y \<noteq> {}" by simp
  then have "G' \<turnstile> Some x are y"
    using exercise_6_2[of G'] 
    by (metis G'_def IntE M_def M_satisfies.simps(2) ex_in_conv subsetI)
  
  then have "G \<turnstile> Some x are y"
    by (metis G'_def G_derives_mono Int_lower1)
  
  from `(No x are y) \<in> G` have "G \<turnstile> No x are y" by (rule derarg.ass)
  thus ?thesis
    using `G \<turnstile> Some x are y`
    by (metis derarg.any)
qed


definition "no_formulas = {x. x \<in> (UNIV::formula set) \<and> (form_no x) }"

definition "no_gamma G = G \<inter> no_formulas"

definition "all_no_formulas = {x. x \<in> (UNIV::formula set) \<and> (form_all x \<or> form_no x) }"
definition "all_no_gamma G = G \<inter> all_no_formulas"

definition "all_some_no_formulas = {x. x \<in> (UNIV::formula set) \<and> (form_all x \<or> form_some x \<or> form_no x) }"

(* TT: often it is useful to establish connections to existing constructs *)
lemma all_no_formulas_alt_def :
  "all_no_formulas = all_formulas \<union> no_formulas"
unfolding all_no_formulas_def all_formulas_def no_formulas_def by auto

lemma in_all_no_formulas [simp] :
  "f \<in> all_no_formulas \<longleftrightarrow> \<not>(form_some f)"
unfolding all_no_formulas_alt_def
by (metis (lifting) UNIV_I all_no_formulas_alt_def all_no_formulas_def all_some_formulas_def forms_distinct(1) in_all_some_formulas mem_Collect_eq) 

lemma all_no_gamma_alt_def :
  "all_no_gamma G = all_gamma G \<union> no_gamma G"
unfolding all_no_gamma_def all_no_formulas_alt_def all_gamma_def no_gamma_def
by auto




definition up_closed :: "atProp set \<Rightarrow> formula set \<Rightarrow> bool" where
  "up_closed A G \<equiv> \<forall>v \<in> A. \<forall>w. (v \<lesssim>G w) \<longrightarrow> w \<in> A"

definition does_not_derive :: "atProp set \<Rightarrow> formula set \<Rightarrow> bool" where
  "does_not_derive A G \<equiv> \<forall>v \<in> A. \<forall>w \<in> A. \<not>(G \<turnstile> No v are w)"

definition "M_ex7 G \<equiv> {A. A \<subseteq> (UNIV::atProp set) \<and> (up_closed A G) \<and> (does_not_derive A G) }"

definition char_model_ex8 :: "formula set \<Rightarrow> (atProp set) model" where
  "char_model_ex8 G v = { A. A \<in> (M_ex7 G) \<and> v \<in> A }"



lemma exercise_8_1: 
  fixes G 
  defines "M \<equiv> char_model_ex8 G"
  assumes G_sub: "G \<subseteq> all_no_formulas"
  shows "M \<Turnstile>M G"
proof (rule M_satisfies_G_I)
  fix g
  assume "g \<in> G"

  show "M \<Turnstile> g"
  proof (cases g)
    case (Some x y)
    with `g \<in> G` G_sub have False by auto
    thus ?thesis ..
  next
    case (All x y)
    then have "x \<lesssim>G y"
      using `g \<in> G`
      by (metis less_equal_prop_ass)
    then have "M x \<subseteq> M y"
      unfolding M_def char_model_ex8_def M_ex7_def
      by simp (metis (lifting, no_types) Collect_mono up_closed_def)
    thus ?thesis
      by (metis M_satisfies.simps(1) All)
  next  
    case (No x y)
    then have g_derives_n : "G \<turnstile> No x are y" 
      using `g \<in> G`
      by (metis ass)
    {
      fix X 
      assume "X \<in> M x"
      have "X \<notin> M y"
        proof (rule notI)
          assume "X \<in> M y"
          have 1: "x \<in> X"
            by (metis (lifting) M_def `X \<in> M x` char_model_ex8_def mem_Collect_eq)
          have 2: "y \<in> X"
            by (metis (lifting) M_def `X \<in> M y` char_model_ex8_def mem_Collect_eq)
          from 1 2 `X \<in> M x` have "\<not>(G \<turnstile> No x are y)"
            unfolding M_def char_model_ex8_def M_ex7_def does_not_derive_def
            by auto
          then have "X \<notin> M x"
            by (metis g_derives_n)
          with `X \<in> M x` show False by metis
        qed
    }
    hence "M x \<inter> M y = {}" by auto
    thus ?thesis
      by (metis M_satisfies.simps(3) No)
  qed
qed

lemma exercise_8_2: 
  fixes G 
  defines "M \<equiv> char_model_ex8 G"
  assumes G_sub: "G \<subseteq> all_no_formulas"
  assumes g_in_all_no : "g \<in> all_no_formulas"
  and "M \<Turnstile> g"
  shows "G \<turnstile> g"
proof - 
  show ?thesis
  proof (cases g)
    case(Some x y)
    with g_in_all_no have False by simp
    thus ?thesis ..
  next
    case(All x y)
    {
      fix Ax
      def Ax \<equiv> "{ z. x \<lesssim>G z }"

      have ?thesis
      proof (cases "Ax \<in> M_ex7 G")
        case (True)
        have x_in_Ax : "x \<in> Ax"
          by (metis Ax_def less_equal_prop_refl mem_Collect_eq)
        have "M \<Turnstile> All x are y"
          using exercise_8_1[of G]
          by (metis All `M \<Turnstile> g`)
        then have "M x \<subseteq> M y" by simp
        from x_in_Ax `Ax \<in> M_ex7 G` have Ax_in_Mx : "Ax \<in> M x"
          by (metis (lifting) M_def char_model_ex8_def mem_Collect_eq)
        from `M x \<subseteq> M y` Ax_in_Mx have Ax_in_My : "Ax \<in> M y"
          by (metis subsetD)
        from Ax_in_My Ax_def have y_in_Ax : "y \<in> Ax"
          by (metis (lifting) M_def char_model_ex8_def mem_Collect_eq)
        from x_in_Ax y_in_Ax Ax_def have "x \<lesssim>G y"
          by (metis mem_Collect_eq)
        then have A_in_M: "G \<turnstile> All x are y"
          by (metis less_equal_prop_def)
        thus ?thesis by (metis All)
      next
        case (False)
        then have "\<not>(does_not_derive Ax G)"
          by (metis (lifting, no_types) M_ex7_def less_equal_prop_trans mem_Collect_eq Ax_def top_greatest up_closed_def)
        then have "\<exists>v \<in> Ax. \<exists>w \<in> Ax. (G \<turnstile> No v are w)" 
          unfolding M_ex7_def does_not_derive_def
          by simp
        then obtain v w where no_v_w : "(G \<turnstile> No v are w)" by metis
        then have cases_x :"(x \<lesssim>G v)" "(x \<lesssim>G w)"
          by (metis (mono_tags) `\<exists>v\<in>Ax. \<exists>w\<in>Ax. (G \<turnstile> No v are w)` derarg.initN2 derarg.reflN derarg.transN less_equal_prop_def mem_Collect_eq order_refl Ax_def set_rev_mp)+ 
   
        from cases_x(1) have all_x_v : "G \<turnstile> All x are v" by (metis less_equal_prop_def)
        from all_x_v no_v_w have no_x_w : "G \<turnstile> No x are w" by (metis all_x_v derarg.transN)
        from no_x_w cases_x(2) have "G \<turnstile> No x are x" by (metis derarg.reflN derarg.transN less_equal_prop_def)
        then have "G \<turnstile> All x are y" by (rule derarg.initN2)
        thus ?thesis by (metis All)
      qed
    }
    thus ?thesis
      by metis
  next
    case (No x y)
    {
      fix Axy
      def Axy \<equiv> "{ z. (x \<lesssim>G z) \<or> (y \<lesssim>G z) }"
    
      have "Axy \<notin> M_ex7 G"
      proof (rule notI)
        assume "Axy \<in> M_ex7 G"
        from `M \<Turnstile> g` No have "M x \<inter> M y = {}" by simp
        have 1 : "Axy \<in> M x"
          by (metis (lifting, no_types) Axy_def M_def `Axy \<in> M_ex7 G` char_model_ex8_def less_equal_prop_refl mem_Collect_eq)
        have 2 : "Axy \<in> M y"
          by (metis (lifting, no_types) Axy_def M_def `Axy \<in> M_ex7 G` char_model_ex8_def less_equal_prop_refl mem_Collect_eq)
        from 1 2 have "M x \<inter> M y \<noteq> {}" by auto
        with `M x \<inter> M y = {}` show False by simp
      qed
      then have "\<not>(does_not_derive Axy G)"
        by (metis (lifting) Axy_def M_ex7_def less_equal_prop_trans mem_Collect_eq subset_UNIV up_closed_def)
      then have "\<exists>v \<in> Axy. \<exists>w \<in> Axy. (G \<turnstile> No v are w)"
        unfolding M_ex7_def does_not_derive_def
        by simp
      then obtain v w where "G \<turnstile> No v are w" "v \<in> Axy" "w \<in> Axy" by auto
      then have cases : "(x \<lesssim>G v) \<or> (y \<lesssim>G v)" "(x \<lesssim>G w) \<or> (y \<lesssim>G w)"
        by (metis mem_Collect_eq Axy_def)+
    
      note case1_e = disjE[OF cases(1)]
      note case2_e = disjE[OF cases(2)]
      note cases_elim = case1_e[case_product case2_e, case_names 1 2 3 4]
      have ?thesis
      proof (cases rule: cases_elim)
        case 1
        then have "G \<turnstile> All x are v" "G \<turnstile> All x are w" by (metis less_equal_prop_def)+
        with `G \<turnstile> No v are w` have "G \<turnstile> No x are w" by (metis derarg.transN)
        then have "G \<turnstile> No w are x" by (rule derarg.reflN)
        with `G \<turnstile> All x are w` have "G \<turnstile> No x are x" by (rule derarg.transN)
        then have "G \<turnstile> No x are y" by (rule derarg.initN)
        thus ?thesis by (metis No)
      next
        case 2
        then have "G \<turnstile> All x are v" "G \<turnstile> All y are w" by (metis less_equal_prop_def)+
        with `G \<turnstile> No v are w` have "G \<turnstile> No x are w" by (metis derarg.transN)
        then have "G \<turnstile> No w are x" by (rule derarg.reflN)
        with `G \<turnstile> All y are w` have "G \<turnstile> No x are y" by (metis derarg.reflN derarg.transN)
        thus ?thesis by (metis No)
      next
        case 3
        then have "G \<turnstile> All y are v" "G \<turnstile> All x are w" by (metis less_equal_prop_def)+
        with `G \<turnstile> No v are w` have "G \<turnstile> No y are w" by (metis derarg.transN)
        then have "G \<turnstile> No w are y" by (rule derarg.reflN)
        with `G \<turnstile> All x are w` have "G \<turnstile> No x are y" by (metis derarg.transN)
        thus ?thesis by (metis No)
      next
        case 4
        then have "G \<turnstile> All y are v" "G \<turnstile> All y are w" by (metis less_equal_prop_def)+
        with `G \<turnstile> No v are w` have "G \<turnstile> No y are w" by (metis derarg.transN)
        then have "G \<turnstile> No w are y" by (rule derarg.reflN)
        with `G \<turnstile> All y are w` have "G \<turnstile> No y are y" by (rule derarg.transN)
        then have "G \<turnstile> No x are y" by (metis derarg.initN derarg.reflN)
        thus ?thesis by (metis No)
      qed
    }
    thus ?thesis by metis
  qed
qed


lemma a :"(A::formula set) \<inter> all_some_no_formulas \<equiv> A"
proof -
  have "\<forall>a \<in> A. a \<in> all_some_no_formulas"
    by (metis (lifting) UNIV_I all_some_no_formulas_def forms_complete mem_Collect_eq)
  then have "A \<subseteq> {x \<in> UNIV. form_all x \<or> form_some x \<or> form_no x}"
    by (metis all_some_no_formulas_def subsetI)
  then have "A = A \<inter> {x \<in> UNIV. form_all x \<or> form_some x \<or> form_no x}"
    by (metis eq_iff inf.bounded_iff inf.cobounded1 subset_refl)
  then show "(A::formula set) \<inter> all_some_no_formulas \<equiv> A"
    unfolding all_some_no_formulas_def by auto
qed

lemma intersect:
  fixes G
  defines "Gall_no \<equiv> G \<inter> all_no_formulas"
    and "Gsome \<equiv> G \<inter> some_formulas"
    shows "G = Gall_no \<union> Gsome"
proof (simp add:Gall_no_def all_no_formulas_def Gsome_def some_formulas_def)
  have 1: "G \<inter> ({x. form_all x \<or> form_no x} \<union> {x. form_some x}) = G \<inter> {x. form_all x \<or> form_no x} \<union> G \<inter> {x. form_some x}"
    by auto 
  have 2: "({x. form_all x \<or> form_no x} \<union> {x. form_some x}) = all_some_no_formulas"
  proof -
    have "Collect form_all \<union> (Collect form_some \<union> Collect form_no) = all_some_no_formulas"
      using all_some_no_formulas_def by auto
    thus "{x. form_all x \<or> form_no x} \<union> {x. form_some x} = all_some_no_formulas"
      by (metis Collect_disj_eq sup_commute sup_left_commute)
  qed
  have "G \<inter> all_some_no_formulas = G \<inter> {x. form_all x \<or> form_no x} \<union> G \<inter> {x. form_some x}"
    by (metis "1" "2" Collect_disj_eq a)
  then have "G = G \<inter> {x. form_all x \<or> form_no x} \<union> G \<inter> {x. form_some x}"
    by (metis a)
  then show "G = G \<inter> {x. form_all x \<or> form_no x} \<union> G \<inter> {x. form_some x}" by fast
qed

theorem exercise_9: 
  fixes G
  assumes G_sat1 : "G \<Turnstile>G g TYPE(formula)"
      and G_sat2 : "G \<Turnstile>G g TYPE((atProp set))"
  shows "G \<turnstile> g"
proof -
  have all_no_form_der_g : "g \<in> all_no_formulas \<Longrightarrow> G \<turnstile> g"
  proof -
    assume "g \<in> all_no_formulas"
    def G' \<equiv> "G \<inter> all_no_formulas"
    def M \<equiv> "char_model_ex8 G'"
    def Gsome \<equiv> "G \<inter> some_formulas"

    show ?thesis
    proof (cases "M \<Turnstile>M Gsome")
      case(True)
      have "G' \<subseteq> all_no_formulas"
        by (metis G'_def Int_lower2)
      have M_sat_G': "M \<Turnstile>M G'" 
        by (metis G'_def M_def exercise_8_1 inf.cobounded1 inf_commute)
      have "G' \<union> Gsome = G" 
        by (metis G'_def Gsome_def intersect)
      with M_sat_G' have M_sat_G : "M \<Turnstile>M G"
        by (metis M_satisfies_G_rewrites(3) True)
      then have "M \<Turnstile> g"
        by (metis G_satisfies_def G_sat2)   
      then have "G' \<turnstile> g"
        using exercise_8_2[of G' g]
        by (metis M_def `g \<in> all_no_formulas` `G' \<subseteq> all_no_formulas`)
      then show ?thesis
        by (metis G'_def G_derives_mono inf.cobounded2 inf_commute)
    next
      case (False)
      then have "\<not>(M \<Turnstile>M G)"
        by (metis Gsome_def M_satisfies_G_rewrites(3) sup_inf_absorb)
      have "G' \<subseteq> all_no_formulas"
        by (metis G'_def Int_lower2)
      from False have 1: "\<exists>f \<in> Gsome. \<not>(M \<Turnstile> f)" by fast
      obtain f where dNd : "f \<in> Gsome" "\<not>(M \<Turnstile> f)"
        by (metis "1")
      obtain x y where Sxy : "f = Some x are y"
        by (metis Gsome_def Int_iff dNd(1) form_some.elims(2) in_some_formulas)
      from dNd have dNdSxy: "\<not>(M \<Turnstile> Some x are y)"
        by (metis Sxy)
      from dNdSxy have "M x \<inter> M y = {}" by auto
      then obtain f' where derNxy : "M \<Turnstile> f'" "f' = No x are y" by (metis M_satisfies.simps(3))
      have "f' \<in> all_no_formulas"
        by (metis derNxy(2) form_some.simps(3) in_all_no_formulas)
      then have "G' \<turnstile> f'"
        using exercise_8_2[of G' f']
        by (metis M_def `G' \<subseteq> all_no_formulas` derNxy(1))
      then have "G \<turnstile> No x are y" by (metis G'_def G_derives_mono Int_lower1 derNxy(2))
      have "G \<turnstile> Some x are y" by (metis Gsome_def IntE Sxy ass dNd(1))
      with `G \<turnstile> No x are y` show ?thesis by (metis derarg.any)
    qed
  qed

  show ?thesis
  proof (cases g)
    case (Some x y)
    show ?thesis
     by (metis G_sat1 Some exercise_7_1 exercise_7_2)
  next
    case (All x y)
    have "g \<in> all_no_formulas"
     by (metis All form_some.simps(2) in_all_no_formulas)
    with all_no_form_der_g show ?thesis by auto
  next
    case (No x y)
    have "g \<in> all_no_formulas"
     by (metis No form_some.simps(3) in_all_no_formulas)
    with all_no_form_der_g show ?thesis by auto
  qed
qed

end
