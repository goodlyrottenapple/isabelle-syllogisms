theory Section4
imports Main "~~/src/HOL/Library/Order_Relation" "~~/src/HOL/Library/Zorn"

begin

(* Section 4.1 *)

typedecl p

datatype Lit = P p ("_." 500) | Not p ("_`")

fun complement :: "Lit \<Rightarrow> Lit" ("_\<acute>" 300) where
  "(p`)\<acute> = (p.)"
| "(p.)\<acute> = (p`)"

datatype formula = All Lit Lit ("All _ are _ ") | Some Lit Lit ("Some _ are _") 

lemma "(p.)\<acute> = (p`)" by (rule complement.simps(2))

lemma complement_involutive[simp] : "x\<acute>\<acute> = x"
  by (metis Lit.exhaust complement.simps(1) complement.simps(2))
(*declare [[show_types]]*)


type_synonym 'a model = "p \<Rightarrow>'a set"

fun modelOnLit :: "'a model \<Rightarrow> Lit \<Rightarrow>'a set" where
  "modelOnLit M (x`) = (UNIV::'a set) - M (x)"
 |"modelOnLit M (x.) = M (x)"


fun M_satisfies :: "'a model \<Rightarrow> formula \<Rightarrow> bool" ("_ \<Turnstile> _")
where
  "M_satisfies M (All x are y) = (modelOnLit M x \<subseteq> modelOnLit M y)"
| "M_satisfies M (Some x are y) = (\<exists>e. e \<in> modelOnLit M x \<inter> modelOnLit M y)"



lemma 
 assumes "M \<Turnstile> All (p.) are (q`)"
 shows "M p \<inter> M q = {}" (* eqivalent to saying M \<Turnstile> No p are q *)
proof -
  from assms have "M p \<subseteq> modelOnLit M (q`)"
    by simp
  then have "M p \<subseteq> ( UNIV - M q )"
    by simp
  then show ?thesis by auto
qed

inductive derarg :: "formula set \<Rightarrow> formula \<Rightarrow> bool" ("_ \<turnstile> _")
  for hs
  where
  axiom: "hs \<turnstile> All X are X"
| some1: "hs \<turnstile> Some X are Y \<Longrightarrow> hs \<turnstile> Some X are X"
| some2: "hs \<turnstile> Some X are Y \<Longrightarrow> hs \<turnstile> Some Y are X"
| barbara: "\<lbrakk>hs \<turnstile> All X are Y; hs \<turnstile> All Y are Z\<rbrakk> \<Longrightarrow> hs \<turnstile> All X are Z"
| darii: "\<lbrakk>hs \<turnstile> All Y are Z; hs \<turnstile> Some X are Y\<rbrakk> \<Longrightarrow> hs \<turnstile> Some X are Z"
| zero: "hs \<turnstile> All X  are (X\<acute>) \<Longrightarrow> hs \<turnstile> All X are Y"
| one: "hs \<turnstile> All (Y\<acute>) are Y \<Longrightarrow> hs \<turnstile> All X are Y"
| antitone: "hs \<turnstile> All Y are (X\<acute>) \<Longrightarrow> hs \<turnstile> All X are (Y\<acute>)"
| x: "\<lbrakk>hs \<turnstile> All X are Y; hs \<turnstile> Some X are (Y\<acute>)\<rbrakk> \<Longrightarrow> hs \<turnstile> _"
| ass: "f \<in> hs \<Longrightarrow> hs \<turnstile> f"

lemma "{Some (p`) are (q.)} \<turnstile> Some (q.) are (q.)"
proof -
  have "{Some (p`) are (q.)} \<turnstile> Some (q.) are (p`)" by (simp add: ass derarg.some2)
  then show ?thesis by (simp add: derarg.some1)
qed



(* section 4.2 *)  


(* preorder on Lit induced by set of formulas G *)
fun less_equal_Lit :: "Lit \<Rightarrow> formula set \<Rightarrow> Lit \<Rightarrow> bool" ("_ \<lesssim> _ _")  where
  "less_equal_Lit x G y = (G \<turnstile> All x are y)"


(* TT: export the theorems for trans and refl, since they are useful in the following *)
lemma less_equal_Lit_refl [simp]:
  "\<And>x G. x \<lesssim>G x"
  by (metis axiom less_equal_Lit.elims(3))

lemma less_equal_Lit_trans:
  "\<And>x G y z. x \<lesssim>G y \<Longrightarrow> y \<lesssim>G z \<Longrightarrow> x \<lesssim>G z"
  by (metis barbara less_equal_Lit.simps(1))

lemma less_equal_Lit_ass [simp] :
  "(All x are y) \<in> G \<Longrightarrow> less_equal_Lit x G y"
  by (metis ass less_equal_Lit.simps(1))

lemma less_equal_Lit_antitone :
  "\<And>G x y. (x \<lesssim>G y) \<longleftrightarrow> ((y\<acute>) \<lesssim>G (x\<acute>))"
by (metis antitone complement_involutive less_equal_Lit.simps)


lemma prop_2_1:
  fixes G 
  defines R_def: "R \<equiv> { (x, y). less_equal_Lit x G y }"
  shows "preorder_on UNIV R"
proof -
  have "refl R"
    by (simp add: refl_on_def R_def) (metis axiom)
  have "trans R"
    by (metis (full_types) assms less_equal_Lit_trans mem_Collect_eq prod_caseI split_conv transI)
  with `refl R` show ?thesis by (simp add: preorder_on_def)
qed

(* equivalence relation induced by the preorder *)
(* should we rename equiv_Lit to equal_Lit? - cant there is an automatically generated definition called equal_Lit *)
definition equiv_Lit :: "Lit \<Rightarrow> formula set \<Rightarrow> Lit \<Rightarrow> bool" ("_ \<approx>_ _")  where
  "equiv_Lit x G y \<equiv> less_equal_Lit x G y \<and> less_equal_Lit y G x"
  

lemma equiv_Lit_refl [simp]:
  "\<And>G x. x \<approx>G x"
unfolding equiv_Lit_def by (metis less_equal_Lit_refl)

lemma equiv_Lit_antitone:
  "\<And>G x y. (x \<approx>G y) \<longleftrightarrow> ((x\<acute>) \<approx>G (y\<acute>))"
by (metis antitone complement_involutive equiv_Lit_def less_equal_Lit.simps)



definition Lit_poset_eqclass :: "Lit \<Rightarrow> formula set \<Rightarrow> Lit set" ("[[_]]_") where
  "Lit_poset_eqclass x G \<equiv> {y. x \<approx>G y}"

lemma Lit_poset_eqclass_membership : "\<And>x G. x \<in> [[x]]G"
  unfolding Lit_poset_eqclass_def by (metis equiv_Lit_refl mem_Collect_eq)

lemma Lit_poset_eqclass_equivalence [simp]: "\<And>x G y. x \<approx>G y \<Longrightarrow> ([[x]]G) = ([[y]]G)"
  unfolding Lit_poset_eqclass_def equiv_Lit_def
  by (metis less_equal_Lit_trans)


datatype lit_mod_elt = Zero_rep | One_rep | Equiv "Lit set"

definition Lit_mod :: "formula set \<Rightarrow> lit_mod_elt set" where
   "Lit_mod G = { Equiv ([[x]]G) | x. x \<in> UNIV }"

definition Lit_mod_plus_cond :: "formula set => bool" where
  "Lit_mod_plus_cond G \<equiv> \<exists> p. (p \<lesssim>G (p\<acute>))"

definition Lit_mod_plus :: "formula set \<Rightarrow> lit_mod_elt set" where
  "Lit_mod_plus G \<equiv> if Lit_mod_plus_cond G then Lit_mod G else
  ((Lit_mod G) \<union> {Zero_rep, One_rep})"

definition zero :: "formula set \<Rightarrow> lit_mod_elt" where
  "zero G \<equiv> if Lit_mod_plus_cond G then Equiv([[SOME p. (p \<lesssim>G (p\<acute>))]]G) else Zero_rep"


lemma Lit_mod_intro[simp] : "\<And>x. ( Equiv [[x]]G) \<in> Lit_mod G"
unfolding Lit_mod_def
by (metis (lifting, mono_tags) UNIV_I mem_Collect_eq)


lemma Lit_mod_plus_intro[simp] : "\<And>x. ( Equiv [[x]]G) \<in> Lit_mod_plus G"
unfolding Lit_mod_plus_def by fastforce


lemma Lit_mod_intro2[simp] : "\<And>x. x \<in> Lit_mod G \<Longrightarrow> \<exists>y. x = (Equiv [[y]]G)"
unfolding Lit_mod_def
proof -
  fix x
  assume "x \<in> {(Equiv [[x]]G) |x. x \<in> UNIV}"
  hence "\<exists>xa. x = (Equiv [[xa]]G) \<and> xa \<in> UNIV"
    by fastforce
  thus "\<exists>y. x = (Equiv [[y]]G)"
    by simp
qed

fun less_equal_Lit_poset_eqclass :: "lit_mod_elt \<Rightarrow> formula set \<Rightarrow> lit_mod_elt \<Rightarrow> bool" ("_ \<lesssim>._ _" 400) where
  "less_equal_Lit_poset_eqclass (Equiv a) G (Equiv b) = (\<exists>aa \<in> a. \<exists>bb \<in> b. (aa \<lesssim>G bb))"
  | "less_equal_Lit_poset_eqclass Zero_rep G _ = True"
  | "less_equal_Lit_poset_eqclass _ G One_rep = True"
  | "less_equal_Lit_poset_eqclass One_rep G _ = False"
  | "less_equal_Lit_poset_eqclass _ G Zero_rep = False"

lemma less_equal_Lit_poset_eqclass_simp[simp] : 
  "(a \<lesssim>G b) \<longleftrightarrow> (Equiv ([[a]]G) \<lesssim>.G (Equiv [[b]]G))"
proof -
  {
    assume "a \<lesssim>G b"
    have "Equiv ([[a]]G) \<lesssim>.G (Equiv [[b]]G)"
      by (metis Lit_poset_eqclass_membership `a \<lesssim> G b` less_equal_Lit_poset_eqclass.simps(1))
  }
  {
    assume "Equiv ([[a]]G) \<lesssim>.G (Equiv [[b]]G)"
    have 1: "\<exists>aa \<in> ([[a]]G). \<exists>bb \<in> ([[b]]G). (aa \<lesssim>G bb)"
      by (metis `(Equiv [[a]]G) \<lesssim>.G (Equiv [[b]]G)` less_equal_Lit_poset_eqclass.simps(1))
    have "\<forall>x \<in> ([[a]]G). (a \<lesssim>G x)" "\<forall>y \<in> ([[b]]G). (b \<lesssim>G y)"
      by (metis Lit_poset_eqclass_def equiv_Lit_def mem_Collect_eq)+
    with 1 have "a \<lesssim>G b"
      by (metis Lit_poset_eqclass_def equiv_Lit_def less_equal_Lit_trans mem_Collect_eq)
  }
  thus ?thesis
    by (metis `a \<lesssim> G b \<Longrightarrow> (Equiv [[a]]G) \<lesssim>.G (Equiv [[b]]G)`)
qed


lemma less_equal_Lit_poset_eqclass_simp2[simp] : 
  "\<And>x G. (Equiv [[x]]G) \<lesssim>.G (Equiv [[x]]G)"
unfolding Lit_poset_eqclass_def
by (metis equiv_Lit_def equiv_Lit_refl less_equal_Lit_poset_eqclass.simps(1) mem_Collect_eq)

lemma zero_less_equal_Lit_poset_eqclass:
  fixes G p
  assumes "p \<lesssim>G (p\<acute>)"
  shows "\<forall>q. ((Equiv [[p]]G) \<lesssim>.G (Equiv [[q]]G))"
proof -
  from assms have "\<forall>q. (p \<lesssim>G q)"
    by (metis less_equal_Lit.simps zero)
  then show ?thesis by (metis less_equal_Lit_poset_eqclass_simp)
qed

lemma 10[simp]:
  fixes G x a
  assumes "(Equiv x) \<in> Lit_mod_plus G"
  and "a \<in> x"
  shows "(Equiv [[a]]G) = (Equiv x)"
proof -
  from assms(1) have "\<exists>a. (Equiv x) = (Equiv [[a]]G)"
    by (metis Lit_mod_intro2 Lit_mod_plus_def UnE insertE lit_mod_elt.distinct(3) lit_mod_elt.distinct(5) singleton_iff)
  {
    fix l
    assume "x \<equiv> [[l]]G"
    have "a \<approx>G l"
      by (metis Lit_poset_eqclass_def `x \<equiv> [[l]]G` assms(2) equiv_Lit_def mem_Collect_eq)
    have ?thesis
      by (metis Lit_poset_eqclass_equivalence `a \<approx> G l` `x \<equiv> [[l]]G`)
  }
  thus ?thesis
    by (metis `\<exists>a. Equiv x = Equiv [[a]]G` lit_mod_elt.inject)
qed

(*lemma 11:
  fixes G l
  defines "a \<equiv> ([[l]]G)"
  shows "a = \<Union>{ ([[y]]G) | y. y \<in> a }"
proof -
  have 1: "\<forall>x \<in> a. ([[x]]G) = a"
    by (metis Lit_poset_eqclass_def Lit_poset_eqclass_equivalence assms mem_Collect_eq)
  then have "\<Union>{ ([[y]]G) | y. y \<in> a } \<subseteq> a" by fast
  with 1 assms show ?thesis 
    by (metis (lifting, mono_tags) Union_upper mem_Collect_eq subsetI subset_antisym)
qed
*)
(*lemma
  fixes G l x
  defines "a \<equiv> (Lit_poset_eqclass G l)"
  assumes "x \<in> a"
  shows "(Lit_poset_eqclass x G) = \<Union>{ (Lit_poset_eqclass G y) | y. y \<in> a }"
using 10[of x G l]
using 11[of G l]
by (metis assms)*)

fun complement_Lit_poset_eqclass :: "lit_mod_elt \<Rightarrow> formula set \<Rightarrow> lit_mod_elt" (infix ".\<acute>" 400)  where 
  "(Equiv a).\<acute>G = Equiv([[(SOME p. (p \<in> a))\<acute>]]G)"
  | "Zero_rep.\<acute>G = One_rep"
  | "One_rep.\<acute>G = Zero_rep"

definition one :: "formula set \<Rightarrow> lit_mod_elt" where
  "one G \<equiv> zero G .\<acute>G"

lemma complement_Lit_poset_eqclass_equivalence:
  fixes G x a b
  assumes "(Equiv x) \<in> Lit_mod_plus G"
  and "a \<in> x"
  and "b \<in> x"
  shows "(Equiv [[a\<acute>]]G) = (Equiv [[b\<acute>]]G)"
proof -
  have "a \<approx>G b"
    by (metis "10" Lit_poset_eqclass_def assms(1) assms(2) assms(3) lit_mod_elt.inject mem_Collect_eq)
  then have "(a\<acute>) \<approx>G (b\<acute>)" by (metis equiv_Lit_antitone)
  thus ?thesis by force
qed

lemma complement_Lit_poset_eqclass_simp: 
  fixes G x a
  assumes "(Equiv x) \<in> Lit_mod_plus G"
  and "a \<in> x"
  shows "(Equiv [[a\<acute>]]G) = (Equiv x).\<acute>G"
by (metis (lifting) assms(1) assms(2) complement_Lit_poset_eqclass.simps(1) complement_Lit_poset_eqclass_equivalence someI)  


lemma complement_Lit_poset_eqclass_simp2 [simp]: "\<And>x G. Equiv [[x\<acute>]]G \<equiv> (Equiv [[x]]G).\<acute>G"
proof -
  fix x :: Lit and G :: "formula set"
  have "(Equiv [[x]]G).\<acute>G = Equiv [[(x\<acute>)]]G"
    by (metis Lit_mod_intro Lit_mod_plus_def Lit_poset_eqclass_def UnI1 complement_Lit_poset_eqclass_simp equiv_Lit_refl mem_Collect_eq)
  thus "(Equiv [[x\<acute>]]G) \<equiv> (Equiv [[x]]G).\<acute>G"
    using Lit_poset_eqclass_def by simp
qed

lemma Lit_poset_eqclass_reflexive:
  fixes G x
  assumes "x \<in> Lit_mod_plus G"
  shows "x \<lesssim>.G x"
proof (cases x)
  case Zero_rep
  thus ?thesis by simp
next
  case One_rep
  thus ?thesis by simp
next
  case Equiv
  obtain y where "x \<equiv> Equiv y" by (metis Equiv)
  have 1: "\<forall>a \<in> y. (Equiv [[a]]G) = x" by (metis "10" `x \<equiv> Equiv y` assms)
  have "\<forall>a \<in> y. (a \<lesssim>G a)" by (metis less_equal_Lit_refl)
  then have "\<forall>a \<in> y. ((Equiv [[a]]G) \<lesssim>.G (Equiv [[a]]G))" by (metis less_equal_Lit_poset_eqclass_simp2)
  obtain a where "(Equiv [[a]]G) = x" "((Equiv [[a]]G) \<lesssim>.G (Equiv [[a]]G))"
    by (metis Equiv Lit_mod_intro2 Lit_mod_plus_def Un_insert_right assms insert_iff less_equal_Lit_poset_eqclass_simp2 lit_mod_elt.distinct(3) lit_mod_elt.distinct(5) sup_bot_right)
  thus ?thesis by fast
qed

lemma Lit_poset_eqclass_trans:
  fixes G x y z
  assumes "x \<in> Lit_mod_plus G"
  and "y \<in> Lit_mod_plus G"
  and "z \<in> Lit_mod_plus G"
  and "(x \<lesssim>.G y)"
  and "(y \<lesssim>.G z)"
  shows "(x \<lesssim>.G z)"
proof (cases x)
  case Zero_rep
  thus ?thesis by simp
next
  case One_rep
  thus ?thesis
    by (metis assms(4) assms(5) less_equal_Lit_poset_eqclass.elims(2) lit_mod_elt.distinct(1) lit_mod_elt.distinct(5))
next
  case Equiv
  note Equiv_x = Equiv
  thus ?thesis
  proof (cases y)
    case Zero_rep
    have False by (metis Equiv Zero_rep assms(4) less_equal_Lit_poset_eqclass.simps(7))
    thus ?thesis ..
  next
    case One_rep
    thus ?thesis
      by (metis Equiv assms(5) less_equal_Lit_poset_eqclass.simps(4) less_equal_Lit_poset_eqclass.simps(5) less_equal_Lit_poset_eqclass.simps(6) lit_mod_elt.exhaust)
  next
    case Equiv
    note Equiv_y = Equiv
    thus ?thesis
    proof (cases z)
      case Zero_rep
      have False by (metis Equiv_y Zero_rep assms(5) less_equal_Lit_poset_eqclass.simps(7))
      thus ?thesis ..
    next
      case One_rep
      thus ?thesis by (metis Equiv_x less_equal_Lit_poset_eqclass.simps(4))
    next
      case Equiv
      note Equiv_z = Equiv
      obtain e f g where "x \<equiv> Equiv e" "y \<equiv> Equiv f" "z \<equiv> Equiv g"
        by (metis Equiv_x Equiv_y Equiv_z)
      then have 1 : "\<forall>a \<in> e. \<forall>b \<in> f. (a \<lesssim>G b)"
      proof -
        obtain a b where "a \<in> e" "b \<in> f"
          by (metis `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(4) less_equal_Lit_poset_eqclass.simps(1))
        then have "Equiv ([[a]]G) = x" "Equiv ([[b]]G) = y"
          by (metis "10" `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(1)) (metis "10" `b \<in> f` `y \<equiv> Equiv f` assms(2))
        then have "(Equiv ([[a]]G)) \<lesssim>.G (Equiv ([[b]]G))" by (metis assms(4))
        then have  "a \<lesssim>G b" by (metis less_equal_Lit_poset_eqclass_simp)
        thus ?thesis by (metis Lit_poset_eqclass_def Lit_poset_eqclass_equivalence `x \<equiv> Equiv e` `y \<equiv> Equiv f` `(Equiv [[a]]G) = x` `(Equiv [[b]]G) = y` less_equal_Lit_poset_eqclass_simp lit_mod_elt.inject mem_Collect_eq)
      qed
      have 2 : "\<forall>a \<in> f. \<forall>b \<in> g. (a \<lesssim>G b)"
      proof -
        obtain b c where "b \<in> f" "c \<in> g"
          by (metis `z \<equiv> Equiv g` `y \<equiv> Equiv f` assms(5) less_equal_Lit_poset_eqclass.simps(1))
        then have "Equiv ([[b]]G) = y" "Equiv ([[c]]G) = z" 
          by (metis "10" `y \<equiv> Equiv f` assms(2)) (metis "10" `c \<in> g` `z \<equiv> Equiv g` assms(3))
        then have "(Equiv ([[b]]G)) \<lesssim>.G (Equiv ([[c]]G))" by (metis assms(5))
        then have  "b \<lesssim>G c" by (metis less_equal_Lit_poset_eqclass_simp)
        thus ?thesis by (metis Lit_poset_eqclass_def Lit_poset_eqclass_equivalence `y \<equiv> Equiv f` `z \<equiv> Equiv g` `(Equiv [[b]]G) = y` `(Equiv [[c]]G) = z` assms(5) less_equal_Lit_poset_eqclass_simp lit_mod_elt.inject mem_Collect_eq)
      qed

      from 1 2 have "\<forall>a \<in> e. \<forall>b \<in> g. (a \<lesssim>G b)" 
        by (metis `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(4) ex_in_conv less_equal_Lit_poset_eqclass.simps(1) less_equal_Lit_trans)
      thus ?thesis
        by (metis `x \<equiv> Equiv e` `y \<equiv> Equiv f` `z \<equiv> Equiv g` assms(4) assms(5) less_equal_Lit_poset_eqclass.simps(1))
    qed
  qed
qed

lemma Lit_poset_eqclass_antisym:
  fixes G x y
  assumes "x \<in> Lit_mod_plus G"
  and "y \<in> Lit_mod_plus G"
  and "(x \<lesssim>.G y)"
  and "(y \<lesssim>.G x)"
  shows "x = y"
proof (cases x)
  case Zero_rep
  thus ?thesis by (metis assms(4) less_equal_Lit_poset_eqclass.simps(5) less_equal_Lit_poset_eqclass.simps(7) lit_mod_elt.exhaust)
next
  case One_rep
  thus ?thesis by (metis assms(3) less_equal_Lit_poset_eqclass.simps(5) less_equal_Lit_poset_eqclass.simps(6) lit_mod_elt.exhaust)
next
  case Equiv
  note Equiv_x = Equiv
  thus ?thesis
  proof (cases y)
    case Zero_rep
    thus ?thesis by (metis Equiv_x assms(3) less_equal_Lit_poset_eqclass.simps(7))
  next
    case One_rep
    thus ?thesis by (metis Equiv_x assms(4) less_equal_Lit_poset_eqclass.simps(6))
  next
    case Equiv
    note Equiv_y = Equiv
    obtain e f where "x \<equiv> Equiv e" "y \<equiv> Equiv f" by (metis Equiv_x Equiv_y)
    have 1 : "\<forall>a \<in> e. \<forall>b \<in> f. (a \<lesssim>G b)"
      by (metis "10" `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(1) assms(2) assms(3) less_equal_Lit_poset_eqclass_simp lit_mod_elt.inject)

    have 2 : "\<forall>a \<in> f. \<forall>b \<in> e. (a \<lesssim>G b)"
      by (metis "10" `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(1) assms(2) assms(4) less_equal_Lit_poset_eqclass_simp lit_mod_elt.inject)
  
    from 1 2 have "\<forall>a \<in> e. \<forall>b \<in> f. (a \<approx>G b)" by (metis equiv_Lit_def)
    then have "\<forall>a \<in> e. \<forall>b \<in> f. (Equiv [[a]]G) = (Equiv [[b]]G)" by force
    thus ?thesis 
      by (metis "10" `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(1) assms(2) assms(3) less_equal_Lit_poset_eqclass.elims(2) lit_mod_elt.distinct(3) lit_mod_elt.distinct(5) lit_mod_elt.inject)
  qed
qed


lemma Lit_eqclass_partial_order:
  fixes G 
  defines R_def: "R \<equiv> { (x, y). x \<in> Lit_mod_plus G \<and> y \<in> Lit_mod_plus G \<and> (x \<lesssim>.G y) }"
  shows "partial_order_on (Lit_mod_plus G) R"
proof -
  have "refl_on (Lit_mod_plus G) R"
    unfolding refl_on_def
    by (metis (lifting) Lit_poset_eqclass_reflexive SigmaI assms mem_Collect_eq split_conv subrelI)

  have "trans R"
    unfolding trans_def
    by (metis (lifting, mono_tags) Lit_poset_eqclass_trans assms curryD curryI curry_split mem_Collect_eq)

  have "antisym R"
    unfolding antisym_def
      by (metis (lifting) Lit_poset_eqclass_antisym assms mem_Collect_eq split_conv)
  
  with `refl_on (Lit_mod_plus G) R` `trans R` show ?thesis by (metis partial_order_on_def preorder_on_def)
qed


lemma Lit_eqclass_antitone :
  fixes G x y
  assumes "x \<in> Lit_mod_plus G"
  and "y \<in> Lit_mod_plus G"
  shows "(x \<lesssim>.G y) \<longleftrightarrow> ((y.\<acute>G) \<lesssim>.G (x.\<acute>G))"
proof (cases x)
  case Zero_rep
  thus ?thesis by (metis complement_Lit_poset_eqclass.simps(2) less_equal_Lit_poset_eqclass.elims(3) less_equal_Lit_poset_eqclass.simps(2) less_equal_Lit_poset_eqclass.simps(3) less_equal_Lit_poset_eqclass.simps(4) lit_mod_elt.distinct(1))
next
  case One_rep
  thus ?thesis by (metis complement_Lit_poset_eqclass.simps(1) complement_Lit_poset_eqclass.simps(2) complement_Lit_poset_eqclass.simps(3) less_equal_Lit_poset_eqclass.elims(2) less_equal_Lit_poset_eqclass.elims(3) lit_mod_elt.distinct(1) lit_mod_elt.distinct(5))
next
  case Equiv
  note Equiv_x = Equiv
  thus ?thesis
  proof (cases y)
    case Zero_rep
    thus ?thesis by (metis Equiv_x complement_Lit_poset_eqclass.simps(1) complement_Lit_poset_eqclass.simps(2) less_equal_Lit_poset_eqclass.elims(2) less_equal_Lit_poset_eqclass.simps(7) lit_mod_elt.distinct(1) lit_mod_elt.distinct(5))
  next
    case One_rep
    thus ?thesis by (metis Equiv_x complement_Lit_poset_eqclass.simps(3) less_equal_Lit_poset_eqclass.simps(2) less_equal_Lit_poset_eqclass.simps(4))
  next
    case Equiv
    note Equiv_y = Equiv

    obtain e f where "x \<equiv> Equiv e" "y \<equiv> Equiv f" 
      by (metis Equiv_x Equiv_y)
    have 1: "\<forall>a \<in> e. (Equiv [[a]]G) = x" by (metis "10" `x \<equiv> Equiv e` assms(1))
    have 2: "\<forall>a \<in> f. (Equiv [[a]]G) = y" by (metis "10" `y \<equiv> Equiv f` assms(2))
    have "\<forall>a \<in> e. \<forall>b \<in> f. (a \<lesssim>G b) \<longleftrightarrow> ((b\<acute>) \<lesssim>G (a\<acute>))" by (metis less_equal_Lit_antitone)
    then have "\<forall>a \<in> e. \<forall>b \<in> f. ((Equiv [[a]]G) \<lesssim>.G (Equiv [[b]]G)) \<longleftrightarrow> ((Equiv [[(b\<acute>)]]G) \<lesssim>.G (Equiv [[(a\<acute>)]]G))" by (metis less_equal_Lit_poset_eqclass_simp)
    then have 3: "\<forall>a \<in> e. \<forall>b \<in> f. ((Equiv [[a]]G) \<lesssim>.G (Equiv [[b]]G)) \<longleftrightarrow> (((Equiv [[b]]G).\<acute>G) \<lesssim>.G ((Equiv [[a]]G).\<acute>G))" by (metis complement_Lit_poset_eqclass_simp2)
    then obtain a b where "((Equiv [[a]]G) \<lesssim>.G (Equiv [[b]]G)) \<longleftrightarrow> (((Equiv [[b]]G).\<acute>G) \<lesssim>.G ((Equiv [[a]]G).\<acute>G))" "(Equiv [[a]]G) = x" "(Equiv [[b]]G) = y"
      by (metis "1" "2" Lit_poset_eqclass_reflexive `x \<equiv> Equiv e` `y \<equiv> Equiv f` all_not_in_conv assms(1) assms(2) complement_Lit_poset_eqclass_simp2 equals0I less_equal_Lit_poset_eqclass.simps(1))
    thus ?thesis by fast
  qed
qed

lemma Lit_eqclass_involutive :
  fixes G x
  assumes "x \<in> Lit_mod_plus G"
  shows "((x.\<acute>G).\<acute>G) = x"
proof (cases x)
  case Zero_rep
  thus ?thesis by simp  
next
  case One_rep
  thus ?thesis by simp
next
  case Equiv
  then have "x \<in> Lit_mod G"
    by (metis "10" Lit_mod_intro Lit_poset_eqclass_reflexive assms less_equal_Lit_poset_eqclass.simps(1))
  thus ?thesis by (metis Lit_mod_intro2 complement_Lit_poset_eqclass_simp2 complement_involutive)
qed


lemma Lit_eqclass_complement_in_Lit_mod:
  fixes G x
  assumes "x \<in> Lit_mod G"
  shows "(x.\<acute>G) \<in> Lit_mod G"
by (metis Lit_mod_intro Lit_mod_intro2 assms complement_Lit_poset_eqclass_simp2)


lemma zero_less_than_all:
  fixes G x
  assumes "x \<in> Lit_mod_plus G"
  shows "(zero G \<lesssim>.G x)"
proof -
  {
    assume "\<not>Lit_mod_plus_cond G"
    have ?thesis by (metis `\<not> Lit_mod_plus_cond G` less_equal_Lit_poset_eqclass.simps(2) zero_def)
  }
  {
    assume "Lit_mod_plus_cond G"
    obtain p where "zero G = p" by simp
    then obtain q where "(Equiv [[q]]G) = p" by (metis `Lit_mod_plus_cond G` zero_def)
    then have "(Equiv [[q]]G) = (Equiv [[SOME p. (p \<lesssim> G (p\<acute>))]]G)" by (metis `Lit_mod_plus_cond G` `zero G = p` zero_def)
    then have "q \<lesssim>G (q\<acute>)"
      by (metis (lifting, no_types) Lit_mod_plus_cond_def Lit_poset_eqclass_def Lit_poset_eqclass_membership `(Equiv [[q]]G) = p` `Lit_mod_plus_cond G` complement_involutive empty_Collect_eq equiv_Lit_antitone equiv_Lit_def less_equal_Lit.elims(2) less_equal_Lit.elims(3) less_equal_Lit_trans lit_mod_elt.inject mem_Collect_eq one someI_ex)
    then have ?thesis
      by (metis Lit_mod_intro2 Lit_mod_plus_def `zero G = p` `(Equiv [[q]]G) = p` `Lit_mod_plus_cond G` assms zero_less_equal_Lit_poset_eqclass)
  }
  thus ?thesis by (metis `\<not> Lit_mod_plus_cond G \<Longrightarrow> zero G \<lesssim>.G x`)
qed

lemma all_zero_Eqclasses:
  fixes G a
  assumes "Lit_mod_plus_cond G"
  and "a \<lesssim>G (a\<acute>)"
  shows "(Equiv [[a]]G) = zero G"
proof (rule ccontr)
  assume "(Equiv [[a]]G) \<noteq> zero G"
  then show False
    by (metis Lit_mod_intro Lit_mod_plus_def Lit_poset_eqclass_antisym assms(1) assms(2) zero_def zero_less_equal_Lit_poset_eqclass zero_less_than_all)
qed

lemma Lit_eqiv_class_complement_inconsistency :
  fixes G x y
  assumes "x \<in> Lit_mod_plus G"
  and "y \<in> Lit_mod_plus G"
  and "(x \<lesssim>.G y)"
  and "(x \<lesssim>.G (y.\<acute>G))"
  shows "x = zero G"
proof (cases x)
  case Zero_rep
  thus ?thesis by (metis Lit_eqclass_complement_in_Lit_mod Lit_mod_intro2 Lit_mod_plus_def assms(1) complement_Lit_poset_eqclass.simps(2) lit_mod_elt.distinct(5) zero_def)
next
  case One_rep
  thus ?thesis by (metis assms(3) assms(4) complement_Lit_poset_eqclass.simps(3) less_equal_Lit_poset_eqclass.elims(2) lit_mod_elt.distinct(1) lit_mod_elt.distinct(5))
next
  case Equiv
  note Equiv_x = Equiv
  thus ?thesis
  proof (cases y)
    case Zero_rep
    thus ?thesis by (metis Equiv_x assms(3) less_equal_Lit_poset_eqclass.simps(7))
  next
    case One_rep
    thus ?thesis by (metis Equiv_x assms(4) complement_Lit_poset_eqclass.simps(3) less_equal_Lit_poset_eqclass.simps(7))
  next
    case Equiv
    note Equiv_y = Equiv
    obtain e f where "x \<equiv> Equiv e" "y \<equiv> Equiv f" by (metis Equiv_x Equiv_y)
    have "\<forall>a \<in> e. \<forall>b \<in> f. (a \<lesssim>G b)"
      by (metis "10" `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(1) assms(2) assms(3) less_equal_Lit_poset_eqclass_simp lit_mod_elt.inject)
    have "\<forall>a \<in> e. \<forall>b \<in> f. (a \<lesssim>G (b\<acute>))"
      by (metis "10" `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(1) assms(2) assms(4) complement_Lit_poset_eqclass_simp less_equal_Lit_poset_eqclass_simp lit_mod_elt.inject)
    then obtain a b where "(a \<lesssim>G b)" "(a \<lesssim>G (b\<acute>))" "a \<in> e" "b \<in> f"
      by (metis `x \<equiv> Equiv e` `y \<equiv> Equiv f` assms(3) less_equal_Lit_poset_eqclass.simps(1))
    have "b \<lesssim>G (a\<acute>)" by (metis `a \<lesssim> G (b\<acute>)` antitone less_equal_Lit.simps)
    have "a \<lesssim>G (a\<acute>)" by (metis `a \<lesssim> G b` `b \<lesssim> G (a\<acute>)` less_equal_Lit_trans)
    have "Lit_mod_plus_cond G"
      unfolding Lit_mod_plus_cond_def by (metis `a \<lesssim> G (a\<acute>)`)
    then have "zero G = (Equiv [[a]]G)" by (metis `a \<lesssim> G (a\<acute>)` all_zero_Eqclasses)
    thus ?thesis by (metis "10" `a \<in> e` `x \<equiv> Equiv e` assms(1))
  qed
qed

lemma Lit_eqclass_in_Lit_mod_plus:
  fixes G x
  assumes "x \<in> Lit_mod_plus G"
  shows "x.\<acute>G \<in> Lit_mod_plus G"
proof (cases x)
  case Zero_rep
  thus ?thesis by (metis (mono_tags) Lit_eqclass_complement_in_Lit_mod Lit_mod_plus_def Un_insert_right assms complement_Lit_poset_eqclass.simps(2) insertI1 insert_commute)
next
  case One_rep
  thus ?thesis by (metis Lit_eqclass_complement_in_Lit_mod Lit_mod_plus_def Un_absorb assms complement_Lit_poset_eqclass.simps(3) insert_subset le_iff_sup sup.boundedE)
next
  case Equiv
  thus ?thesis by (metis Lit_mod_plus_intro complement_Lit_poset_eqclass.simps(1))
qed

lemma zero_in_Lit_mod_plus[simp]:
  fixes G
  shows "zero G \<in> Lit_mod_plus G"
proof -
{
  assume "\<not>Lit_mod_plus_cond G"
  then have "zero G = Zero_rep" by (metis zero_def)
  have ?thesis by (metis Lit_mod_plus_def Un_upper2 `\<not> Lit_mod_plus_cond G` `zero G = Zero_rep` insert_subset)
}
{
  assume "Lit_mod_plus_cond G"
  then have "zero G = Equiv [[SOME p. (p \<lesssim> G (p\<acute>))]]G" by (metis zero_def)
  have ?thesis by (metis Lit_mod_plus_intro `zero G = Equiv [[SOME p. (p \<lesssim> G (p\<acute>))]]G`)
}
  thus ?thesis by (metis `\<not> Lit_mod_plus_cond G \<Longrightarrow> zero G \<in> Lit_mod_plus G`)
qed

lemma one_in_Lit_mod_plus[simp]:
  fixes G
  shows "one G \<in> Lit_mod_plus G"
unfolding one_def by (metis Lit_eqclass_in_Lit_mod_plus zero_in_Lit_mod_plus)

definition up_closed :: "lit_mod_elt set \<Rightarrow> formula set \<Rightarrow> bool" where
  "up_closed A G \<equiv> \<forall>v \<in> A. (\<forall>w \<in> Lit_mod_plus G. (v \<lesssim>.G w) \<longrightarrow> w \<in> A)"

definition complete :: "lit_mod_elt set \<Rightarrow> formula set \<Rightarrow> bool" where
  "complete A G \<equiv> \<forall>v \<in> Lit_mod_plus G. v \<in> A \<or> (v.\<acute>G) \<in> A"

definition consistent :: "lit_mod_elt set \<Rightarrow> formula set \<Rightarrow> bool" where
  "consistent A G \<equiv> \<forall>v \<in> A. \<not>(v \<in> A \<and> (v.\<acute>G) \<in> A)"


definition "points G \<equiv> {S. S \<subseteq> Lit_mod_plus G \<and> up_closed S G \<and> complete S G \<and> consistent S G}"

lemma zeroisone:
    assumes "G \<equiv> {Some (q.) are (q`)}"
    shows " zero G = one G"
proof - 
  have "G\<turnstile> All (q.) are (q`)" 
    by (metis (mono_tags) ass assms axiom complement.simps(1) insert_compr mem_Collect_eq some2 the_elem_eq x)
  have "G\<turnstile> All (q`) are (q.)"
    by (metis (full_types) ass assms axiom complement.simps(1) complement_involutive insertI1 x)
  have "zero G = Equiv [[q.]] G" 
    by (metis Lit_mod_plus_cond_def `G \<turnstile> All q. are (q\`)` all_zero_Eqclasses complement.simps(1) complement_involutive less_equal_Lit.elims(3))
  have "zero G = Equiv [[q`]] G" 
    by (metis Lit_mod_plus_cond_def `G \<turnstile> All (q\`) are (q.)` all_zero_Eqclasses complement.simps(1) less_equal_Lit.elims(3))
  thus ?thesis 
    by (metis `zero G = Equiv [[q.]]G` complement.simps(2) complement_Lit_poset_eqclass_simp2 one_def)
qed

lemma falseiszero:
  assumes "G \<equiv> {All (q.) are (q`)}"
  shows "(case (zero G) of (Equiv z) \<Rightarrow> (q.)\<in> z)"
(*ak nitpick finds a false counterexample *)
proof -
  have "Lit_mod_plus_cond G"
    unfolding Lit_mod_plus_cond_def
      by (metis (mono_tags) ass assms complement.simps(1) complement_involutive insertI1 less_equal_Lit.elims(3) the_elem_eq)
  have "(q.) \<lesssim>G ((q.)\<acute>)" 
    by (metis assms complement.simps(2) insertI1 less_equal_Lit_ass)
  then have "zero G = Equiv [[q.]]G" 
    unfolding zero_def by (metis (lifting) Lit_mod_plus_cond_def all_zero_Eqclasses someI)
  have "(q.) \<in> [[q.]]G" by (metis Lit_poset_eqclass_membership)
  thus ?thesis
by (metis `zero G = Equiv [[q.]]G` lit_mod_elt.simps(10))
qed


definition consistent2 :: "lit_mod_elt set \<Rightarrow> formula set \<Rightarrow> bool" where
  "consistent2 S G \<equiv> ( \<forall>x \<in> S. \<forall>y \<in> S. \<not>(x \<lesssim>.G (y.\<acute>G)) )"

lemma l4_1_aux : 
  fixes G S
  assumes "S \<subseteq> Lit_mod_plus G"
  shows "consistent2 S G \<Longrightarrow> consistent S G"
proof -
  assume "consistent2 S G"

  have "consistent S G" 
    unfolding consistent_def
    proof (rule ccontr)
      assume "\<not> (\<forall>x \<in> S. \<not> (x \<in> S \<and> x.\<acute>G \<in> S))"
      then have "\<exists>x \<in> S. x \<in> S  \<and> x.\<acute>G \<in> S" by blast
      then obtain x where "x \<in> S  \<and> x.\<acute>G \<in> S" by fast
      then have "\<not> (x \<lesssim>.G x)" 
        by (metis Lit_eqclass_antitone `consistent2 S G` assms consistent2_def set_rev_mp)
      have "(x \<lesssim>.G x)"
        by (metis Lit_poset_eqclass_reflexive `x \<in> S \<and> x .\<acute> G \<in> S` assms in_mono)
      then show False by (metis `\<not> (x \<lesssim>.G x)`)
    qed
  thus ?thesis by simp
qed




lemma l4_1 :
  fixes G S_0
  assumes "S_0 \<subseteq> Lit_mod_plus G"
  and "points G \<noteq> {}"
  shows "( \<exists>S \<in> points G. S_0 \<subseteq> S ) \<longleftrightarrow> (consistent2 S_0 G)"
proof -
  {
    assume "\<exists>S \<in> points G. S_0 \<subseteq> S"
    have "\<forall>x \<in> S_0. \<forall>y \<in> S_0. \<not>(x \<lesssim>.G (y.\<acute>G))"
    proof (rule ccontr)
      assume "\<not> (\<forall>x \<in> S_0. \<forall>y \<in> S_0. \<not>(x \<lesssim>.G (y.\<acute>G)))"
      then have "\<exists>x \<in> S_0. \<exists>y \<in> S_0. (x \<lesssim>.G (y.\<acute>G))" by fast
      then obtain x y where "(x \<lesssim>.G (y.\<acute>G))" "x \<in> S_0" "y \<in> S_0" by force
      
      obtain S where S_0_sub_S: "S_0 \<subseteq> S" "S \<in> points G" by (metis `\<exists>S\<in>points G. S_0 \<subseteq> S`)
      {
        have "S \<notin> points G"
        proof (rule ccontr)
          assume "\<not>(S \<notin> points G)"
          have "(y.\<acute>G) \<in> S"
          proof -
            have f1: "\<And>v. S_0 \<subseteq> v \<longrightarrow> y \<in> v"
              by (metis (lifting) `y \<in> S_0` in_mono)
            have "\<And>v. S_0 \<subseteq> v \<longrightarrow> x \<in> v"
              by (metis (lifting) `x \<in> S_0` in_mono)
            hence "x \<in> S"
              using S_0_sub_S(1) subset_trans by simp
            hence "x \<in> S \<and> y .\<acute> G \<in> Lit_mod_plus G \<and> up_closed S G"
              using f1 Lit_eqclass_in_Lit_mod_plus S_0_sub_S(2) assms(1) points_def by simp
            hence "\<exists>w u. w \<in> S \<and> y.\<acute>G \<in> Lit_mod_plus u \<and> (w \<lesssim>.u y.\<acute>G) \<and> up_closed S u"
              by (metis (lifting) `x \<lesssim>.G y .\<acute> G`)
            thus "y .\<acute> G \<in> S"
              using up_closed_def by auto
          qed

          have "y \<in> S" by (metis S_0_sub_S(1) `y \<in> S_0` in_mono)
          then show False by (metis (lifting) S_0_sub_S(2) `y .\<acute> G \<in> S` consistent_def mem_Collect_eq points_def)
        qed 
      }
      then show False by (metis S_0_sub_S(2))
    qed
  }
  {
    assume "consistent2 S_0 G"
    then have "\<forall>x \<in> S_0. \<forall>y \<in> S_0. \<not>(x \<lesssim>.G (y.\<acute>G))" by (metis consistent2_def)
    {
      assume "S_0 = {}"
      have "( \<exists>S \<in> points G. S_0 \<subseteq> S )" by (metis Collect_mem_eq `S_0 = {}` assms(2) empty_Collect_eq empty_subsetI)
    }
    {
      assume "S_0 \<noteq> {}" 
      def A \<equiv> "{x. S_0 \<subseteq> x \<and> x \<subseteq> Lit_mod_plus G \<and> consistent2 x G}"
  
      have "\<forall>C \<in> chains A. \<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U"
      proof rule
        fix C 
        assume "C \<in> chains A"
        show  "\<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U"
        proof (simp add: A_def)
        {
          assume "C \<noteq> {}"
          def U \<equiv> "\<Union>C"
          obtain x where "x \<in> C" by (metis Collect_mem_eq `C \<noteq> {}` empty_Collect_eq)
          then have "S_0 \<subseteq> x" by (metis (mono_tags) A_def `C \<in> chains A` chainsD2 mem_Collect_eq set_rev_mp)
          then have "S_0 \<subseteq> U" by (metis (full_types) U_def Union_upper `x \<in> C` subset_trans)
  
          have "\<Union>C \<subseteq> Lit_mod_plus G" 
            by (metis (lifting) A_def Sup_le_iff `C \<in> chains A` chainsD2 mem_Collect_eq set_rev_mp)
          
          have "consistent2 (\<Union>C) G"
            unfolding consistent2_def
            proof auto
              fix y and x and ya and yb
              assume a1: "y \<in> C"
              assume a2: "x \<in> y"
              assume a3: "ya \<in> C"
              assume a4: "yb \<in> ya"
              assume a5: "x \<lesssim>.G yb .\<acute> G" 
              show False by (metis (lifting, mono_tags) A_def `C \<in> chains A` a1 a2 a3 a4 a5 chainsD chainsD2 consistent2_def mem_Collect_eq subsetD)
            qed
  
          have "\<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U" by (metis (lifting) A_def U_def Union_upper `S_0 \<subseteq> U` `\<Union>C \<subseteq> Lit_mod_plus G` `consistent2 (\<Union>C) G` mem_Collect_eq)
        }
        {
          assume "C = {}"
          def U \<equiv> "S_0"
          have "\<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U" by (metis (lifting) A_def `C = {}` `consistent2 S_0 G` all_not_in_conv assms(1) empty_Collect_eq eq_iff)
        }
          thus "\<exists>U. S_0 \<subseteq> U \<and> U \<subseteq> Lit_mod_plus G \<and> consistent2 U G \<and> (\<forall>X\<in>C. X \<subseteq> U)" 
            by (metis (lifting) A_def `C \<noteq> {} \<Longrightarrow> \<exists>U\<in>A. \<forall>X\<in>C. X \<subseteq> U` mem_Collect_eq)
        qed
      qed
      then have "\<exists>M \<in> A. \<forall>X \<in> A. M \<subseteq> X \<longrightarrow> X = M" by (metis Zorn_Lemma2)
      then obtain S_1 where "S_1 \<in> A" "\<forall>X \<in> A. S_1 \<subseteq> X \<longrightarrow> X = S_1" by force
  
      then have "consistent2 S_1 G"
        by (metis (lifting, no_types) A_def mem_Collect_eq)
      have S_1_in_Lit_mod : "S_1 \<subseteq> Lit_mod_plus G" by (metis (lifting, no_types) A_def `S_1 \<in> A` mem_Collect_eq)
      def S \<equiv> "{ (q::lit_mod_elt). q \<in> Lit_mod_plus G \<and> (\<exists>p \<in> S_1. (p \<lesssim>.G q))}"
  
      have "\<forall>x \<in> S. (\<exists>y \<in> S_1. (y \<lesssim>.G x))" 
        proof -
          { fix sk\<^sub>0 :: lit_mod_elt
            have ff1: "sk\<^sub>0 \<in> {uu. \<exists>x. x \<in> S_1 \<and> (x \<lesssim>.G uu)} \<or> sk\<^sub>0 \<notin> S \<or> (\<exists>x\<^sub>1. x\<^sub>1 \<in> S_1 \<and> (x\<^sub>1 \<lesssim>.G sk\<^sub>0))"
              using S_def by blast
            have "sk\<^sub>0 \<notin> S \<or> (\<exists>x\<^sub>1. x\<^sub>1 \<in> S_1 \<and> (x\<^sub>1 \<lesssim>.G sk\<^sub>0))"
              using ff1 by fastforce }
          thus "\<forall>x\<in>S. \<exists>y\<in>S_1. (y \<lesssim>.G x)"
            by blast
        qed
   
      have S_in_Lit_mod_plus : "S \<subseteq> Lit_mod_plus G"
        by (metis (lifting, no_types) S_def mem_Collect_eq subsetI)
      
      have "S_0 \<subseteq> S_1" by (metis (lifting, no_types) A_def `S_1 \<in> A` mem_Collect_eq)
      have "S_1 \<subseteq> S"
        unfolding S_def by (metis (lifting, mono_tags) Lit_poset_eqclass_reflexive S_1_in_Lit_mod S_def in_mono mem_Collect_eq subsetI)
      then have "S_0 \<subseteq> S" by (metis `S_0 \<subseteq> S_1` dual_order.trans)
      
      have "S_1 \<noteq> {}" by (metis `S_0 \<noteq> {}` `S_0 \<subseteq> S_1` subset_empty)
  
      have "one G \<in> S" 
        proof -
          obtain x where "x \<in> S_1" by (metis `S_1 \<noteq> {}` ex_in_conv)
  
          then have "x \<in> Lit_mod_plus G" by (metis (full_types) S_1_in_Lit_mod in_mono)
          have "x \<lesssim>.G (one G)"
            proof -
            {
              assume "\<not>Lit_mod_plus_cond G"
              then have "one G = One_rep" by (metis Lit_eqiv_class_complement_inconsistency Lit_mod_plus_def Un_insert_right complement_Lit_poset_eqclass.simps(2) insertCI less_equal_Lit_poset_eqclass.simps(2) one_def)
              then have ?thesis by (metis (full_types) Lit_eqclass_antitone `x \<in> Lit_mod_plus G` complement_Lit_poset_eqclass.simps(3) less_equal_Lit_poset_eqclass.simps(2) one_in_Lit_mod_plus)
            }
            {
              assume "Lit_mod_plus_cond G"
              then have "zero G = Equiv [[SOME p. (p \<lesssim> G (p\<acute>))]]G" by (metis zero_def)
              then have "(zero G) \<lesssim>.G x.\<acute>G" by (metis (full_types) Lit_eqclass_in_Lit_mod_plus `x \<in> Lit_mod_plus G` zero_less_than_all)
              then have ?thesis by (metis Lit_eqclass_antitone Lit_eqclass_in_Lit_mod_plus Lit_eqclass_involutive `x \<in> Lit_mod_plus G` one_def zero_in_Lit_mod_plus)
            }
              thus ?thesis by (metis `\<not> Lit_mod_plus_cond G \<Longrightarrow> x \<lesssim>.G (one G)`)
            qed
            then have "\<exists>p\<in>S_1. (p \<lesssim>.G (one G))" by (metis `x \<in> S_1`)
            show ?thesis by (metis (lifting, no_types) S_def `\<exists>p\<in>S_1. (p \<lesssim>.G (one G))` mem_Collect_eq one_in_Lit_mod_plus)
          qed
  
      have "up_closed S G"
        unfolding up_closed_def 
        proof auto
          fix x y
          assume "x \<in> S" and "y \<in> Lit_mod_plus G" and "x \<lesssim>.G y"
  
          { assume "x \<in> S_1"
          have "y \<in> S" 
            unfolding S_def by (metis (lifting, no_types) `x \<in> S_1` `x \<lesssim>.G y` `y \<in> Lit_mod_plus G` mem_Collect_eq) }
          { assume "x \<notin> S_1"
          then have "\<exists>a \<in> S_1. (a \<lesssim>.G x)" by (metis `x \<in> S` `\<forall>x\<in>S. \<exists>y\<in>S_1. (y \<lesssim>.G x)`)
          then have "y \<in> S"
            unfolding S_def by (metis (lifting, mono_tags) Lit_poset_eqclass_trans S_1_in_Lit_mod S_in_Lit_mod_plus `x \<in> S` `x \<lesssim>.G y` `y \<in> Lit_mod_plus G` mem_Collect_eq set_rev_mp) }
          thus "y \<in> S" by (metis `x \<in> S_1 \<Longrightarrow> y \<in> S`)
        qed
  
  
      have "consistent S G"
      proof (rule ccontr)
        assume "\<not> consistent S G"
        then obtain r where "r \<in> S" "r.\<acute>G \<in> S" by (metis (full_types) consistent_def)
        then obtain q_1 q_2 where "q_1 \<in> S_1" "q_1 \<lesssim>.G r" "q_2 \<in> S_1" "q_2 \<lesssim>.G r.\<acute>G" by (metis `\<forall>x\<in>S. \<exists>y\<in>S_1. (y \<lesssim>.G x)`)
        then have 1: "r \<lesssim>.G q_2.\<acute>G" by (metis (full_types) Lit_eqclass_antitone Lit_eqclass_involutive S_1_in_Lit_mod S_in_Lit_mod_plus `r.\<acute>G \<in> S` `r \<in> S` in_mono)
        have 2: "r \<in> Lit_mod_plus G" by (metis S_in_Lit_mod_plus `r \<in> S` in_mono)
        have "q_1 \<in> Lit_mod_plus G" "q_2 \<in> Lit_mod_plus G" by (metis S_1_in_Lit_mod `q_1 \<in> S_1` set_rev_mp) (metis S_1_in_Lit_mod `q_2 \<in> S_1` set_rev_mp)
        then have "q_2.\<acute>G \<in> Lit_mod_plus G" by (metis Lit_eqclass_in_Lit_mod_plus)
        with 1 2 `q_1 \<lesssim>.G r` have "q_1 \<lesssim>.G q_2.\<acute>G" by (metis Lit_poset_eqclass_trans `q_1 \<in> Lit_mod_plus G`)
        then have "q_2.\<acute>G \<in> S_1" by (metis `q_1 \<in> S_1` `q_2 \<in> S_1` `consistent2 S_1 G` consistent2_def)
        then show False by (metis S_1_in_Lit_mod `q_2 \<in> S_1` `consistent2 S_1 G` consistent_def l4_1_aux)
      qed
  
      have "complete S G"
        unfolding complete_def
      proof (rule ccontr)
        assume "\<not> (\<forall>x\<in>Lit_mod_plus G. x \<in> S \<or> x.\<acute>G \<in> S)"
        then have "\<exists>x \<in> Lit_mod_plus G. x \<notin> S \<and> x.\<acute>G \<notin> S" by blast
        then obtain r where "r \<in> Lit_mod_plus G" "r \<notin> S \<and> r.\<acute>G \<notin> S" by force
  
        have "consistent2 (S_1 \<union> {r}) G"
          proof (rule ccontr)
            assume "\<not> consistent2 (S_1 \<union> {r}) G"
            then have "\<exists>x \<in> (S_1 \<union> {r}). \<exists>y \<in> (S_1 \<union> {r}). (x \<lesssim>.G y.\<acute>G)" 
              by (metis (mono_tags) consistent2_def)
            then obtain x y where "x \<in> (S_1 \<union> {r})" "y \<in> (S_1 \<union> {r})" "(x \<lesssim>.G y.\<acute>G)" by blast
            have "x \<in> Lit_mod_plus G" "y \<in> Lit_mod_plus G"
              by (metis (full_types) S_1_in_Lit_mod Un_iff `r \<in> Lit_mod_plus G` `x \<in> S_1 \<union> {r}` empty_iff in_mono insert_iff)
                 (metis (full_types) S_1_in_Lit_mod Un_iff `r \<in> Lit_mod_plus G` `y \<in> S_1 \<union> {r}` empty_iff in_mono insert_iff)
            {
              assume "x = r" "y \<noteq> r"
              then have "r \<lesssim>.G y.\<acute>G" by (metis `x \<lesssim>.G y .\<acute> G`)
              then have "y \<lesssim>.G r.\<acute>G" by (metis (mono_tags) Lit_eqclass_antitone Lit_eqclass_in_Lit_mod_plus Lit_eqclass_involutive `r \<in> Lit_mod_plus G` `x = r` `x \<lesssim>.G y .\<acute> G` `y \<in> Lit_mod_plus G`)
              have "y \<in> S_1" by (metis Un_iff `y \<in> S_1 \<union> {r}` `y \<noteq> r` singleton_iff)
              then have "r.\<acute>G \<in> S" by (metis (lifting, no_types) Lit_eqclass_in_Lit_mod_plus S_def `r \<in> Lit_mod_plus G` `y \<lesssim>.G r .\<acute> G` mem_Collect_eq)
              then have False by (metis `r \<notin> S \<and> r .\<acute> G \<notin> S`)
            }
            {
              assume "x \<noteq> r" "y = r"
              then have "x \<lesssim>.G r.\<acute>G" by (metis `x \<lesssim>.G y .\<acute> G`)
              have "x \<in> S_1" by (metis Un_iff `x \<in> S_1 \<union> {r}` `x \<noteq> r` singleton_iff)
              then have "r.\<acute>G \<in> S" by (metis (lifting, no_types) Lit_eqclass_in_Lit_mod_plus S_def `r \<in> Lit_mod_plus G` `x \<lesssim>.G r .\<acute> G` mem_Collect_eq)
              then have False by (metis `r \<notin> S \<and> r .\<acute> G \<notin> S`)
            }
            {
              assume "x = r" "y = r"
              then have "r \<lesssim>.G r.\<acute>G" by (metis `x \<lesssim>.G y.\<acute>G`)
              then have "r = zero G" by (metis Lit_eqiv_class_complement_inconsistency Lit_poset_eqclass_reflexive `r \<in> Lit_mod_plus G`)
              then have False by (metis `r \<notin> S \<and> r .\<acute> G \<notin> S` `one G \<in> S` one_def)
            }   
            {
              assume "x \<noteq> r" "y \<noteq> r"
              then have "x \<in> S_1" "y \<in> S_1" 
                by (metis Un_iff `x \<in> S_1 \<union> {r}` singleton_iff)
                   (metis Un_iff `y \<in> S_1 \<union> {r}` `y \<noteq> r` singleton_iff)
              then have "x \<lesssim>.G y.\<acute>G" by (metis `x \<lesssim>.G y .\<acute> G`)
              then have False by (metis `x \<in> S_1` `y \<in> S_1` `consistent2 S_1 G` consistent2_def)
            }
            then show False by (metis `\<lbrakk>x = r; y = r\<rbrakk> \<Longrightarrow> False` `\<lbrakk>x = r; y \<noteq> r\<rbrakk> \<Longrightarrow> False` `\<lbrakk>x \<noteq> r; y = r\<rbrakk> \<Longrightarrow> False`)
          qed
  
        have "S_0 \<subseteq> (S_1 \<union> {r})" by (metis `S_0 \<subseteq> S_1` sup.coboundedI1)
        have "(S_1 \<union> {r}) \<subseteq> Lit_mod_plus G" by (metis S_1_in_Lit_mod Un_empty_right Un_insert_right `r \<in> Lit_mod_plus G` insert_subset)
        then have "(S_1 \<union> {r}) \<in> A"
          unfolding A_def by (metis (lifting) `S_0 \<subseteq> S_1 \<union> {r}` `consistent2 (S_1 \<union> {r}) G` mem_Collect_eq)
        then show False
          by (metis Un_absorb Un_empty_right Un_insert_right `r \<notin> S \<and> r .\<acute> G \<notin> S` `S_1 \<subseteq> S` `\<forall>X\<in>A. S_1 \<subseteq> X \<longrightarrow> X = S_1` insert_subset subset_Un_eq)
      qed
  
      have "S \<in> points G" 
        unfolding points_def 
        by (metis (lifting, no_types) S_in_Lit_mod_plus `complete S G` `consistent S G` `up_closed S G` mem_Collect_eq)
      have "( \<exists>S \<in> points G. S_0 \<subseteq> S )" by (metis `S \<in> points G` `S_0 \<subseteq> S`)
    }
    then have "\<exists>S\<in>points G. S_0 \<subseteq> S" by (metis `S_0 = {} \<Longrightarrow> \<exists>S\<in>points G. S_0 \<subseteq> S`)
  }
  thus ?thesis by (metis `\<exists>S\<in>points G. S_0 \<subseteq> S \<Longrightarrow> \<forall>x\<in>S_0. \<forall>y\<in>S_0. \<not> (x \<lesssim>.G y.\<acute>G)` consistent2_def)
qed
(*declare [[show_types]]*)

end
