(*header {* $\AA$: the logic of All p are q --- Section2.thy*}*)

theory Section2
imports Main "~~/src/HOL/Library/Order_Relation"

begin

subsection {* Syntax and Semantics --- Types and Definitions in Isabelle *}

text {* In this section we are going to formalize the proofs of Section 2 of the Lecture Notes. 
Therefore, we need to find a datatype of formulas of the kind
\pftext{All p are q} and in order to do this we even need to first define a datatype of atomic
propositions \pf{p,q,\ldots}. After we have done this, we can define the semantics of such formulas
in a model, we can implement the derivability relation and proof soundness and completeness.*}

text {*  The set of atomic propositions is formalized as a
  type.\footnote{ See \cite[p.173]{tutorial:isabellehol} for further explanations
  on \texttt{typedecl}.} 
  % actually lots of questions when looking at p.119
  Roughly speaking types are sets as known from set theory, 
  but there are some differences. Making good use of types is one of 
  the things one has to learn using Isabelle/HOL. For example, 
  formalizing atomic proposition as a type imposes a constraint 
  on the set of propositions:

\specialbox{Types in Isabelle are non-empty.}

*}

typedecl atProp

text {* Next we use the \pf{\bf datatype} declaration to define formulas. 
  \pftext{All} is called a constructor, which can be considered as
  a function that takes two arguments of type \pftext{atProp} and produces
  an element of type \pftext{formula}. The addition \pftext{\ep{All \_ are \_ }}
  is optional, 
  but allows us to write, as in the   lecture notes,
  \pf{All p are q} instead of \pf{All p q}. *}

datatype formula = All atProp atProp ("All _ are _ ")
(* (* print theorems screws up (to some extent) the document preparation *)
print_theorems
*)

text {*  Inductively defined sets are best formalized using the datatype 
  declaration, for example, because Isabelle then provides inbuilt 
  support for induction. The \pf{\bf print-theorems} command is not necessary, 
  but if you move your mouse over it in Isabelle you can see
  which theorems you get for free by using the datatype declaration.
  For example
{\footnotesize
\begin{verbatim}
  formula.eq.simps:
    equal_class.equal All ?atProp1 are ?atProp2 All ?atProp1' are ?atProp2'  
    \<equiv> ?atProp1 = ?atProp1' \<and> ?atProp2 = ?atProp2'
\end{verbatim}
}
says that two formulas are equal iff their respective atomic propositions are 
equal.\footnote{See \cite[Section 8.5.2]{tutorial:isabellehol} 
(and in particular p.176) and 
\cite[Section 2.4]{tutorial:datatypes} for more details.} *}

text {*  The next definition describes models over a carrier as models parametric
  in an an aribrary (non-empty) type
  called \pftext{\primea}. The arrow \pftext{$\Rightarrow$} and \pftext{set} are 
  type constructors, where \pftext{set} is the type
  of all subsets of \pftext{\primea} and \pftext{$\Rightarrow$} 
  constructs the type of all 
  set-theoretic functions. To summarize, a model over \pf{\primea}
  is a function from atomic propositions to the powerset of \pf{\primea}, 
  that is, it is
  an element of the type \pftext{\ep{atProp $\Rightarrow$ \primea\  set}}, 
  for which we
  introduce the abbreviation\footnote{See \cite[p.24]{tutorial:isabellehol} for more
on \texttt{type\_synonym}.} *}

type_synonym 'a model = "(atProp \<Rightarrow>'a set)" 

text {* In particular, the notion of model above cannot have empty carrier. Alternatively, 
  we could have defined a model over \pf{$'a$} as a pair of a possible 
  empty subset of \pf{$'$a} and a function
  \pftext{\ep{atProp $\Rightarrow$ \primea\  set}} 
  but then we would need an extra condition to make sure that
  the image of the function lies inside that carrier. 
  In other words, we  get the additional 
  complication of 
  specifying the well formed models among the premodels as in *}

type_synonym 'a pre_model = "'a set \<times> (atProp \<Rightarrow> 'a set)"
definition wf_model :: "'a pre_model \<Rightarrow> bool" 
  where "wf_model M \<equiv> let (M,f) = M in (! p. f p \<subseteq> M)" 

text {* In the following we will only use the first alternative and 
  not make use of pre-model and wf-model. *}


text {* The lecture notes continue with the definition of satisfiability
  \begin{qcolor}
  $$\Model \models  \mbox{\sf All $p$ are $q$} \quadiff 
    \semantics{p} \subseteq \semantics{q}
    $$
  \end{qcolor}
  which we formalize as follows.
*}



fun satisfies :: "'a model \<Rightarrow> formula \<Rightarrow> bool" ("_ \<Turnstile> _" )
where
  "satisfies M (All x are y) = (M x \<subseteq> M y)"

(* Do we want a discussion about fun and possible alternatives (see below)? *)

(*
definition satisfies :: "'a model \<Rightarrow> formula \<Rightarrow> bool" where
"satisfies M f \<equiv> case f of All x are y \<Rightarrow> (M x \<subseteq> M y)"
*)

(* definitions cant pattern match, because they are native HOL *)
(*
definition satisfies :: "'a model \<Rightarrow> formula \<Rightarrow> bool" where
"satisfies M (All x are y) \<equiv> (M x \<subseteq> M y)"
*)

text {* The lecture notes continue with the following example. *}

text{*
\begin{qcolor}
\textbf{Example.}
Let $\bP = \{n,p,q\}$. %(Hence $\AA$ has exactly nine sentences.)
Let $M = \{1,2, 3,4, 5\}$.
Let
$\semantics{n} = \emptyset$,
 $\semantics{p} = \{1,3, 4\}$,
 and $\semantics{q} = \{1,3\}$.
This specifies a model $\Model$.
The following sentences are 
true in $\Model$:  {\sf All $n$ are $n$}, 
 {\sf All $n$ are $p$}, 
 {\sf All $n$ are $q$},    {\sf All $p$ are $p$}, {\sf All $q$ are $p$}, 
 and {\sf All $q$ are $q$}.
The other three sentences in $\AA$ are false in $\Model$.
\end{qcolor}
*}

text {*
The interesting   question is how to formalise the three ``let" statements above.
In particular, the ``let $M=\dots$'' is formalized differently than the other two.
The reason is that the carrier $M$ of the model is formalized as a
type parameter. Therefore we can instantiate it by defining a datatype: *}

datatype example_2_1 = e1 | e2 | e3 | e4 | e5

text {*The other two ``let" statements are translated as assumptions. 
For the first one, note that \pftext{\ep{UNIV :: atProp set}} is the 
Isabelle way of naming \pf{UNIV} as the largest set in \pf{atProp set}, 
that is, \pf{UNIV} is \pf{atProp} seen as a set. For the second note 
that Isabelle infers the type of the carrier of $M$ upon reading 
\pf{M p = \{e1,e3,e4\}}, the elements of which are elements of the 
type \pf{example-2-1}. We can now formalize and prove the claims made
in the exercise.
*}    

lemma example_2_1:
assumes "(UNIV :: atProp set) = {n,p,q} \<and> n\<noteq>p \<and> n\<noteq>q \<and> p\<noteq>q"
assumes "M n = {}  \<and>  M p = {e1,e3,e4}  \<and>  M q = {e1,e3}"
shows "M \<Turnstile> All n are n" 
   and "M \<Turnstile>All n are p" 
   and "M \<Turnstile>All n are q" 
   and "M \<Turnstile> All p are p" 
   and "M \<Turnstile> All q are p" 
   and "M \<Turnstile> All q are q"
   and "\<not> (M \<Turnstile> All p are n)"
   and "\<not> (M \<Turnstile> All p are q)"
   and "\<not> (M \<Turnstile> All q are n)"
proof %invisible -
  show "M \<Turnstile> All n are n" by simp
  show "M \<Turnstile> All n are p" by (metis assms(2) empty_subsetI satisfies.simps)
  show "M \<Turnstile> All n are q" by (metis assms(2) bot.extremum satisfies.simps)
  show "M \<Turnstile> All p are p" by simp
  show "M \<Turnstile> All q are p" by (metis assms(2) insert_mono satisfies.simps subset_insertI)
  show "M \<Turnstile> All q are q" by simp
  show "\<not> (M \<Turnstile> All p are n)" by (metis assms(2) bot.extremum_unique insert_not_empty satisfies.simps)
  show "\<not> (M \<Turnstile> All p are q)" by (metis assms(2) empty_iff example_2_1.distinct(15) example_2_1.distinct(5) insert_iff insert_subset satisfies.simps)
  show "\<not> (M \<Turnstile> All q are n)" by (metis assms(2) insert_not_empty satisfies.simps subset_empty)
qed    


text {* The proof of the 9 statements can be done 
automatically using sledgehammer \cite{tutorial:sledgehammer}. Sledgehammer is an Isabelle command 
that calls automatic
theorem provers, either locally installed or over the internet, in order to prove
the current goal. For us, sledgehammer is a crucial ingredient of Isabelle. It allows us to conduct
proofs close to the level of pen and paper mathematics. Whenever in these notes, or in the theory files,
 you see a \pf{{\bf by}\ep{metis \ldots}} this shows a proof found by sledgehammer. 
Actually, for better readability of this document, we made most of these automatically found proofs invisible as can easily
be seen by comparing directly with the theory file.

\medskip We emphasize that the proofs \pf{{\bf by}\ep{metis \ldots}} are not meant to be readable
by humans. In our notes, they are usually proofs that are obvious on the mathematical level of
abstraction. On the other hand, if you know that such a proof depends on a particular fact
it is a good idea to check whether this fact is contained in the list of facts appearing in the 
dots of a \pf{{\bf by}\ep{metis \ldots}}.
\marginpar[left text]{video}
*}

text {* The lecture notes continue with extending satisfiability to sets
  of formulas 
\begin{qcolor}    
\begin{center}
$\Model\models\Gamma$ iff $\Model\models \phi$ for every $\phi\in \Gamma$
\end{center}
\end{qcolor}

and to semantic entailment between sets of formulas and formulas
\begin{qcolor}
\begin{center}
$\Gamma\models \phi$ iff  for all $\Model$: if  $\Model\models \Gamma$,  then
also $\Model\models\phi$.
\end{center}
\end{qcolor}
which we formalize as follows.
\specialbox{Overloading names, although possible to a degree, is not
as easy in Isabelle as it is in pen and paper maths. For example,
comparing the definitions of \pf{satisfies} and \pf{M-satisfies-G}
one would think that, as they have different types, both could well
have the same name, or, at least, use the same notation $\models$. 
But one problem here is that the parsing is done before the
type checking and ambiguous parse trees would result 
(recommended experiment). So this is a point that requires
some compromise from the mathematician's perspective.}
 *}

definition M_satisfies_G :: "'a model \<Rightarrow> formula set \<Rightarrow> bool" ("_ \<Turnstile>M _")
where
  "M_satisfies_G M G  \<equiv> \<forall>f. f \<in> G \<longrightarrow> (M \<Turnstile> f)"

text {* 
If we want to define semantic consequence or entailment, we want to say
that $G\models g$ iff $\forall M :: {'a} \textit{ model}. 
M\models G \rightarrow M\models g$. Due to the free type variable
$'a$ we run into a slight technical difficulty. For reasons explained
in some detail in \cite{Arthan14}, every variable on the right of a
definition also needs to appear on the left. 
So we could write, using a dummy term \pf{ty}, \ldots
*}


definition entails_b :: "formula set \<Rightarrow> formula \<Rightarrow> 'a \<Rightarrow> bool" 
where
  "entails_b G f (ty::'a) \<equiv> \<forall> (M::'a model). (M \<Turnstile>M G) \<longrightarrow> (M \<Turnstile> f)"

text {* \dots but this definition has the disadvantage that it looks
as if the function \pf{entails} depended on values of type $'a$. 
One way out is to use the ``type itself'' construction, which 
provides a type depending on $'a$ with only element (this element is denoted by 
TYPE($'a$) and we will encounter it later). More on the
itself type can be found in \cite{Wenzel97}.*}


definition entails :: "formula set \<Rightarrow> formula \<Rightarrow> 'a itself \<Rightarrow> bool" ("_ \<Turnstile>G _ _")
where
  "entails G f (ty::'a itself) \<equiv> \<forall> (M::'a model). (M \<Turnstile>M G) \<longrightarrow> (M \<Turnstile> f)"

(* can we show in Isabelle that an itself type has only one element? *)

(*
lemma itself_a:
shows "card( UNIV :: 'a itself set)=1"
oops
*)

(*
declare [[show_types]]

lemma itself_b:
fixes x y
assumes "x \<in> (UNIV :: 'a itself set)"
assumes "y \<in> (UNIV :: 'a itself set)"
shows "x=y"
find_theorems name:itself
using HOL.equal_itself_def
sorry

lemma itself_c:
assumes "x :: 'a itself set"
assumes "y :: 'a itself set"
shows "x=y"
*)

text {* \textbf{Further Reading. } For general background on Isabelle see Paulson's
original \cite{Paulson89} (in particular Section 1 and 2). \cite{Paulson89} also
gives a reason why types are assumed to be non-empty. In
 \cite[p.119]{tutorial:isabellehol} one can find a model checker as a worked out
example. *}

subsection {* Proof Theory --- Rules and Natural Deduction in Isabelle *}

text {*

The deductive system $\AA$ is given as 

\begin{qcolor}
\begin{framed}
$$ \begin{array}{lcl}
\infer[\mbox{\sc Axiom}]{ \mbox{\sf  All  $p$  are  $p$ }}{}
& \qquad &
\infer[\mbox{\sc Barbara}]{ \mbox{\sf  All  $p$  are  $q$ }}{ \mbox{\sf  All  $p$  are  $n$}
&   \mbox{\sf  All  $n$ are  $q$ }}
\\
\end{array}
$$
\end{framed}
\end{qcolor}

which is formalized as follows. (The 0 in \pf{0\ $\vdash$\ -} is an
annotation to avoid overloading wrt to \pf{-\ $\vdash$\ -} in the
next definition.)
*}

inductive derivable :: "formula \<Rightarrow> bool" ("0\<turnstile> _")
where
  A_axiom: "0\<turnstile> (All X are X)"
| A_barbara: "\<lbrakk>0\<turnstile>(All X are Y); 0\<turnstile>(All Y are Z)\<rbrakk> \<Longrightarrow> 0\<turnstile>(All X are Z)"
 
text {* 
\specialbox{
Isabelle implements natural deduction. The Isabelle notation for a rule of the
shape 
$$\infer[\mbox{\it name}]{ \mbox{\sf  C}}{ \mbox{\sf  A}
&   \mbox{\sf  B}}$$
is $$\pftext{ name: $\semantics{A;B} \Longrightarrow$ \sf C}$$
as in the rules \pf{A-axiom} and \pf{A-barbara} above. 
}
*}

text {* \specialbox{ Something about "inductive" } *}

text {* Let us look at how to reason in Isabelle using the natural 
deduction rules. The following example is again from the lecture notes. *}

text {* 
\begin{qcolor}
\textbf{Example. } 
Let $\Gamma$ be
$$\set{ \mbox{\sf All $l$ are $m$},  \mbox{\sf All $q$ are $l$},
 \mbox{\sf All $m$ are $p$}, \mbox{\sf All $n$ are $p$},   \mbox{\sf All $l$ are $q$}}$$
Let $\phi$ be    {\sf All $q$ are $p$}.  Here is a proof tree showing that
$\Gamma\proves \phi$:
\begin{framed}
$$
\infer[\mbox{\sc Barbara}]{ \mbox{\sf All $q$ are $p$}}{  \mbox{\sf All $q$ are $l$} & 
\infer[\mbox{\sc Barbara}]{ \mbox{\sf All $l$ are $p$}}{ 
\infer[\mbox{\sc Barbara}]{\mbox {\sf All $l$ are $m$}}{ \mbox{\sf All $l$ are $m$} &  
\infer[\mbox{\sc Axiom}]{\mbox{\sf All $m$ are $m$}}{}}
&   \mbox{\sf All $m$ are $p$}}}
$$
\end{framed}
\end{qcolor}
The proof tree
can be implemented in Isabelle as follows.
*}


lemma example_2_5:
assumes "0\<turnstile>All l are m" 
and "0\<turnstile>All q are l" 
and "0\<turnstile>All m are p" 
and "0\<turnstile>All n are p" 
and "0\<turnstile>All l are q"
shows "0\<turnstile> All q are p"

apply (rule_tac Y=l in A_barbara)
 apply (rule assms(2))
  
 apply (rule_tac Y=m in A_barbara)
  apply (rule_tac Y=m in A_barbara)
   apply (rule assms(1))

   apply (rule A_axiom)
  apply (rule assms(3))
done 

text {* Comparing the Isabelle proof with the paper proof, we see
that in Isabelle we reasoned backwards from the goal \pf{All q are p}. 
The first \pf{{\bf apply} \ep{rule-tac Y=l in A-barbara}}, for example, 
corresponds to the bottom application of the {\sc Barbara} rule. 
\marginpar[left text]{video}
*}

text {* \specialbox{ here it would be good to have an 
exercise for the reader } *}

text {* Later in the lecture notes we want to compare derivability from assumptions with 
semantic entailment, so we define $\Gamma\vdash\phi$ as a variation of 
the above $\vdash\phi$: *}

inductive derives :: "formula set \<Rightarrow> formula \<Rightarrow> bool" ("_ \<turnstile> _")
where
  A_assumption: "f \<in> hs \<Longrightarrow>  hs \<turnstile> f"
| A_axiom: "hs \<turnstile> (All X are X)"
| A_barbara: "\<lbrakk>hs \<turnstile>(All X are Y); hs \<turnstile>(All Y are Z)\<rbrakk> \<Longrightarrow> hs \<turnstile>(All X are Z)"
 
text {* Accordingly, we have the following variation of the above
example.
 *}

lemma example_2_5_b:
fixes l m n p q
defines "G_2_5  \<equiv> {All l are m,All q are l,All m are p,All n are p,All l are q}"
shows "G_2_5 \<turnstile> All q are p"
apply (rule_tac Y=l in A_barbara)
 apply (rule A_assumption) apply (simp add: G_2_5_def)
  apply (rule_tac Y=m in A_barbara)
    apply (rule_tac Y=m in A_barbara)
     apply (rule A_assumption) apply (simp add: G_2_5_def)

     apply (rule A_axiom)
    apply (rule A_assumption) apply (simp add: G_2_5_def)
done 

text {* The proof is similar to the first one, but instead of referring
to an assumption of the lemma, we use now the rule \pf{A-assumption}.
After applying the rule \pf{A-assumption}, Isabelle leaves us with a 
subgoal, namely
\pftext{ All q are l 
    $\in$ G-2-5 }
which is obviously true and easy to discharge by 
\pf{{\bf apply} \ep{simp add: G-2-5-def}}.
\footnote{A summary of rules is given in \cite[Section 5.7]{tutorial:isabellehol}.
Chapter 5 also contains a general introduction to the logic of Isabelle.}

\specialbox{ maybe a bit more about auto, simp, etc ... \cite[Section 3.1]{tutorial:isabellehol}}
*}

text {* 
Next we come to our first mathematical result on the calculus, namely
that it is sound. Recall that \pf{TYPE\ep{atProp}} is the unique element
of the type \pf{atProp itself}, which appears in the definition of $\models{}G$.
*}

lemma prop_2_2_1:
  fixes G g
  assumes "G \<turnstile> g"
  shows  "G \<Turnstile>G g (TYPE(atProp))"
using assms
proof (induct rule: derives.induct)
  case (A_assumption) 
  show ?case 
by (metis A_assumption.hyps M_satisfies_G_def entails_def)
next 
  case (A_axiom)
  show ?case by (metis entails_def order_refl satisfies.simps)
next
  case (A_barbara)
  show ?case by (metis A_barbara.hyps(2) A_barbara.hyps(4) entails_def satisfies.simps subset_trans)
qed


text {* To quote from the book: 
\begin{qcolor}The soundness proofs of all the logical systems in this book are all pretty much the same.    
They are always inductions, and the crux of the matter is usually a simple fact about sets.  
(Above, the crux of the matter is that the inclusion relation $\subseteq$ on 
 subsets of a given set is always a transitive relation.)
We almost never present the soundness proof in any detail.\end{qcolor}
The Isabelle proof gives another justification for skipping the details of the 
mathematical soundness proof: 
After telling Isabelle that we want to use induction and after 
listing the cases, the details of the
proof are done automatically using sledgehammer, that is, the three lines above 
\pf{{\bf by} \ep{metis \dots}} are provided
by an automatic theorem prover. For us, this essentially means that no
mathematical ideas are needed. 
%
\footnote{Although it is clear that with automatic theorem proving
becoming more and more powerful it will happen more  and more often that automatic provers will find 
proofs that would require ideas from a human point of view. On the other hand, for the proofs of 
this section, there is an astonishingly good match between the details one would hide in a 
pen and paper proof and the details that can be discharged by an automatic theorem prover.}
%

\medskip It may also be worth noting that the Isabelle proof is quite a bit shorter than the proof
in the book. Usually, such easy
proofs do not make it into the literature. Nowadays that can be done without sacrificing rigor by delegating
these proofs to a theorem prover. 
Moreover, checking all the cases using the tool may well be faster then 
checking the cases (carefully) by hand.
 *}

text {* \textbf{Further Reading. } Section 3 and 4 of \cite{Paulson89} contain 
an exposition of Isabelle's meta-logic and an example of an object logic.
*}

subsection {* Completeness --- Proofs in Isabelle/Isar *}

text {* Isabelle supports two styles of proof, apply-style and Isar-style.
We have seen an example of both. The proof for Example 2.5 was given
apply-style. This is very convenient for that type of problem, which
consists in finding a derivation in a calculus, the rules of which
have been directly encoded using Isabelle rules.

\medskip But the proof of the soundness result in Proposition 2.2.1 was written
in a very different style. As an exercise you might want to
try and do the soundness proof apply-style, starting with
\begin{verbatim}
  apply (rule derives.induct)
  apply (rule assms)
\end{verbatim} 
You will notice that you will need to know quite a bit about
how Isabelle proofs are implemented internally. Instead, the Isar proof language
\cite{isar} allows proofs to be written in a style much closer to informal proofs 
and is much quicker to learn. 
This section will present more examples and some exercises, for background and details 
see the introduction \cite{tutorial:isar}. A useful resource is also the
Isabelle/Isar reference manual \cite{isar}, in particular Appendix A.
*}

text {* Coming back to the development of the syntax and semantics of our logic,
it is the next 
definition which is the crucial one as it links up both syntax and semantics: 
Given a theory $G$, 
  derivability induces a preorder on atomic propositions, which is then
used to define the notion of canonical model below.  *}

definition less_equal_atprop :: "atProp \<Rightarrow> formula set \<Rightarrow> atProp \<Rightarrow> bool" ("_ \<lesssim>_ _")
where
  "less_equal_atprop u G v \<equiv> G \<turnstile> All u are v"

text {* We show that \isasymlesssim\ is a preorder. We would
hope that there is a theory about orders and preorders ready for us
to use and to find
it we write: *}

find_theorems name:preorder

text {* After which, in the output window, we find 
\begin{verbatim}
  Order_Relation.preorder_on_empty: preorder_on {} {}
\end{verbatim}
Pressing the command key, hovering over the line above and clicking without delay
brings up the theory \verb+Order_Relation+
and the definition of \verb+preorder_on+, which takes two arguments,
a set $A$ and a relation, ie, a subset of $A\times A$. The relation
in question is $\{(x,y) \mid x\; {\lesssim}G\; y\}$. The set on which this
relation lives can be given by using \pf{UNIV}.
\marginpar[left text]{video}
*}


lemma prop_2_4_1:
  fixes G 
  shows "preorder_on UNIV { (x,y). x \<lesssim>G y }"
proof (auto simp add: preorder_on_def)
   show "refl { (x,y). x \<lesssim>G y }" 
    unfolding refl_on_def
    using A_axiom by (metis UNIV_Times_UNIV case_prodI iso_tuple_UNIV_I less_equal_atprop_def mem_Collect_eq subset_iff)
  show "trans { (x,y). x \<lesssim>G y }" 
    unfolding trans_def
    using A_barbara by %invisible (metis (full_types) less_equal_atprop_def mem_Collect_eq split_conv)
qed
 
text {* As a side remark, the latex code of Proposition 2.4.1 and
its proof in the
book is only 10\% shorter, measured in number of characters, than the
Isabelle code (only part of which is shown above).
*}

text {* Next we give the definition of the canonical model of a theory $G$.
In words it says that in the canonical model 
the interpretation of the atomic proposition $u$
is the set of all atomic propositions smaller or equal to $u$. *}

definition "canonical_model G u \<equiv> { v. v \<lesssim>G u }"

text {* The next lemma confirms that the canonical model of $G$ 
satisfies $G$: *}

lemma lemma_2_4_2:
  fixes G assumes "M = canonical_model G"
  shows "M \<Turnstile>M G"
proof (auto simp add: M_satisfies_G_def)
  fix g  assume "g \<in> G"
  then obtain p q where "(All p are q) = g" by %invisible (metis formula.exhaust)

  then have "p \<lesssim>G q" using A_assumption by %invisible (metis (full_types) `g \<in> G` less_equal_atprop_def)

  then have "M p \<subseteq> M q" using A_barbara by %invisible (metis assms canonical_model_def less_equal_atprop_def mem_Collect_eq subsetI)

  thus "M \<Turnstile> g" by %invisible (metis `(All p are q) = g` satisfies.simps)

qed

text{* Next comes the completeness theorem. *}

lemma thm_2_4_3: 
  assumes "G \<Turnstile>G (All p are q) (TYPE(atProp))"
  shows "G \<turnstile> All p are q"
proof -
  define M where "M = canonical_model G"
  have "M \<Turnstile> All p are q" using lemma_2_4_2 by %invisible (metis (full_types) M_def assms entails_def)
  
  then have "M p \<subseteq> M q" by %invisible auto


  have "p \<lesssim>G p" using A_axiom by %invisible (metis less_equal_atprop_def)

  then have "p \<in> M p" using canonical_model_def by %invisible (metis M_def mem_Collect_eq)


  have "p \<in> M q" using `M p \<subseteq> M q` by %invisible (metis `p \<in> M p`  set_rev_mp)

  then have "p \<lesssim>G q" using canonical_model_def by %invisible (metis M_def  mem_Collect_eq)

  thus ?thesis by %invisible (metis less_equal_atprop_def)

qed

end