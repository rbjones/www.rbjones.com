header{*The Construction of PolySets*}

theory PolySetsC
imports Sets
begin

text{*
The theory \emph{PolySetsC}
\footnote{$ $Id: PolySetsC.thy,v 1.1 2006/11/17 14:57:38 rbj01 Exp $ $}
first provides a construction of a model of a set theory with a universal set (a membership relation) by construction from some other membership relation and then proceeds to establish properties of the model suitable for use in a higher order axiomatisation.

It is one of several approaches to the formalisation of this topic which I am exploring.
This particular variant begins from an axiomatisation of a well-founded set theory in the theory `Sets'.

The first stage is to construct the PolySet ordinals for which purpose we need an ordered pair constructor.
*}

subsection{* Well-Founded Poly-Sets and Poly-Set Ordinals *}

text{*
There is an injection from the well-founded sets into the PolySets.
The set we are about to define is the image under that injection of the Von Neumann ordinals.
The injection is defined first.
*}

consts wf_polyset :: "Set \<Rightarrow> Set" 
recdef wf_polyset "{(x,y). x \<in>\<^isub>g y}"
   "wf_polyset s = (if (s = zero)
                   then zero
                   else (Wkp(zero, Co (image wf_polyset {x . x \<in>\<^isub>g s}))))"
(hints recdef_wf: wf)

text{*
The definitions of the well-founded and ordinal polysets are then:
*}

constdefs
   wf_polysets :: "Set set"
      "wf_polysets == image wf_polyset UNIV"
   polyset_ords :: "Set set"
      "polyset_ords == image wf_polyset ordinals"

text{*
Not sure whether these are of any value.
*}

constdefs
  mem_restr :: "Set set \<Rightarrow> (Set * Set)set"
          "mem_restr s == {(x,y) . x \<in> s \<and> y \<in> s \<and> x \<in>\<^isub>g y}"

text{*
The operation of subtraction on the left for ordinals (from \emph{Sets.thy}) must now be transferred to operate on PolySet ordinals.
*}

constdefs
   ps_olminus :: "Set \<Rightarrow> Set \<Rightarrow> Set" (infixr "{\<parallel>-}" 60)
      "ps_olminus x y == (THE z. \<exists>v w. x = wf_polyset v
                                   \<and> y = wf_polyset w
                                   \<and> z = wf_polyset (v {|-} w))"

subsection{* PolySets *}

text{*
The PolySets are now definable inductively.
First the constructor for PolySets is defined, then the PolySets are defined as the set of PolySets obtainable from the empty set by this constructor.

In fact, the polyset constructor is just the ordered pair constructor, and I don't think we really need another name for it.
*}

consts
  polysets :: "Set set"
inductive "polysets"
intros
  zPsI[intro!]: "zero : polysets"
   PsI[intro!]: "(\<forall> ord s.
                 ord \<in> polyset_ords
               \<and> (\<forall>w. w \<in>\<^isub>g s \<longrightarrow> s : polysets))
               \<Longrightarrow> Wkp(ords, s) \<in> polysets"

subsection{* Pattern Instantiation *}

text{*
The PolySets are patterns, in which the ordinals are instantiable pattern variables.
The key element in defining the membership relation over the PolySets is the specification of when a PolySet conforms to a pattern.
It does do of course, when the pattern can be instantiated according to some assignment of values to the pattern variables, to give the required PolySet.
I therefore begin with the definition of this process of instantiation, after which the definition of membership will be straightforward,
*}

text{*
Pattern instantiation is defined by transfinite recursion over the PolySets.
The well-founded relation with respect to which the recursion is well-founded is not the intended membership relation over the PolySets, but the membership relation from the theory \emph{Sets}.

The function we require here is total over the intended domains, which are subsets of unspecified types.
Our logic is a logic of total functions, and so we have to define instantiation not as a function but as a relation (which will be many one over the target domain).

A PolySet valuation for an ordinal in the PolySets is a (HOL, total) function which maps the PolySet ordinals less than the given ordinal to PolySets.
It doesn't matter what it does elsewhere.
*}

constdefs
   wfps_mem :: "Set \<Rightarrow> Set \<Rightarrow> bool" (infix "\<in>\<^isub>r" 70)
      "wfps_mem o1 o2 == o1 \<in>\<^isub>g Snd o2"

   is_ps_val :: "Set * (Set \<Rightarrow> Set) \<Rightarrow> bool"
      "is_ps_val == \<lambda> (ord, va). 
            ord \<in> polyset_ords
          \<and> (\<forall> o2. o2 \<in>\<^isub>r ord \<longrightarrow> (va o2) \<in> polysets)"

consts
   ps_instantiate :: "Set \<Rightarrow> (Set \<Rightarrow> Set) \<Rightarrow> (Set * Set)set"
inductive
   "ps_instantiate ord va"
intros
   vPsInI : "o2 \<in>\<^isub>r ord
            \<Longrightarrow> (o2, va o2) : ps_instantiate ord va"
   oPsInI : "o1 \<in> polyset_ords
            \<Longrightarrow> \<not> (wfps_mem o1 ord)
            \<Longrightarrow> (o1, ord {\<parallel>-} o1) : ps_instantiate ord va"
   sPsInI : "\<not> s \<in> polyset_ords \<and> t \<in> polysets
             \<and> ord2 = Fst s \<and> ord2 = Fst t
             \<and> (\<exists>r. r \<subseteq> ps_instantiate ord va
               \<and> single_valued r
               \<and> Domain r = X\<^isub>g(Snd s)
               \<and> t = Co (Range r))
             \<Longrightarrow> (s,t): ps_instantiate ord va"
monos subset_mono

constdefs
  ps_inst :: "Set * (Set \<Rightarrow> Set) \<Rightarrow> Set \<Rightarrow> Set"
     "ps_inst == \<lambda>(ord, va) ps. THE x. (ps,x) \<in>  ps_instantiate ord va"


subsection{* Membership *}

text{*
Membership is now defined as follows.
Nothing is a member of the empty set.
If the left element of a PolySet is the empty set, then there are no free variables in the right hand side, and the members of the PolySet are the members of the set on the right.
If the left element is not the empty set then it will be a PolySet ordinal which is the set of free variables which may occur in patterns on the right.
Each member of the set on the right is a pattern and a set is a member of the PolySet if there is a valuation for the free variables and an element (pattern) of the set on the right such that the set results when the pattern is instantiated using the valuation.
*}

constdefs
  ps_mem :: "Set \<Rightarrow> Set \<Rightarrow> bool"
     "ps_mem s t == (if t = zero
                     then False
                     else (if Fst t = zero
                           then s \<in>\<^isub>g Snd t
                           else (\<exists>va u. is_ps_val (Fst t, va)
                                 \<and> (u,s) \<in> ps_instantiate (Fst t) va )))"


subsection{* Extensionality *}

text{*
The membership structure consisting of the relation \emph{ps\_mem} over the set \emph{polysets} is not extensional.
For example, no polyset with rhs the empty set has any members, but there are as many such polysets as the ordinals in type \emph{Set}.
Also, for every polyset with a non-empty rhs, there are extensionally equivalent polysets obtained by permuting the names of the free variables, or by adding extra unused variables.

We can recover extensionality by taking a quotient with resepect to the smallest equivalence relattionship relative to which the induced membership relationship is extensional.
There must be one such quotient, since taking all polysets as equivalent yields a trivially extensional relationship. 

We obtain the relationship by a (transfinite) inductive definition.

It is convenient to define first the extension (as a \emph{Set set}) of a polyset.
*}

constdefs
  X\<^isub>r :: "Set \<Rightarrow> Set set"
     "X\<^isub>r t == {s. ps_mem s t}" 

text{*
To make it obvious that the following constructor is monotonic, the reference to the inductive set is packaged up as follows:
*}

constdefs
  eqsubset :: "Set \<Rightarrow>  Set \<Rightarrow> (Set * Set)set \<Rightarrow> bool"
     "eqsubset s t r == (X\<^isub>r s) \<subseteq> (r `` (X\<^isub>r t))"

text{*
Monotonicity is then proven.
*}

lemma eqsubset_mono: "A \<subseteq> B \<Longrightarrow> eqsubset s t A \<longrightarrow> eqsubset s t B"
by (simp add:eqsubset_def, blast)

text{*
Now the equivalence relation.
*}

consts
  ps_equiv :: "(Set * Set)set"
inductive
  ps_equiv
intros
  pseI[intro!]: "s:polysets \<and> t:polysets
         \<and> eqsubset s t ps_equiv
         \<and> eqsubset t s ps_equiv
         \<Longrightarrow> (s,t):ps_equiv"
monos eqsubset_mono

lemma refl_ps_equiv : "refl polysets ps_equiv"
apply (unfold refl_def)
apply auto
oops

lemma equiv_ps_equiv : "equiv polysets ps_equiv"
oops

text{*
Now that we have the equivalence relation we can take a quotient and lift the membership relationship up to the quotient classes.
The membership structure $(ps\_eqc, pseqc\_mem)$ will provide the representation for the new type of PolySets.
*}

constdefs
   ps_eqc :: "Set set set"
      "ps_eqc == polysets // ps_equiv"
   pseqc_mem :: "Set set \<Rightarrow> Set set \<Rightarrow> bool"
      "pseqc_mem s t == \<exists>v w. v \<in> s \<and> w \<in> t \<and> ps_mem v w"
   pseqc :: "Set \<Rightarrow> Set set"
      "pseqc s == ps_equiv `` {s}"

lemma zero_ps_eqc: "pseqc zero \<in> ps_eqc"
apply (unfold pseqc_def ps_eqc_def)
apply (rule quotientI, auto)
done

end

