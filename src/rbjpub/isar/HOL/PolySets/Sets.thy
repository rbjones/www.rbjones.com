header{* Pure Well-Founded Sets *}

theory Sets
imports Main
begin

text{*
The theory \emph{Sets}\footnote{$ $Id: Sets.thy,v 1.2 2006/11/28 16:50:49 rbj01 Exp $ $} is a bare-boned set theory in Isabelle-HOL intended only to permit a transparent presentation of the Poly-Sets.
I did at first attempt the construction without axiomatising a particular set theory, so that the poly-sets could be built from an arbitrary membership structure with suitable properties, but the advantages of this are overwhelmed by the extra complexity it causes, and I have concluded that maximising the intelligibility of the poly-sets (and of further constructions based on them) is incompatible with the innovation of treating set theory as a theory \emph{about} membership structures, rather than a theory about the sets in \emph{in} one such structure,

The reader should beware that what follows is an axiomatic set theory presented in the context of a Higher Order Logic which has its own set theoretic vocabulary.
It is convenient to make use of that vocabulary, and so two notions of set and membership should be distinguished.
The extant set theory is that of elements of type \emph{set} and uses the usual set membership predicate $\in$.
All of the standard set theoretic symbols belong to this theory.
The new set theory is axiomatised in type \emph{Set} and uses the (not very nice) operator $\verb!\in_g!$ for membership.

For the sake of keeping down culture shock the axioms are theorems rather than rules.
Working in Isabelle higher-order rules (which provide something like a sequent calculus) are more convenient and will be derived as needed.
*}

subsection{* Extensionality and Well-Foundedness *}

text{*

Extensionality and Well-Foundedness express constraints on the notion of set.
They constrain the sets to be the pure well-founded sets.

Well foundedness is expressed as an induction principle.
This is stronger than the first order axiom of regularity, though in the context of higher order replacement (which appears later) the difference disappears.

As it happens, we may not need it anyway, since the poly-set construction which follows naturally extracts a subset of the well-founded sets, leaving behind any non-well-founded sets.

Nor is it certain that we need an extensional set theory as our starting point.
The construction yields in the first instance a non-extensional model, which is made extensional by taking a quotient, so it might well work if it is non-extensional all the way up to that final oeration.
Since the question of how weak our starting point might possibly have been is not of much wieght, it is preferred to keep things simple by starting from a cery standard model of the pure-well-founded sets.

*}

typedecl Set

consts mem :: "Set \<Rightarrow> Set \<Rightarrow> bool" (infix "\<in>\<^isub>g" 80)

axioms
   Ext: "\<forall> x (y::Set). (x = y) = (\<forall>z::Set. z \<in>\<^isub>g x = z \<in>\<^isub>g y)"

   Wf:  "\<forall>P. (\<forall>s. (\<forall>t. t \<in>\<^isub>g s \<longrightarrow> P t) \<longrightarrow> P s) \<longrightarrow> (\<forall>u. P u)"

text{*
The axiom \emph{Wf} is related to the definition of the predicate \emph{wf} in theory \emph{WellFounded\_recursion}.
The latter is a property of relations while \emph{Wf} is simply a sentence (which distinguishes the set of relations which satisfy it),
The following lemma connects the property with the axiom, and will be used to justify recursive definitions.
*}

lemma wf: "wf {(x,y). x \<in>\<^isub>g y}"
apply (simp add: wf_def)
apply (rule Wf)
done

subsection{* Closure *}

text{*

Having tied down what kind of thing a set is, the final axiom tells us that there are many of them. 
It says that every set is a member of a ``galaxy'' (\emph{Gy}) which is the kind of thing which most people call a universe.
The empty set and the hereditarily finite sets are galaxies, and the next one is a model of ZFC.
(Note that we inherit choice from our context)
Galaxies are closed under full power-set, sumset and replacement.
The universe is also closed under replacement (you don't have to show that the image of a set is a subset of a galaxy for it to be a set, though it won't otherwise be a member of the galaxy).

I hope that it makes things easier to read if the available set theoretic vocabulary is used, and to that end define a constant $X_g$ which gives the extension of a \emph{Set} as a \emph{set} of Sets.
*}

constdefs
  X\<^isub>g :: "Set \<Rightarrow> Set set"
     "X\<^isub>g x == {y . y \<in>\<^isub>g x}"

  Gy :: "Set \<Rightarrow> bool"
     "Gy g == (\<forall>x. x \<in> X\<^isub>g g \<longrightarrow>
              (\<exists>y. y \<in> X\<^isub>g g \<and> X\<^isub>g y = \<Union>{z. \<exists>v. v \<in>\<^isub>g x \<and> z = X\<^isub>g v})
           \<and> (\<forall>x. x \<in> X\<^isub>g g \<longrightarrow> (\<exists>y. y \<in> X\<^isub>g g \<and> X\<^isub>g y = {z . X\<^isub>g z \<subseteq> X\<^isub>g x}))
           \<and> (\<forall>r::(Set * Set)set. single_valued r
                   \<longrightarrow> (\<exists>y. X\<^isub>g y = r `` (X\<^isub>g x) \<and> ((X\<^isub>g y) \<subseteq> (X\<^isub>g g) \<longrightarrow> y \<in> X\<^isub>g g))))"

lemma ext_xt [simp]: "X\<^isub>g x = X\<^isub>g y \<Longrightarrow> x = y"
apply (unfold X\<^isub>g_def)
apply (simp add:Ext)
apply auto
done

text{*
Having thus defined a galaxy as a set closed under distributed union, power set and replacement, the final axiom states that every set is a member of a galaxy.

The existence of glaxies will I hope be helpful in overcoming awkwarndesses which might arise in working with the well-founded poly-sets from the presence of non-well-founded poly-sets.
Though the domain as a whole is not much like a model of ZFC, we have pleanty of things around which are like that.
*}

axioms
   G: "\<forall>s. \<exists>t. s \<in>\<^isub>g t \<and> Gy t"

text{*
These two definitions may be useful in defining operators or in expressing closure properties.
The first expresses the existence of a set with some extension, the second designates the set with some extension.
*}

constdefs

  E\<^isub>g :: "Set set \<Rightarrow> bool"
     "E\<^isub>g ss == \<exists>s. X\<^isub>g s = ss"
 
  C\<^isub>g :: "Set set \<Rightarrow> Set"
     "C\<^isub>g s == (THE x. X\<^isub>g x = s)"

  XX\<^isub>g :: "Set \<Rightarrow> Set set set"
     "XX\<^isub>g s == {x. \<exists>y. y \<in>\<^isub>g s \<and> x = X\<^isub>g y}"

lemma C\<^isub>gX\<^isub>g [simp]:
   "\<forall>s. C\<^isub>g(X\<^isub>g s) = s"
apply (simp add: C\<^isub>g_def X\<^isub>g_def)
apply (rule allI) 
apply (rule the_equality, auto)
apply (simp add:Ext, auto)
done

lemma E\<^isub>gC\<^isub>g [simp]:
   "E\<^isub>g s \<Longrightarrow> X\<^isub>g (C\<^isub>g s) = s"
apply (unfold E\<^isub>g_def C\<^isub>g_def)
apply (erule exE)
apply (subgoal_tac "(THE x. X\<^isub>g x = s) = sa")
apply auto
done

subsection{* Pairs *}

text{*
The constructor for Wiener-Kuratowski ordered pairs is defined here,
It remains to be established whether pairs always exist.
*}

constdefs
   Wkp :: "(Set * Set) \<Rightarrow> Set"
      "Wkp == \<lambda>(x,y). C\<^isub>g{C\<^isub>g{x},C\<^isub>g{x,y}}"

   Fst :: "Set \<Rightarrow> Set"
      "Fst s == THE x. \<exists>y. s = Wkp(x,y)"

   Snd :: "Set \<Rightarrow> Set"
      "Snd s == THE y. \<exists>x. s = Wkp(x,y)"

subsection{* Ordinals *}

text{*
The ordinals are defined in Jech \cite{jech2000} as those sets which are transitive and well-ordered by membership.
However, I think I might get more milage from a recursive definition of ordinals so that's what I'll do.

First I define zero, the sucessor relationship, the limit of a set of ordinals and the predecessor of a successor ordinal.
The last two are just set union (notionally restricted to appropriate sets of ordinals).
*}

constdefs
  zero  :: "Set"
     "zero == C\<^isub>g {}"

  succ  :: "Set \<Rightarrow> Set"
     "succ s == C\<^isub>g (X\<^isub>g s \<union> {s})"

  SetUnion :: "Set \<Rightarrow> Set" 
     "SetUnion s == C\<^isub>g (\<Union>{x. \<exists>y. y \<in>\<^isub>g s \<and> x = X\<^isub>g y})"

  limit :: "Set \<Rightarrow> Set"
     "limit == SetUnion"

  pred  :: "Set \<Rightarrow> Set"
     "pred == SetUnion"

text{*
The ordinals are now defined inductively.
This probably isn't the simplest definition of ordinal, but it might be the one most directly related to our intuition about what a Von Neumann ordinal is.
*}

consts
   ordinals:: "Set set"
inductive ordinals
intros
   zoI[intro!]: "zero \<in> ordinals"
   soI[intro!]: "x \<in> ordinals \<Longrightarrow> succ x \<in> ordinals"
   loI[intro!]: "\<forall>t. t \<in>\<^isub>g s \<longrightarrow> t \<in> ordinals \<Longrightarrow> limit s \<in> ordinals" 

constdefs
   Ordinal:: "Set \<Rightarrow> bool"
   "Ordinal s == s \<in> ordinals"

text{*
We will need to subtract ordinals on the left.
Addition is defined first.
Since the ordinals are not a type this is more awkward that it would otherwise be,
I couldn't get the definition by recursion through isabelle so I ended up using an inductive set definition.
*}

lemma subset_mono:
   "A \<subseteq> B \<Longrightarrow>  x \<subseteq> A \<longrightarrow> x \<subseteq> B"
by auto

consts
   oplusx :: "Set \<Rightarrow> (Set * Set) set"
inductive
   "oplusx x"
intros
   azI: "y = zero \<Longrightarrow> (y,x) \<in> (oplusx x)"
   asI: "y = succ v \<Longrightarrow> (v,z) \<in> oplusx x \<Longrightarrow> (y, succ z) \<in> oplusx x"
   alI: "y = limit s
             \<Longrightarrow> (\<exists>r. r \<subseteq> oplusx x
                   \<and> single_valued r
                   \<and> Domain r = X\<^isub>g s
                   \<and> z = limit (C\<^isub>g (Range r)))
             \<Longrightarrow> (y,z) \<in> oplusx x"
monos subset_mono

constdefs
   oplus ::   "Set \<Rightarrow> Set \<Rightarrow> Set" (infixl "{+}" 60)
      "oplus x y == THE z. (y,z) \<in> (oplusx x)"

   olminus :: "Set \<Rightarrow> Set \<Rightarrow> Set" (infixr "{|-}" 60)
      "olminus x y == THE z. y = x {+} z"

end