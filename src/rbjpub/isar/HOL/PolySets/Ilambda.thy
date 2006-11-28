header{*An Illative Lambda Calculus*}

theory Ilambda
imports PolySets
begin

text{*
The theory \emph{Ilambda}
\footnote{$ $Id: Ilambda.thy,v 1.1 2006/11/28 16:50:49 rbj01 Exp $ $}
is intended to provide an ``illative lambda-calculus" based on the PolySets, i,e, in which the values of expressions are PolySets.

This is an exploratory theory, by which I mean that I don't really know how its going to work out.
*}

subsection{*Desiderata*}

text{*
The single most important thing I want to explore here is the conjecture that the functions definable as patterns include the polymorphic functions definable in a language similar to ML.

This question will be explored as a part of conisideration of how one might devise a logical system based on PolySets which is a compromise between the flexibility of the ML type system and the power of the HOL logic.

The main feature common to both these systems is that they are essentially functional rather than set theoretic, and therefore that the primary primitive constructor is the operation of function application rather than the predicate of set membership.
A second feature which distinguishes these systems from PolySet \emph{theory} is that they are neither of them first order theories.
HOL is the transformation of the typed lambda-calculus into a logical system rather than the development of the theory of the lambda-calculus in some other logic,
ML is the adoption of a congenial syntax for something which under the surface might be thought of as a lambda-calculus.

In a similar manner it is intended here to pave the way for leaving behind HOL and using the PolySet dressed in more functional syntax as a logical system in its own right.

Calling this an \emph{illative} lambda-calculus refers back to the use of that term in combinatory logic.
In that context, the \emph{pure} combinatory logic is the calculus of functions based usually on the combinatory S,K and I but absent constants corresponding to logical operators.
To turn this into a logical system suitable for use as a foundation for mathematics it is necessary to add one or more operators such as equality, universal quantification, or restricted quantification.
When that is done it is called an \emph{illative} combinatory logic.

One feature which illative combinatory logics and ML share but in which they differ from HOL is in the role of types.
In the former two system types are properties of terms, a term may have many types, but the types are not constituents of or decorations on terms or their constituents.
In HOL types are part of the syntax of terms and each term has a single type.

This distinction is important in understanding what happens in local definitions (which we will be concerned with) and of some ways of providing structure in the large (which are also of concern but will not here consider).
In HOL a polymorphic object is semantically a family of monotypical objects.
No function takes a polymorphic value, a polymorphic function is a family of functions each taking an argument whose type is some monotypical instance of the polymorphic type of its argument.
This means that you cannot instantiate the types of the formal parameters in the body of a functional abstraction.
If a let clause is explained in terms of a lambda-abstraction, then a polymorphic function defined by the let clause cannot be instantiated in the body of the clause,
*}

subsection{*Primitive Operators*}

text{*
Rather than looking at syntax, I begin by looking at the semantics of plausible primitive operations.
*}

subsubsection{*Application and Abstraction*}

text{*
The first things we need in a lambda-calculus are of course application and abstraction.

The only issue for abstraction is what value it should have if the operator is not a function with the operand in its domain.
I would like, in the first instance to adopt a notion of application shich is defined provided only that the operator is single valued at the particular value denoted by the operand and whose value is otherwise undetermined (but is nevertheless some PolySet).
In Isabelle-HOL I think I can only do this using the choice function:

Abstraction is defined similarity, via @{term C\<^isub>p}, so that an abstraction denotes the appropriate function only if that function exists, which needs to be proven.
Note that abstraction takes place always over some set declared to be the domain of the abstraction.
This is a half way house between the typed abstract in HOL and the untyped abstraction in ML and combinatory logics.
You can declare the domain as the universal set V (not yet defined) but we will see that there are severe constraints on the kind of functions over V which exist.
*}

constdefs
   PsApply :: "pset \<Rightarrow> pset \<Rightarrow> pset" (infixl ".\<^isub>p" 70)
      "PsApply == SOME ap::pset \<Rightarrow> pset \<Rightarrow> pset. \<forall> f a r. ap f a = r \<longrightarrow>
                  Wkp\<^isub>p(a,r) \<in>\<^isub>p f \<or> \<not> (\<exists>v. \<forall>w. Wkp\<^isub>p(a,w) \<in>\<^isub>p f = (w = v))"

   PsAbs :: "pset \<Rightarrow> (pset \<Rightarrow> pset) \<Rightarrow> pset"
      "PsAbs d f == C\<^isub>p {Wkp\<^isub>p(a,r) | a r. r = f a \<and> a \<in>\<^isub>p d}"

text{*

*}

end
