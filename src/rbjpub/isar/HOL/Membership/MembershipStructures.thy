header{* Membership Structures *}

theory MembershipStructures
imports Main
begin

text{*
$Id: MembershipStructures.thy,v 1.2 2006/11/09 12:23:05 rbj01 Exp $

First, type abbreviations are introduced for membership structures (i.e. interpretations of a set theory) and for properties of membership structures (the kind of thing expressed by an axiom of set theory).

Normally a membership structure is considered as a set with a binary relation.
However, there is in most cases some redundancy in this, since the set is the field of the relatioin, and can be recovered from it.
In informal mathematics this is of no consequence, but in formal mathematics redundancy causes clutter.
The cases where the set is not the same as the field of the relationship are sufficiently strange that, (like the possibility of an empty domain in a first order interpretation) it is unlikely to be of interest in practice and it is worthwhile to exclude it.

I therefore begin with a notion of membership structure in which there may be no isolated elements and which therefore can be represented simply by the relation, and this theory therefore begins as an extension to the theory of relations.
*}

types
  'a MS = "('a \<times> 'a)set"
  'a PMS = "'a MS \<Rightarrow> bool"

subsection{* Extensionality *}

text{*
We will normally be working with extensional relationships.
In that case the extension of a set is usually all we need to know about it, and an extension suffices to identify a set.
We therefore define two functions which will normally provide an injection from sets into extensions, connecting sethood in some membership structure with Isabelle HOL sethood.
The main purpose of this is to enable us to use the set theoretic language already available to us while talking about a different kind of set.
*}

constdefs
  Ex :: "'a MS \<Rightarrow> 'a \<Rightarrow> ('a set)"
  "Ex r x == {y . (y,x):r}"

  Co :: "'a MS \<Rightarrow> ('a set) \<Rightarrow> 'a"
  "Co r s == (THE x. x:Field r \<and> Ex r x = s)"

text{*
My concern here is exclusively with extensional concepts of set, extensionality being considered in some circles the quintessence of sethood.
There are non-extensional set theories but they will not be investigated here,

Though our representation for membership structures excludes isolated elements, it does not rule out urelements, but a full axiom of extensionality would rule out urelements with no elements (though not ``Quine atoms'' (and possibly other schemes).
Though in principle NFU could be done within this framework, in practice this would be awkward, and it would complicate the development unduly to organised the work in a manner sympathetic to NFU.
I therefore propose to confine this study to fully extensional structures.

Full extensionality is defined as follows.
*}

constdefs
   FullExt :: "'a PMS"
     "FullExt ms == ALL x y. x:(Field ms) \<and> y:(Field ms)
     \<longrightarrow> (ALL z. (z, x):ms = ((z,y):ms)) \<longrightarrow> x = y"


lemma FullExt1: "\<lbrakk>FullExt ms; x:(Field ms); y:(Field ms); (ALL z. (z, x):ms = ((z,y):ms))\<rbrakk> \<Longrightarrow> x = y"
apply (simp add:FullExt_def)
done

subsection{* *}

locale ExtMs =

fixes
    mr :: "('a * 'a)set"

assumes
  FullExt: "FullExt ms"

lemma "A \<longrightarrow> A"
proof
assume A
show A .
qed


text{*
\ignore{
lemma (in ExtMs) ExtMs1 : "\<lbrakk>x:(Field mr); y:(Field mr); (ALL z. (z, x):mr = ((z,y):mr))\<rbrakk> \<Longrightarrow> x = y"

lemma (in ExtMs) ExCo_inv :"ALL x. x : Field ms \<longrightarrow> Co ms (Ex ms x) = x"
apply (simp add:Ex_def Co_def)
apply auto
apply (rule the_equality)
apply simp
apply (rule FullExt1)
assume "xa \<in> Field ms"
show 
qed
apply (rule FullExt)
}
*}


text{*
*}

end
