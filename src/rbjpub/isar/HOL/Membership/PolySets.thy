header{*PolySets*}

theory PolySets
imports MembershipStructures
begin

text{* $Id: PolySets.thy,v 1.1 2006/11/09 12:05:24 rbj01 Exp $ *}

types
  'a MS = "'a set * ('a \<Rightarrow> 'a \<Rightarrow> bool)"
  'a PMS = "'a MS \<Rightarrow> bool"

text{*
We will normally be working with extensional relationships.
In that case the extension of a set is usually all we need to know about it, and an extension suffices to identify a set.
We therefore define two functions which will normally provide an injection from sets into extensions, connecting sethood in some membership structure with Isabelle HOL sethood.
The main purpose of this is to enable us to use the set theoretic language already available to us while talking about a different kind of set.
*}

consts
  Ex :: "'a MS \<Rightarrow> 'a \<Rightarrow> 'a set"
  Co :: "'a MS \<Rightarrow> 'a set \<Rightarrow> 'a"

primrec
  "Ex (X,r) x = {y . x:X \<and> y:X \<and> r x y}"
primrec
  "Co (X,r) s = (THE x. Ex (X,r) x = s)"


subsection{* *}

text{*
*}



end
