header{*PolySets*}

theory PolySets
imports MembershipStructures
begin

text{*
The theory \emph{PolySets}
\footnote{$ $Id: PolySets.thy,v 1.2 2006/11/13 07:12:37 rbj01 Exp $ $}
first provides a construction of a model of a set theory with a universal set (a membership relation) by construction from some other membership relation and then proceeds to establish properties of the model suitable for use in a higher order axiomatisation.

My first thought was to establish, in the theory \emph{MembershipStructures}, locales for well-founded extensional membership structures with sufficient other properties to yield under the construction a domain with the required properties.
However, I find that the locales are not as helpful as I hoped.
The assumption of well-foundedness does not facilitate the use of transfinite induction in the construction, since the definitional facilities available in locales are too limited.

The construction is therefore defined relative to an arbitrary membership structure, and the properties of the original membership structure are considered only after the construction when they are required to deduce desirable properties of the resulting model.

The first stage is to construct the PolySet ordinals for which purpose we need an ordered pair constructor.
*}

subsection{* Pairs *}

text{*
Pairs and ordered pairs are defined as relationships over an arbitrary binary relationship.
This does not mean that a representation is chosen which works in any relation.
The representation is the usual Wiener-Kuratovski construction $(x,y) = \{x, \{x,y\}\}$, and the relationship we define tells us whether one element is an ordered pair of two others, without prejudging or depending whether such pairs in fact exist in any given relationship. 
*}

constdefs
  Wkp :: "'a MS \<Rightarrow> ('a * 'a) \<Rightarrow> 'a \<Rightarrow> bool"
   "Wkp ms == \<lambda>(x,y) z. \<exists> v. Ext ms v = {x,y} \<and> Ext ms z = {x,v}"

subsection{* PolySet Ordinals *}

text{*
There is an injection from the well-founded sets into the PolySets.
The set we are about to define is the image under that injection of the Von Neumann ordinals (the injection is not itself defined).

This is done by defining the successor function, and then the intersection of the sets which contain the empty set and are closed under taking the strict supremum of a set of ordinals.

The set defined will be well-ordered by PolySet membership (to be defined) if there is exactly one zero in the original relationship.
Otherwise it will either be the empty set or the universal set.
*}

constdefs 
  Zero :: "'a MS \<Rightarrow> 'a \<Rightarrow> bool"
          "Zero ms x == x \<in> Field ms \<and> Ext ms x = {}" 
  Succ :: "'a MS \<Rightarrow> 'a  \<Rightarrow> 'a \<Rightarrow> bool"
          "Succ ms x y == \<exists> v w. Wkp ms (v,w) y \<and> Zero ms v \<and> Ext ms w = (Ext ms x) \<union> {x}"
  UnionSuccs :: "'a MS \<Rightarrow> 'a set \<Rightarrow> 'a \<Rightarrow> bool"
          "UnionSuccs ms s t == Ext ms t = {u . (\<exists> v w. v \<in> s \<and> (w,v) \<in> ms \<and> Succ ms w u)}"

consts PolySetOrds :: "'a MS \<Rightarrow> 'a set"
inductive "PolySetOrds ms"
intros  
   zPsoI : "Zero ms z \<Longrightarrow> z: PolySetOrds ms"
    PsoI : "(\<forall>psos. UnionSuccs ms psos pso
                 \<and> (\<forall>y. y \<in> psos \<longrightarrow> y: PolySetOrds ms))
            \<Longrightarrow> pso: PolySetOrds ms"

constdefs
  RelRestr :: "'a MS \<Rightarrow> 'a set \<Rightarrow> 'a MS"
          "RelRestr ms s == {(x,y) . x \<in> s \<and> y \<in> s \<and> (x,y) \<in> ms}"
  PolySetOrdMs :: "'a MS \<Rightarrow> 'a MS"
          "PolySetOrdMs ms == RelRestr ms (PolySetOrds ms)"


subsection{* PolySets *}

text{*
The PolySets are now definable inductively.
*}

constdefs
  MakePolySet:: "'a MS \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
           "MakePolySet ms ord pss ps == ord \<in> (PolySetOrds ms) \<and> Wkp ms (ord, pss) ps"

consts
  PolySets :: "'a MS \<Rightarrow> 'a set"
inductive "PolySets ms"
intros
  zPsI: "Zero ms z \<Longrightarrow> z : PolySets ms"
   PsI: "(\<forall> t ord u.
                 ord \<in> (PolySetOrds ms)
               \<and> (Ext ms u = t)
               \<and> MakePolySet ms ord u v
               \<and> (\<forall>w. w \<in> t \<longrightarrow> w : PolySets ms))
               \<Longrightarrow> v \<in> PolySets ms"

subsection{* Membership *}

text{*
The PolySets are patterns, in which the ordinals are instantiable pattern variables.
The key element in defining the membership relation over the PolySets is the specification of when a PolySet conforms to a pattern.
It does do of course, when the pattern can be instantiated according to some assignment of values to the pattern variables, to give the required PolySet.
I therefore begin with the definition of this process of instantiation, after which the definition of membership will be straightforward,
*}

subsubsection{* Pattern Instantiation *}

text{*
Pattern instantiation is defined by transfinite recursion over the PolySets.
The well-founded relation with respect to which the recursion is well-founded is not the intended membership relation over the PolySets, but the presumed membership relation from which the PolySets are constructed.
Though this need not itself be well-founded, its restriction to the PolySets is.

The function we require here is total over the intended domains, which are subsets of unspecified types.
Our logic is a logic of total functions, and so we have to define instantiation not as a function but as a relation (which will be many one over the target domain).

A PolySet valuation for an ordinal in the PolySets derived from some membership structure is a (HOL, total) function which maps the PolySet ordinals less than the given ordinal to PolySets.
It doesn't matter what it does elsewhere.
*}

constdefs
   PsOrdLt :: "'a MS \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
      "PsOrdLt ms o1 o2 ==
            o1 \<in> PolySetOrds ms
          \<and> o2 \<in> PolySetOrds ms
          \<and> (\<exists> so z. Zero ms z
          \<and> (o1, so) \<in> ms
          \<and> MakePolySet ms z so o2)"

   isPsValuation :: "'a MS \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
      "isPsValuation ms ord va ==
            ord \<in> PolySetOrds ms
          \<and> (\<forall> o2. PsOrdLt ms o2 ord \<longrightarrow> (va o2) \<in> PolySets ms)"


consts
   PolySetInstantiate :: "'a MS \<Rightarrow> 'a \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a * 'a) set"
   PsOrdAdd :: "'a MS \<Rightarrow> ('a * 'a) \<Rightarrow> 'a \<Rightarrow> bool"

inductive
   "PolySetInstantiate ms ord va"
intros
   zPsInI : "Zero ms z
            \<Longrightarrow> (ord, z) : PolySetInstantiate ms ord va" 
   vPsInI : "PsOrdLt ms o2 ord
            \<Longrightarrow> (o2, va o2) : PolySetInstantiate ms ord va" 
   oPsInI : "o1 \<in> PolySetOrds ms
             \<and> \<not> PsOrdLt ms o1 ord
             \<and> PsOrdAdd ms (ord,o2) o1
             \<Longrightarrow> (o1, o2) : PolySetInstantiate ms ord va"

text{*
\begin{verbatim}
   sPsInI : "\<not> s \<in> PolySetOrds ms
             \<and> MakePolySet ms or sps1 s
             \<and> MakePolySet ms or sps2 t
             \<and> (\<forall>ps2. (ps2,sps2) \<in> ms
               = (\<exists>ps1. (ps1,sps1) \<in> ms \<and> (ps1, ps2) \<in> PolySetInstantiate ms ord va))
             \<Longrightarrow> (s,t): PolySetInstantiate ms ord va"

\end{verbatim}
*}

end
