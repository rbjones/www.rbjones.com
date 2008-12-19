(*  Title:      HOL/PreOrders.thy
    ID:         $Id: PreOrders.thy,v 1.1 2008/12/19 19:37:31 rbj Exp $
    Author:     Roger Bishop Jones Tobias Nipkow, Markus Wenzel, and Larry Paulson
*)

header {* PreOrders *}

theory PreOrders
imports Code_Setup
uses
  "~~/src/Provers/order.ML"
begin

subsection {* pre-orders *}

text {* adapted by rbj from Orderings.thy (by Tobias Nipkow, Markus Wenzel, and Larry Paulson) *}

class preorder = ord +
  assumes less_le: "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x"
  and preorder_refl [iff]: "x \<le> x"
  and preorder_trans: "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"

begin

text{* \ignore{ declare less_le [simp] } *}

definition
  pro_eq::"'a \<Rightarrow> 'a \<Rightarrow> bool"
where "pro_eq x y == x \<le> y \<and> y \<le> x"

text {*\ignore{declare pro_eq_def [simp] }*}

notation
  "pro_eq"  ("op ~") and
  "pro_eq"  ("(_/ ~ _)" [50, 51] 50)

lemma pro_eq_refl [simp]: "x ~ x"
using pro_eq_def by auto

text {* "AntiSymmetry" *}

lemma antisym [intro]: "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x ~ y"
using pro_eq_def by auto

text {* Reflexivity. *}

lemma eq_refl: "x = y \<Longrightarrow> x \<le> y"
    -- {* This form is useful with the classical reasoner. *}
by (erule ssubst) (rule preorder_refl)

lemma less_irrefl [iff]: "\<not> x < x"
by (simp add: less_le)

lemma le_less: "x \<le> y \<longleftrightarrow> x < y \<or> pro_eq x y"
    -- {* NOT suitable for iff, since it can cause PROOF FAILED. *}
unfolding pro_eq_def
unfolding less_le
by blast

lemma le_imp_less_or_eq: "x \<le> y \<Longrightarrow> x < y \<or> x ~ y"
unfolding less_le pro_eq_def by blast

lemma less_imp_le: "x < y \<Longrightarrow> x \<le> y"
unfolding less_le by blast


text {* Useful for simplification, but too risky to include by default. *}

lemma less_imp_not_eq: "x < y \<Longrightarrow> (x ~ y) \<longleftrightarrow> False"
unfolding pro_eq_def less_le by auto

lemma less_imp_not_eq2: "x < y \<Longrightarrow> (y ~ x) \<longleftrightarrow> False"
unfolding pro_eq_def less_le by auto


text {* Transitivity rules for calculational reasoning *}

lemma neq_le_trans: "\<not> a ~ b \<Longrightarrow> a \<le> b \<Longrightarrow> a < b"
by (simp add: less_le pro_eq_def)

lemma le_neq_trans: "a \<le> b \<Longrightarrow> \<not> a ~ b \<Longrightarrow> a < b"
by (simp add: less_le pro_eq_def)


text {* "Asymmetry" *}

lemma less_not_sym: "x < y \<Longrightarrow> \<not> (y < x)"
by (simp add: less_le antisym)

lemma less_asym: "x < y \<Longrightarrow> (\<not> P \<Longrightarrow> y < x) \<Longrightarrow> P"
by (drule less_not_sym, erule contrapos_np) simp

lemma eq_iff: "x ~ y \<longleftrightarrow> x \<le> y \<and> y \<le> x"
unfolding pro_eq_def
by (blast intro: antisym)

lemma antisym_conv: "y \<le> x \<Longrightarrow> x \<le> y \<longleftrightarrow> x ~ y"
unfolding pro_eq_def
by (blast intro: antisym)

lemma less_imp_neq: "x < y \<Longrightarrow> \<not> x ~ y"
unfolding pro_eq_def less_le
by auto

text {* Transitivity. *}

lemma less_trans: "x < y \<Longrightarrow> y < z \<Longrightarrow> x < z"
by (simp add: less_le) (blast intro: preorder_trans antisym)

lemma le_less_trans: "x \<le> y \<Longrightarrow> y < z \<Longrightarrow> x < z"
by (simp add: less_le) (blast intro: preorder_trans antisym)

lemma less_le_trans: "x < y \<Longrightarrow> y \<le> z \<Longrightarrow> x < z"
by (simp add: less_le) (blast intro: preorder_trans antisym)


text {* Useful for simplification, but too risky to include by default. *}

lemma less_imp_not_less: "x < y \<Longrightarrow> (\<not> y < x) \<longleftrightarrow> True"
by (blast elim: less_asym)

lemma less_imp_triv: "x < y \<Longrightarrow> (y < x \<longrightarrow> P) \<longleftrightarrow> True"
by (blast elim: less_asym)


text {* Transitivity rules for calculational reasoning *}

lemma less_asym': "a < b \<Longrightarrow> b < a \<Longrightarrow> P"
by (rule less_asym)

text {* Dual preorder *}

lemma dual_preorder:
  "preorder (op \<ge>) (op >)"
by unfold_locales
   (simp add: less_le, auto intro: antisym preorder_trans)

end

subsection {* Linear preorders *}

class linpreorder = preorder +
  assumes linear: "x \<le> y \<or> y \<le> x"
begin

lemma less_linear: "x < y \<or> x ~ y \<or> y < x"
unfolding less_le pro_eq_def using less_le linear by blast

lemma le_less_linear: "x \<le> y \<or> y < x"
using linear less_le by auto

lemma le_cases [case_names le ge]:
  "(x \<le> y \<Longrightarrow> P) \<Longrightarrow> (y \<le> x \<Longrightarrow> P) \<Longrightarrow> P"
using linear by blast

lemma linpreorder_cases [case_names less equal greater]:
  "(x < y \<Longrightarrow> P) \<Longrightarrow> (x ~ y \<Longrightarrow> P) \<Longrightarrow> (y < x \<Longrightarrow> P) \<Longrightarrow> P"
using less_linear by blast

lemma not_less: "\<not> x < y \<longleftrightarrow> y \<le> x"
apply (simp add: less_le)
using linear apply (blast intro: antisym)
done

lemma not_less_iff_gr_or_eq:
 "\<not>(x < y) \<longleftrightarrow> (x > y | x ~ y)"
unfolding pro_eq_def less_le
using linear by blast

lemma not_le: "\<not> x \<le> y \<longleftrightarrow> y < x"
apply (simp add: less_le)
using linear apply (blast intro: antisym)
done

lemma neq_iff: "\<not> x ~ y \<longleftrightarrow> x < y \<or> y < x"
unfolding pro_eq_def less_le
using linear by blast

lemma neqE: "\<not> x ~ y \<Longrightarrow> (x < y \<Longrightarrow> R) \<Longrightarrow> (y < x \<Longrightarrow> R) \<Longrightarrow> R"
apply (simp add: neq_iff less_le)
using linear by auto

lemma antisym_conv1: "\<not> x < y \<Longrightarrow> x \<le> y \<longleftrightarrow> x ~ y"
unfolding pro_eq_def
by (blast intro: antisym dest: not_less [THEN iffD1])

lemma antisym_conv2: "x \<le> y \<Longrightarrow> \<not> x < y \<longleftrightarrow> x ~ y"
unfolding pro_eq_def less_le by auto

lemma antisym_conv3: "\<not> y < x \<Longrightarrow> \<not> x < y \<longleftrightarrow> x ~ y"
unfolding pro_eq_def less_le
using linear by (blast intro: antisym dest: not_less [THEN iffD1])

text{*Replacing the old Nat.leI*}
lemma leI: "\<not> x < y \<Longrightarrow> y \<le> x"
unfolding not_less .

lemma leD: "y \<le> x \<Longrightarrow> \<not> x < y"
unfolding not_less .

(*FIXME inappropriate name (or delete altogether)*)
lemma not_leE: "\<not> y \<le> x \<Longrightarrow> x < y"
unfolding not_le .

text {* Dual order *}

lemma dual_linpreorder:
  "linpreorder (op \<ge>) (op >)"
by unfold_locales
  (simp add: less_le, auto intro: antisym preorder_trans simp add: linear)

text {* min/max *}

text {* for historic reasons, definitions are done in context ord *}

definition (in ord)
  min :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  [code unfold, code inline del]: "min a b = (if a \<le> b then a else b)"

definition (in ord)
  max :: "'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  [code unfold, code inline del]: "max a b = (if a \<le> b then b else a)"

lemma min_le_iff_disj:
  "min x y \<le> z \<longleftrightarrow> x \<le> z \<or> y \<le> z"
unfolding min_def using linear by (auto intro: preorder_trans)

lemma le_max_iff_disj:
  "z \<le> max x y \<longleftrightarrow> z \<le> x \<or> z \<le> y"
unfolding max_def using linear by (auto intro: preorder_trans)

lemma min_less_iff_disj:
  "min x y < z \<longleftrightarrow> x < z \<or> y < z"
unfolding min_def less_le
apply (auto intro: preorder_trans)
using linear preorder_trans
by blast

lemma less_max_iff_disj:
  "z < max x y \<longleftrightarrow> z < x \<or> z < y"
unfolding max_def less_le pro_eq_def
using linear by (auto intro: preorder_trans) 

lemma min_less_iff_conj [simp]:
  "z < min x y \<longleftrightarrow> z < x \<and> z < y"
unfolding min_def less_le using linear by (auto intro: preorder_trans)

lemma max_less_iff_conj [simp]:
  "max x y < z \<longleftrightarrow> x < z \<and> y < z"
unfolding max_def less_le using linear by (auto intro: preorder_trans)

lemma split_min [noatp]:
  "P (min i j) \<longleftrightarrow> (i \<le> j \<longrightarrow> P i) \<and> (\<not> i \<le> j \<longrightarrow> P j)"
by (simp add: min_def)

lemma split_max [noatp]:
  "P (max i j) \<longleftrightarrow> (i \<le> j \<longrightarrow> P j) \<and> (\<not> i \<le> j \<longrightarrow> P i)"
by (simp add: max_def)

end

subsection {* Reasoning tools setup *}

ML {*

signature ORDERS =
sig
  val print_structures: Proof.context -> unit
  val setup: theory -> theory
  val preorder_tac: thm list -> Proof.context -> int -> tactic
end;

structure Orders: ORDERS =
struct

(** Theory and context data **)

fun struct_eq ((s1: string, ts1), (s2, ts2)) =
  (s1 = s2) andalso eq_list (op aconv) (ts1, ts2);

structure Data = GenericDataFun
(
  type T = ((string * term list) * Order_Tac.less_arith) list;
    (* Order structures:
       identifier of the structure, list of operations and record of theorems
       needed to set up the transitivity reasoner,
       identifier and operations identify the structure uniquely. *)
  val empty = [];
  val extend = I;
  fun merge _ = AList.join struct_eq (K fst);
);

fun print_structures ctxt =
  let
    val structs = Data.get (Context.Proof ctxt);
    fun pretty_term t = Pretty.block
      [Pretty.quote (Syntax.pretty_term ctxt t), Pretty.brk 1,
        Pretty.str "::", Pretty.brk 1,
        Pretty.quote (Syntax.pretty_typ ctxt (type_of t))];
    fun pretty_struct ((s, ts), _) = Pretty.block
      [Pretty.str s, Pretty.str ":", Pretty.brk 1,
       Pretty.enclose "(" ")" (Pretty.breaks (map pretty_term ts))];
  in
    Pretty.writeln (Pretty.big_list "Order structures:" (map pretty_struct structs))
  end;


(** Method **)

fun struct_tac ((s, [eq, le, less]), thms) prems =
  let
    fun decomp thy (Trueprop $ t) =
      let
        fun excluded t =
          (* exclude numeric types: linear arithmetic subsumes transitivity *)
          let val T = type_of t
          in
	    T = HOLogic.natT orelse T = HOLogic.intT orelse T = HOLogic.realT
          end;
	fun rel (bin_op $ t1 $ t2) =
              if excluded t1 then NONE
              else if Pattern.matches thy (eq, bin_op) then SOME (t1, "=", t2)
              else if Pattern.matches thy (le, bin_op) then SOME (t1, "<=", t2)
              else if Pattern.matches thy (less, bin_op) then SOME (t1, "<", t2)
              else NONE
	  | rel _ = NONE;
	fun dec (Const (@{const_name Not}, _) $ t) = (case rel t
	      of NONE => NONE
	       | SOME (t1, rel, t2) => SOME (t1, "~" ^ rel, t2))
          | dec x = rel x;
      in dec t end;
  in
    case s of
      "preorder" => Order_Tac.partial_tac decomp thms prems
    | "linpreorder" => Order_Tac.linear_tac decomp thms prems
    | _ => error ("Unknown kind of order `" ^ s ^ "' encountered in transitivity reasoner.")
  end

fun preorder_tac prems ctxt =
  FIRST' (map (fn s => CHANGED o struct_tac s prems) (Data.get (Context.Proof ctxt)));

(** Attribute **)

fun add_struct_thm s tag =
  Thm.declaration_attribute
    (fn thm => Data.map (AList.map_default struct_eq (s, Order_Tac.empty TrueI) (Order_Tac.update tag thm)));
fun del_struct s =
  Thm.declaration_attribute
    (fn _ => Data.map (AList.delete struct_eq s));

val attribute = Attrib.syntax
     (Scan.lift ((Args.add -- Args.name >> (fn (_, s) => SOME s) ||
          Args.del >> K NONE) --| Args.colon (* FIXME ||
        Scan.succeed true *) ) -- Scan.lift Args.name --
      Scan.repeat Args.term
      >> (fn ((SOME tag, n), ts) => add_struct_thm (n, ts) tag
           | ((NONE, n), ts) => del_struct (n, ts)));


(** Diagnostic command **)

val print = Toplevel.unknown_context o
  Toplevel.keep (Toplevel.node_case
    (Context.cases (print_structures o ProofContext.init) print_structures)
    (print_structures o Proof.context_of));

val _ =
  OuterSyntax.improper_command "print_orders"
    "print order structures available to transitivity reasoner" OuterKeyword.diag
    (Scan.succeed (Toplevel.no_timing o print));


(** Setup **)

val setup =
  Method.add_methods
    [("preorder", Method.ctxt_args (Method.SIMPLE_METHOD' o preorder_tac []), "transitivity reasoner")] #>
  Attrib.add_attributes [("preorder", attribute, "theorems controlling transitivity reasoner")];

end;

*}

setup Orders.setup


text {* Declarations to set up transitivity reasoner of partial and linear orders. *}

context preorder
begin

(* The type constraint on @{term op =} below is necessary since the operation
   is not a parameter of the locale. *)

lemmas
  [preorder add less_reflE: preorder "op = :: 'a \<Rightarrow> 'a \<Rightarrow> bool" "op <=" "op <"] =
  less_irrefl [THEN notE]
lemmas
  [preorder add le_refl: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  preorder_refl
lemmas
  [preorder add less_imp_le: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_imp_le
lemmas
  [preorder add eqI: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  antisym
lemmas
  [preorder add eqD1: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  eq_refl
lemmas
  [preorder add eqD2: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  sym [THEN eq_refl]
lemmas
  [preorder add less_trans: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_trans
lemmas
  [preorder add less_le_trans: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_le_trans
lemmas
  [preorder add le_less_trans: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  le_less_trans
lemmas
  [preorder add le_trans: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  preorder_trans
lemmas
  [preorder add le_neq_trans: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  le_neq_trans
lemmas
  [preorder add neq_le_trans: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  neq_le_trans
lemmas
  [preorder add less_imp_neq: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_imp_neq
lemmas
  [preorder add eq_neq_eq_imp_neq: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
   eq_neq_eq_imp_neq
lemmas
  [preorder add not_sym: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_sym

end

context linpreorder
begin

lemmas
  [preorder del: preorder "op = :: 'a => 'a => bool" "op <=" "op <"] = _

lemmas
  [preorder add less_reflE: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_irrefl [THEN notE]
lemmas
  [preorder add le_refl: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  preorder_refl
lemmas
  [preorder add less_imp_le: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_imp_le
lemmas
  [preorder add not_lessI: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_less [THEN iffD2]
lemmas
  [preorder add not_leI: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_le [THEN iffD2]
lemmas
  [preorder add not_lessD: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_less [THEN iffD1]
lemmas
  [preorder add not_leD: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_le [THEN iffD1]
lemmas
  [preorder add eqI: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  antisym
lemmas
  [preorder add eqD1: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  eq_refl
lemmas
  [preorder add eqD2: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  sym [THEN eq_refl]
lemmas
  [preorder add less_trans: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_trans
lemmas
  [preorder add less_le_trans: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_le_trans
lemmas
  [preorder add le_less_trans: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  le_less_trans
lemmas
  [preorder add le_trans: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  preorder_trans
lemmas
  [preorder add le_neq_trans: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  le_neq_trans
lemmas
  [preorder add neq_le_trans: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  neq_le_trans
lemmas
  [preorder add less_imp_neq: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  less_imp_neq
lemmas
  [preorder add eq_neq_eq_imp_neq: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  eq_neq_eq_imp_neq
lemmas
  [preorder add not_sym: linpreorder "op = :: 'a => 'a => bool" "op <=" "op <"] =
  not_sym

end


setup {*
let

fun prp t thm = (#prop (rep_thm thm) = t);

fun prove_antisym_le sg ss ((le as Const(_,T)) $ r $ s) =
  let val prems = prems_of_ss ss;
      val less = Const (@{const_name less}, T);
      val t = HOLogic.mk_Trueprop(le $ s $ r);
  in case find_first (prp t) prems of
       NONE =>
         let val t = HOLogic.mk_Trueprop(HOLogic.Not $ (less $ r $ s))
         in case find_first (prp t) prems of
              NONE => NONE
            | SOME thm => SOME(mk_meta_eq(thm RS @{thm linpreorder_class.antisym_conv1}))
         end
     | SOME thm => SOME(mk_meta_eq(thm RS @{thm preorder_class.antisym_conv}))
  end
  handle THM _ => NONE;

fun prove_antisym_less sg ss (NotC $ ((less as Const(_,T)) $ r $ s)) =
  let val prems = prems_of_ss ss;
      val le = Const (@{const_name less_eq}, T);
      val t = HOLogic.mk_Trueprop(le $ r $ s);
  in case find_first (prp t) prems of
       NONE =>
         let val t = HOLogic.mk_Trueprop(NotC $ (less $ s $ r))
         in case find_first (prp t) prems of
              NONE => NONE
            | SOME thm => SOME(mk_meta_eq(thm RS @{thm linpreorder_class.antisym_conv3}))
         end
     | SOME thm => SOME(mk_meta_eq(thm RS @{thm linpreorder_class.antisym_conv2}))
  end
  handle THM _ => NONE;

fun add_simprocs procs thy =
  Simplifier.map_simpset (fn ss => ss
    addsimprocs (map (fn (name, raw_ts, proc) =>
      Simplifier.simproc thy name raw_ts proc) procs)) thy;
fun add_solver name tac =
  Simplifier.map_simpset (fn ss => ss addSolver
    mk_solver' name (fn ss => tac (Simplifier.prems_of_ss ss) (Simplifier.the_context ss)));

in
  add_simprocs [
       ("antisym le", ["(x::'a::preorder) <= y"], prove_antisym_le),
       ("antisym less", ["~ (x::'a::linpreorder) < y"], prove_antisym_less)
     ]
  #> add_solver "Transitivity" Orders.preorder_tac
  (* Adding the transitivity reasoners also as safe solvers showed a slight
     speed up, but the reasoning strength appears to be not higher (at least
     no breaking of additional proofs in the entire HOL distribution, as
     of 5 March 2004, was observed). *)
end
*}


subsection {* Name duplicates *}

lemmas preorder_less_le = less_le
lemmas preorder_eq_refl = preorder_class.eq_refl
lemmas preorder_less_irrefl = preorder_class.less_irrefl
lemmas preorder_le_less = preorder_class.le_less
lemmas preorder_le_imp_less_or_eq = preorder_class.le_imp_less_or_eq
lemmas preorder_less_imp_le = preorder_class.less_imp_le
lemmas preorder_less_imp_not_eq = preorder_class.less_imp_not_eq
lemmas preorder_less_imp_not_eq2 = preorder_class.less_imp_not_eq2
lemmas preorder_neq_le_trans = preorder_class.neq_le_trans
lemmas preorder_le_neq_trans = preorder_class.le_neq_trans

lemmas preorder_antisym = antisym
lemmas preorder_less_not_sym = preorder_class.less_not_sym
lemmas preorder_less_asym = preorder_class.less_asym
lemmas preorder_eq_iff = preorder_class.eq_iff
lemmas preorder_antisym_conv = preorder_class.antisym_conv
lemmas preorder_less_trans = preorder_class.less_trans
lemmas preorder_le_less_trans = preorder_class.le_less_trans
lemmas preorder_less_le_trans = preorder_class.less_le_trans
lemmas preorder_less_imp_not_less = preorder_class.less_imp_not_less
lemmas preorder_less_imp_triv = preorder_class.less_imp_triv
lemmas preorder_less_asym' = preorder_class.less_asym'

lemmas linpreorder_linear = linear
lemmas linpreorder_less_linear = linpreorder_class.less_linear
lemmas linpreorder_le_less_linear = linpreorder_class.le_less_linear
lemmas linpreorder_le_cases = linpreorder_class.le_cases
lemmas linpreorder_not_less = linpreorder_class.not_less
lemmas linpreorder_not_le = linpreorder_class.not_le
lemmas linpreorder_neq_iff = linpreorder_class.neq_iff
lemmas linpreorder_neqE = linpreorder_class.neqE
lemmas linpreorder_antisym_conv1 = linpreorder_class.antisym_conv1
lemmas linpreorder_antisym_conv2 = linpreorder_class.antisym_conv2
lemmas linpreorder_antisym_conv3 = linpreorder_class.antisym_conv3


subsection {* Bounded quantifiers *}

syntax
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3ALL _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3EX _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _<=_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3ALL _>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3EX _>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3ALL _>=_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3EX _>=_./ _)" [0, 0, 10] 10)

syntax (xsymbols)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

syntax (HOL)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3! _<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3? _<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3! _<=_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3? _<=_./ _)" [0, 0, 10] 10)

syntax (HTML output)
  "_All_less" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_<_./ _)"  [0, 0, 10] 10)
  "_Ex_less" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_<_./ _)"  [0, 0, 10] 10)
  "_All_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<le>_./ _)" [0, 0, 10] 10)
  "_Ex_less_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<le>_./ _)" [0, 0, 10] 10)

  "_All_greater" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_>_./ _)"  [0, 0, 10] 10)
  "_Ex_greater" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_>_./ _)"  [0, 0, 10] 10)
  "_All_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<forall>_\<ge>_./ _)" [0, 0, 10] 10)
  "_Ex_greater_eq" :: "[idt, 'a, bool] => bool"    ("(3\<exists>_\<ge>_./ _)" [0, 0, 10] 10)

translations
  "ALL x<y. P"   =>  "ALL x. x < y \<longrightarrow> P"
  "EX x<y. P"    =>  "EX x. x < y \<and> P"
  "ALL x<=y. P"  =>  "ALL x. x <= y \<longrightarrow> P"
  "EX x<=y. P"   =>  "EX x. x <= y \<and> P"
  "ALL x>y. P"   =>  "ALL x. x > y \<longrightarrow> P"
  "EX x>y. P"    =>  "EX x. x > y \<and> P"
  "ALL x>=y. P"  =>  "ALL x. x >= y \<longrightarrow> P"
  "EX x>=y. P"   =>  "EX x. x >= y \<and> P"

print_translation {*
let
  val All_binder = Syntax.binder_name @{const_syntax All};
  val Ex_binder = Syntax.binder_name @{const_syntax Ex};
  val impl = @{const_syntax "op -->"};
  val conj = @{const_syntax "op &"};
  val less = @{const_syntax less};
  val less_eq = @{const_syntax less_eq};

  val trans =
   [((All_binder, impl, less), ("_All_less", "_All_greater")),
    ((All_binder, impl, less_eq), ("_All_less_eq", "_All_greater_eq")),
    ((Ex_binder, conj, less), ("_Ex_less", "_Ex_greater")),
    ((Ex_binder, conj, less_eq), ("_Ex_less_eq", "_Ex_greater_eq"))];

  fun matches_bound v t = 
     case t of (Const ("_bound", _) $ Free (v', _)) => (v = v')
              | _ => false
  fun contains_var v = Term.exists_subterm (fn Free (x, _) => x = v | _ => false)
  fun mk v c n P = Syntax.const c $ Syntax.mark_bound v $ n $ P

  fun tr' q = (q,
    fn [Const ("_bound", _) $ Free (v, _), Const (c, _) $ (Const (d, _) $ t $ u) $ P] =>
      (case AList.lookup (op =) trans (q, c, d) of
        NONE => raise Match
      | SOME (l, g) =>
          if matches_bound v t andalso not (contains_var v u) then mk v l u P
          else if matches_bound v u andalso not (contains_var v t) then mk v g t P
          else raise Match)
     | _ => raise Match);
in [tr' All_binder, tr' Ex_binder] end
*}


subsection {* Transitivity reasoning *}

context ord
begin

lemma prord_le_eq_trans: "a \<le> b \<Longrightarrow> b = c \<Longrightarrow> a \<le> c"
  by (rule subst)

lemma prord_le_eq_trans2: "a \<le> b \<Longrightarrow> b ~ c \<Longrightarrow> a \<le> c"
  unfolding pro_eq_def
  using preorder_trans
  by auto

lemma prord_eq_le_trans: "a = b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
  by (rule ssubst)

lemma prord_eq_le_trans2: "a ~ b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
  unfolding pro_eq_def
  using preorder_trans
  by auto

lemma prord_less_eq_trans: "a < b \<Longrightarrow> b = c \<Longrightarrow> a < c"
  by (rule subst)

lemma prord_less_eq_trans2: "a < b \<Longrightarrow> b ~ c \<Longrightarrow> a < c"
  unfolding pro_eq_def less_le
  using preorder_trans
  by auto

lemma prord_eq_less_trans: "a = b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  by (rule ssubst)

lemma prord_eq_less_trans2: "a ~ b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  unfolding pro_eq_def less_le
  using preorder_trans
  by auto

end

lemma preorder_less_subst2: "(a::'a::preorder) < b ==> f b < (c::'c::preorder) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b < c"
  finally (preorder_less_trans) show ?thesis .
qed

lemma preorder_less_subst1: "(a::'a::preorder) < f b ==> (b::'b::preorder) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (preorder_less_trans) show ?thesis .
qed

lemma preorder_le_less_subst2: "(a::'a::preorder) <= b ==> f b < (c::'c::preorder) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a < c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b < c"
  finally (preorder_le_less_trans) show ?thesis .
qed

lemma preorder_le_less_subst1: "(a::'a::preorder) <= f b ==> (b::'b::preorder) < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a <= f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (preorder_le_less_trans) show ?thesis .
qed

lemma preorder_less_le_subst2: "(a::'a::preorder) < b ==> f b <= (c::'c::preorder) ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b <= c"
  finally (preorder_less_le_trans) show ?thesis .
qed

lemma preorder_less_le_subst1: "(a::'a::preorder) < f b ==> (b::'b::preorder) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a < f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a < f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (preorder_less_le_trans) show ?thesis .
qed

lemma preorder_subst1: "(a::'a::preorder) <= f b ==> (b::'b::preorder) <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (preorder_trans) show ?thesis .
qed

lemma preorder_subst2: "(a::'a::preorder) <= b ==> f b <= (c::'c::preorder) ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b <= c"
  finally (preorder_trans) show ?thesis .
qed

lemma prord_le_eq_subst: "a <= b ==> f b = c ==>
  (!!x y. x <= y ==> f x <= f y) ==> f a <= c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a <= b" hence "f a <= f b" by (rule r)
  also assume "f b = c"
  finally (prord_le_eq_trans) show ?thesis .
qed

lemma prord_eq_le_subst: "a = f b ==> b <= c ==>
  (!!x y. x <= y ==> f x <= f y) ==> a <= f c"
proof -
  assume r: "!!x y. x <= y ==> f x <= f y"
  assume "a = f b"
  also assume "b <= c" hence "f b <= f c" by (rule r)
  finally (prord_eq_le_trans) show ?thesis .
qed

lemma prord_less_eq_subst: "a < b ==> f b = c ==>
  (!!x y. x < y ==> f x < f y) ==> f a < c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a < b" hence "f a < f b" by (rule r)
  also assume "f b = c"
  finally (prord_less_eq_trans) show ?thesis .
qed

lemma prord_eq_less_subst: "a = f b ==> b < c ==>
  (!!x y. x < y ==> f x < f y) ==> a < f c"
proof -
  assume r: "!!x y. x < y ==> f x < f y"
  assume "a = f b"
  also assume "b < c" hence "f b < f c" by (rule r)
  finally (prord_eq_less_trans) show ?thesis .
qed

text {*
  Note that this list of rules is in reverse order of priorities.
*}

lemmas preorder_trans_rules [trans] =
  preorder_less_subst2
  preorder_less_subst1
  preorder_le_less_subst2
  preorder_le_less_subst1
  preorder_less_le_subst2
  preorder_less_le_subst1
  preorder_subst2
  preorder_subst1
  prord_le_eq_subst
  prord_eq_le_subst
  prord_less_eq_subst
  prord_eq_less_subst
  forw_subst
  back_subst
  rev_mp
  mp
  preorder_neq_le_trans
  preorder_le_neq_trans
  preorder_less_trans
  preorder_less_asym'
  preorder_le_less_trans
  preorder_less_le_trans
  preorder_trans
  preorder_antisym
  prord_le_eq_trans
  prord_eq_le_trans
  prord_less_eq_trans
  prord_eq_less_trans
  trans


(* FIXME cleanup *)

text {* These support proving chains of decreasing inequalities
    a >= b >= c ... in Isar proofs. *}

lemma xt1:
  "a = b ==> b > c ==> a > c"
  "a > b ==> b = c ==> a > c"
  "a = b ==> b >= c ==> a >= c"
  "a >= b ==> b = c ==> a >= c"
  "(x::'a::preorder) >= y ==> y >= z ==> x >= z"
  "(x::'a::preorder) > y ==> y >= z ==> x > z"
  "(x::'a::preorder) >= y ==> y > z ==> x > z"
  "(a::'a::preorder) > b ==> b > a ==> P"
  "(x::'a::preorder) > y ==> y > z ==> x > z"
  "(a::'a::preorder) >= b ==> \<not> b >= a ==> a > b"
  "\<not>(a::'a::preorder) >= b ==> b >= a ==> b > a"
  "a = f b ==> b > c ==> (!!x y. x > y ==> f x > f y) ==> a > f c" 
  "a > b ==> f b = c ==> (!!x y. x > y ==> f x > f y) ==> f a > c"
  "a = f b ==> b >= c ==> (!!x y. x >= y ==> f x >= f y) ==> a >= f c"
  "a >= b ==> f b = c ==> (!! x y. x >= y ==> f x >= f y) ==> f a >= c"
apply auto
using pro_eq_def less_le
by auto

lemma xt2:
  "(a::'a::preorder) >= f b ==> b >= c ==> (!!x y. x >= y ==> f x >= f y) ==> a >= f c"
by (subgoal_tac "f b >= f c", force, force)

lemma xt3: "(a::'a::preorder) >= b ==> (f b::'b::preorder) >= c ==> 
    (!!x y. x >= y ==> f x >= f y) ==> f a >= c"
by (subgoal_tac "f a >= f b", force, force)

lemma xt4: "(a::'a::preorder) > f b ==> (b::'b::preorder) >= c ==>
  (!!x y. x >= y ==> f x >= f y) ==> a > f c"
by (subgoal_tac "f b >= f c", force, force)

lemma xt5: "(a::'a::preorder) > b ==> (f b::'b::preorder) >= c==>
    (!!x y. x > y ==> f x > f y) ==> f a > c"
by (subgoal_tac "f a > f b", force, force)

lemma xt6: "(a::'a::preorder) >= f b ==> b > c ==>
    (!!x y. x > y ==> f x > f y) ==> a > f c"
by (subgoal_tac "f b > f c", force, force)

lemma xt7: "(a::'a::preorder) >= b ==> (f b::'b::preorder) > c ==>
    (!!x y. x >= y ==> f x >= f y) ==> f a > c"
by (subgoal_tac "f a >= f b", force, force)

lemma xt8: "(a::'a::preorder) > f b ==> (b::'b::preorder) > c ==>
    (!!x y. x > y ==> f x > f y) ==> a > f c"
by (subgoal_tac "f b > f c", force, force)

lemma xt9: "(a::'a::preorder) > b ==> (f b::'b::preorder) > c ==>
    (!!x y. x > y ==> f x > f y) ==> f a > c"
by (subgoal_tac "f a > f b", force, force)

lemmas xtrans = xt1 xt2 xt3 xt4 xt5 xt6 xt7 xt8 xt9

(* 
  Since "a >= b" abbreviates "b <= a", the abbreviation "..." stands
  for the wrong thing in an Isar proof.

  The extra transitivity rules can be used as follows: 

lemma "(a::'a::preorder) > z"
proof -
  have "a >= b" (is "_ >= ?rhs")
    sorry
  also have "?rhs >= c" (is "_ >= ?rhs")
    sorry
  also (xtrans) have "?rhs = d" (is "_ = ?rhs")
    sorry
  also (xtrans) have "?rhs >= e" (is "_ >= ?rhs")
    sorry
  also (xtrans) have "?rhs > f" (is "_ > ?rhs")
    sorry
  also (xtrans) have "?rhs > z"
    sorry
  finally (xtrans) show ?thesis .
qed

  Alternatively, one can use "declare xtrans [trans]" and then
  leave out the "(xtrans)" above.
*)


subsection {* Order on functions *}

instantiation "fun" :: (type, ord) ord
begin

definition
  le_fun_def [code func del]: "f \<le> g \<longleftrightarrow> (\<forall>x. f x \<le> g x)"

definition
  less_fun_def [code func del]: "(f\<Colon>'a \<Rightarrow> 'b) < g \<longleftrightarrow> f \<le> g \<and> f \<noteq> g"

instance ..

end


subsection {* Monotonicity, least value operator and min/max *}

context preorder
begin

definition
  mono :: "('a \<Rightarrow> 'b\<Colon>preorder) \<Rightarrow> bool"
where
  "mono f \<longleftrightarrow> (\<forall>x y. x \<le> y \<longrightarrow> f x \<le> f y)"

lemma monoI [intro?]:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>preorder"
  shows "(\<And>x y. x \<le> y \<Longrightarrow> f x \<le> f y) \<Longrightarrow> mono f"
  unfolding mono_def by iprover

lemma monoD [dest?]:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>preorder"
  shows "mono f \<Longrightarrow> x \<le> y \<Longrightarrow> f x \<le> f y"
  unfolding mono_def by iprover

end

context linpreorder
begin

lemma min_of_mono:
  fixes f :: "'a \<Rightarrow> 'b \<Colon> linpreorder"
  shows "mono f \<Longrightarrow> min (f m) (f n) ~ f (min m n)"
using linear pro_eq_refl
  by (auto simp: mono_def PreOrders.min_def min_def pro_eq_def)

lemma max_of_mono:
  fixes f :: "'a \<Rightarrow> 'b\<Colon>linpreorder"
  shows "mono f \<Longrightarrow> max (f m) (f n) ~ f (max m n)"
  by (auto simp: mono_def PreOrders.max_def max_def)

end

text{*
\ignore{

lemma LeastI2_order:
  "[| P (x::'a::preorder);
      !!y. P y ==> x <= y;
      !!x. [| P x; ALL y. P y --> x \<le> y |] ==> Q x |]
   ==> Q (Least P)"
apply (unfold Least_def)
apply (rule theI2)
  apply (blast intro: preorder_antisym)+
done
}

*}

lemma min_leastL: "(!!x. least <= x) ==> min least x = least"
by (simp add: min_def)

lemma max_leastL: "(!!x. least <= x) ==> max least x = x"
by (simp add: max_def)

lemma min_leastR: "(\<And>x\<Colon>'a\<Colon>preorder. least \<le> x) \<Longrightarrow> min x least ~ least"
apply (simp add: min_def)
apply (blast intro: preorder_antisym)
done

lemma max_leastR: "(\<And>x\<Colon>'a\<Colon>preorder. least \<le> x) \<Longrightarrow> max x least ~ x"
apply (simp add: max_def)
apply (blast intro: preorder_antisym)
done

end
