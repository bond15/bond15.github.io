
(* PAGE:PRELUDE *)
(* ================================================================
   Discussion: Where do induction principles come from?

   Paste into https://coq.vercel.app/scratchpad.html and step through.

   For every [Inductive] type T, Coq automatically generates T_ind.
   The pattern:
     - P : T -> Prop is the property we want to prove.
     - One case per constructor.
     - Each argument of type T gives an inductive hypothesis (IH).
     - Conclusion: forall t : T, P t.
   ================================================================ *)


(* PAGE:ENUM *)
(* ---------------------------------------------------------------
   1. Enumerated types: induction ~ case analysis
   --------------------------------------------------------------- *)

(* Learning objective: read an induction principle and apply it.
   For a type with no recursive constructors, induction is just
   checking every constructor, one case each. *)

Inductive MyType : Type := A | B | C.

Check MyType_ind.
(*
      P(A)     P(B)     P(C)
   --------------------------
           ∀x. P(x)
*)

Definition alwaysTrue (x : MyType) : Prop := True.

Check MyType_ind alwaysTrue.

Theorem AlwaysTrue : forall x : MyType, alwaysTrue x.
Proof.
  apply MyType_ind.
  (*
     ------  A     ------  B     ------  C
      True          True          True
  *)
  - unfold alwaysTrue. trivial.
  - unfold alwaysTrue. trivial.
  - unfold alwaysTrue. trivial.
Qed.

Definition xIsABC (x : MyType) : Prop := x = A \/ x = B \/ x = C.

Check MyType_ind xIsABC.


Theorem MyType_cases : forall x : MyType, xIsABC x.
Proof.
  unfold xIsABC.
  apply MyType_ind.
  (*
     ---------------------  A
     A = A ∨ A = B ∨ A = C

     ---------------------  B
     B = A ∨ B = B ∨ B = C

     ---------------------  C
     C = A ∨ C = B ∨ C = C
  *)
  - left. reflexivity.
  - right. left. reflexivity.
  - right. right. reflexivity.
Qed.


(* PAGE:NAT *)
(* ---------------------------------------------------------------
   2. Natural numbers: the first IH
   --------------------------------------------------------------- *)

(* Learning objective: see where an inductive hypothesis comes from.
   succ takes a nat, so its case gets an IH, and we use it with
   rewrite. *)

Module MyNat.

Inductive nat : Type := zero | succ : nat -> nat.

Check nat_ind.
(*
      P(zero)     ∀n. P(n) ⇒ P(succ n)
   ------------------------------------
                ∀n. P(n)
*)

Fixpoint plus (n m : nat) : nat :=
  match n with
  | zero => m
  | succ n' => succ (plus n' m)
  end.

Theorem ZeroPlusNIsN : forall (n : nat), plus zero n = n.
Proof.
  intros. compute. reflexivity.
Qed.

Definition nPlusZeroIsN (n : nat) : Prop := plus n zero = n.


Check nat_ind nPlusZeroIsN.

Theorem plus_zero_r : forall n : nat, nPlusZeroIsN n.
Proof.
  unfold nPlusZeroIsN.
  (* intros. compute. Undo. Undo. *)
  apply nat_ind.
  (*
     ---------------------  zero
     plus zero zero = zero

           plus n zero = n            (IH)
     ---------------------------  succ
     plus (succ n) zero = succ n
  *)
  - compute. reflexivity.
  - intros n IH. simpl. rewrite IH. reflexivity.
Qed.

End MyNat.


(* PAGE:TREE *)
(* ---------------------------------------------------------------
   3. Binary trees: two IHs
   --------------------------------------------------------------- *)

(* Learning objective: every recursive argument gets its own IH.
   node has two subtrees, so its case has two IHs. *)

Inductive Tree (X : Type) : Type :=
| leaf
| node (x : X) (l : Tree X) (r : Tree X).

Check Tree_ind.
(*
      P(leaf)     ∀x l r. P(l) ∧ P(r) ⇒ P(node x l r)
   ---------------------------------------------------
                      ∀t. P(t)
*)

Fixpoint mirror {X : Type} (t : Tree X) : Tree X :=
  match t with
  | leaf _ => leaf X
  | node _ x l r => node X x (mirror r) (mirror l)
  end.

Definition tMirrorTwiceIsT {X : Type} (t : Tree X) : Prop :=
  mirror (mirror t) = t.

Check Tree_ind nat tMirrorTwiceIsT.

Theorem mirror_mirror : forall (X : Type) (t : Tree X), tMirrorTwiceIsT t.
Proof.
  unfold tMirrorTwiceIsT.
  intros X.
  apply Tree_ind.
  (*
     ---------------------------  leaf
     mirror (mirror leaf) = leaf

     mirror (mirror l) = l     mirror (mirror r) = r      (IHl, IHr)
     -----------------------------------------------  node
       mirror (mirror (node x l r)) = node x l r
  *)
  - simpl. reflexivity.
  - intros x l IHl r IHr.
    change (mirror (node X x (mirror r) (mirror l)) = node X x l r).
    simpl. rewrite IHl. rewrite IHr. reflexivity.
Qed.


(* PAGE:UTLC-INDUCTION *)
(* ---------------------------------------------------------------
   4. Untyped lambda calculus terms
   --------------------------------------------------------------- *)

(* Learning objective: the same pattern works for the syntax of a
   language.  This is the structural induction on terms from
   lecture 6. *)

Require Import Arith.   (* for Nat.le_trans and Nat.le_add_r *)

Inductive utlc : Type :=
| var (n : nat)
| app (t1 t2 : utlc)
| lam (x : nat) (t : utlc).

Check utlc_ind.
(*
      ∀x. P(x)     ∀e1 e2. P(e1) ∧ P(e2) ⇒ P(e1 e2)     ∀x e. P(e) ⇒ P(λx.e)
   -------------------------------------------------------------------------
                                  ∀e. P(e)
*)
(* var: no IH.  app: two IHs.  lam: one IH (for the body). *)

(* Number of variable occurrences in a term. *)
Fixpoint numVars (t : utlc) : nat :=
  match t with
  | var _ => 1
  | app t1 t2 => numVars t1 + numVars t2
  | lam _ t => numVars t
  end.

Definition tHasAtLeastOneVar (t : utlc) : Prop := 1 <= numVars t.

Check utlc_ind tHasAtLeastOneVar.

Theorem has_var : forall t : utlc, tHasAtLeastOneVar t.
Proof.
  unfold tHasAtLeastOneVar.
  apply utlc_ind.
  (*
     ----------------  var
     1 <= numVars(x)

     1 <= numVars(e1)     1 <= numVars(e2)      (IH1, IH2)
     -------------------------------------  app
             1 <= numVars(e1 e2)

       1 <= numVars(e)          (IH)
     --------------------  lam
     1 <= numVars(λx.e)
  *)
  - intros n. simpl. apply le_n.
  - intros t1 IH1 t2 IH2. simpl.
    apply Nat.le_trans with (numVars t1).
    + exact IH1.
    + apply Nat.le_add_r.
  - intros x t IH. simpl. exact IH.
Qed.


(* PAGE:SMALL-STEP-INTRO *)
(* ===============================================================
   PART II: Small-step operational semantics in Coq

   Each inference rule becomes a constructor.
   A derivation tree becomes a proof.

     5. Booleans:       what a step relation is.
     6. Mini-IMP:       configurations <c,σ> (lecture 7).
     7. CBV lambda:     values and substitution (lecture 6).
   =============================================================== *)


(* PAGE:BOOLEANS *)
(* ---------------------------------------------------------------
   5. Booleans
   --------------------------------------------------------------- *)

(* Learning objective: what a small-step relation is.  Each rule is
   a constructor, one step is a derivation tree, and -->* chains
   steps together. *)

(* Syntax.

   BNF:
      b ::= true | false | b0 ∨ b1 | b0 ∧ b1 | ¬b

   Inference rules:
                                    b0 bexp   b1 bexp     b0 bexp   b1 bexp      b bexp
      ---------     ----------     -----------------     -----------------     -------
      true bexp     false bexp       b0 ∨ b1 bexp          b0 ∧ b1 bexp        ¬b bexp
*)
Inductive bexp : Type :=
| BTrue
| BFalse
| BOr (b0 b1 : bexp)
| BAnd (b0 b1 : bexp)
| BNot (b : bexp).

(* Notation so we can write expressions as on paper, inside <{ }>.
   For example  <{ ¬(true ∧ false) }>  is  BNot (BAnd BTrue BFalse).
   You can skip this block. *)
Declare Custom Entry imp.
Notation "<{ e }>" := e (e custom imp at level 99).
Notation "( x )" := x (in custom imp, x at level 99).
Notation "x" := x (in custom imp at level 0, x constr at level 0).
Notation "'true'" := true (at level 1).
Notation "'false'" := false (at level 1).
Notation "'true'" := BTrue (in custom imp at level 0).
Notation "'false'" := BFalse (in custom imp at level 0).
Notation "¬ b" := (BNot b) (in custom imp at level 75, right associativity).
Notation "b0 ∧ b1" := (BAnd b0 b1) (in custom imp at level 80, right associativity).
Notation "b0 ∨ b1" := (BOr b0 b1) (in custom imp at level 85, right associativity).

(* Lets us write  b1 --> b2  for one step. *)
Reserved Notation "t '-->' t'" (at level 40).

(* Step rules: step the left operand, then decide.

           b0 --> b2
      -------------------- (S-Or)      ------------------- (S-OrTrue)
      b0 ∨ b1 --> b2 ∨ b1              true ∨ b1 --> true

                                       -------------------- (S-OrFalse)
                                       false ∨ b1 --> b1

           b0 --> b2
      -------------------- (S-And)     ------------------- (S-AndTrue)
      b0 ∧ b1 --> b2 ∧ b1              true ∧ b1 --> b1

                                       --------------------- (S-AndFalse)
                                       false ∧ b1 --> false

          b --> b2
      -------------- (S-Not)   ---------------- (S-NotTrue)   ---------------- (S-NotFalse)
      ¬b --> ¬b2               ¬true --> false                ¬false --> true
*)
Inductive step : bexp -> bexp -> Prop :=
| S_Or       : forall b0 b2 b1, b0 --> b2 -> <{ b0 ∨ b1 }> --> <{ b2 ∨ b1 }>
| S_OrTrue   : forall b1, <{ true ∨ b1 }> --> <{ true }>
| S_OrFalse  : forall b1, <{ false ∨ b1 }> --> b1
| S_And      : forall b0 b2 b1, b0 --> b2 -> <{ b0 ∧ b1 }> --> <{ b2 ∧ b1 }>
| S_AndTrue  : forall b1, <{ true ∧ b1 }> --> b1
| S_AndFalse : forall b1, <{ false ∧ b1 }> --> <{ false }>
| S_Not      : forall b b2, b --> b2 -> <{ ¬b }> --> <{ ¬b2 }>
| S_NotTrue  : <{ ¬true }> --> <{ false }>
| S_NotFalse : <{ ¬false }> --> <{ true }>
where "t '-->' t'" := (step t t').

(* One step:

            ---------------------- S-AndTrue
            true ∧ false --> false
      ---------------------------------- S-Not
      ¬(true ∧ false) --> ¬false                                  *)
Example one_step :
  <{ ¬(true ∧ false) }> --> <{ ¬false }>.
Proof. apply S_Not. apply S_AndTrue. Qed.

(* Multi-step:  t1 -->* t3  means t1 reaches t3 in zero or more
   steps.  Two rules, as in lecture 7:

                              t1 --> t2     t2 -->* t3
      ---------- ms_refl      ------------------------ ms_step
      t -->* t                       t1 -->* t3

   [multi R] works for any step relation R, so the sections
   below reuse it. *)
Inductive multi {X : Type} (R : X -> X -> Prop) : X -> X -> Prop :=
| ms_refl : forall x, multi R x x
| ms_step : forall x y z, R x y -> multi R y z -> multi R x z.

Notation "t '-->*' t'" := (multi step t t') (at level 40).

(* ¬(true ∧ false)  -->  ¬false  -->  true *)
Example run :
  <{ ¬(true ∧ false) }> -->* <{ true }>.
Proof.
  eapply ms_step. { apply S_Not. apply S_AndTrue. }
  eapply ms_step. { apply S_NotFalse. }
  apply ms_refl.
Qed.


(* PAGE:MINI-IMP *)
(* ---------------------------------------------------------------
   6. Mini-IMP (lecture 7, with boolean variables)

   A small version of IMP.  In lecture 7, variables hold integers;
   here they hold booleans, so there are no arithmetic expressions.
   The command rules are the ones from lecture 7 (slides 11-12),
   with b in place of a in assignment.
   --------------------------------------------------------------- *)

(* Learning objective: configurations <c,σ> from lecture 7.  A step
   now carries a state σ, which assignment changes and variables
   read. *)

Module Imp.

Definition var := nat.

(* Syntax.

   BNF:
      b ::= true | false | x | b0 ∨ b1 | b0 ∧ b1 | ¬b        (Section 5, plus x)
      c ::= skip | x := b | c0; c1 | if b then c0 else c1 | while b do c

   Inference rules: the rules from Section 5 for b, plus

      ------         --------      b bexp          c0 com   c1 com
      x bexp         skip com    ----------      ----------------
                                 x := b com         c0; c1 com

      b bexp   c0 com   c1 com           b bexp   c com
      ------------------------         ----------------
      if b then c0 else c1 com         while b do c com
*)
Inductive bexp : Type :=
| BLit (v : bool)          (* the literals true and false *)
| BVar (x : var)
| BOr (b0 b1 : bexp)
| BAnd (b0 b1 : bexp)
| BNot (b : bexp).
(* A literal holds a Coq bool, just as  n  in lecture holds an integer. *)

Inductive com : Type :=
| CSkip
| CAsgn (x : var) (b : bexp)
| CSeq (c0 c1 : com)
| CIf (b : bexp) (c0 c1 : com)
| CWhile (b : bexp) (c : com).

(* Notation so we can write programs as on paper, inside <{ }>.
   For example  <{ X := true; while X do X := false }>.
   The two coercions let a Coq bool or a variable be used directly
   as a bexp.  You can skip this block. *)
Set Warnings "-notation-overridden".   (* we reuse the notations from Section 5 *)
Coercion BLit : bool >-> bexp.
Coercion BVar : var >-> bexp.
Notation "'true'" := (BLit true) (in custom imp at level 0).
Notation "'false'" := (BLit false) (in custom imp at level 0).
Notation "¬ b" := (BNot b) (in custom imp at level 75, right associativity).
Notation "b0 ∧ b1" := (BAnd b0 b1) (in custom imp at level 80, right associativity).
Notation "b0 ∨ b1" := (BOr b0 b1) (in custom imp at level 85, right associativity).
Notation "'skip'" := CSkip (in custom imp at level 0).
Notation "x := b" := (CAsgn x b)
  (in custom imp at level 0, x constr at level 0, b at level 85, no associativity).
Notation "c0 ; c1" := (CSeq c0 c1) (in custom imp at level 90, right associativity).
Notation "'if' b 'then' c0 'else' c1" := (CIf b c0 c1)
  (in custom imp at level 88, b at level 85, c0 at level 88, c1 at level 88).
Notation "'while' b 'do' c" := (CWhile b c)
  (in custom imp at level 88, b at level 85, c at level 88).

(* States  σ : Var -> {true, false}  (Coq bools),  and the update  σ[x ↦ v].
   σ0 is the empty state: every variable is false. *)
Definition state := var -> bool.
Definition σ0 : state := fun _ => false.
Definition update (σ : state) (x : var) (v : bool) : state :=
  fun y => if Nat.eqb x y then v else σ y.
Notation "σ [ x ↦ v ]" := (update σ x v)
  (at level 2, left associativity, format "σ [ x  ↦  v ]").

(* Configurations  <b,σ>  and  <c,σ>  are pairs. *)
Reserved Notation "t '-->b' t'" (at level 40).

(* Step rules for b: the rules from Section 5, with σ carried along,
   plus looking up a variable (like  <x,σ> -->a σ(x)  in lecture):

      ---------------- (S-Var)
      <x,σ> -->b σ(x)
*)
Inductive bstep : bexp * state -> bexp -> Prop :=
| S_Var      : forall σ x, (BVar x, σ) -->b σ x
| S_Or       : forall σ b0 b2 b1, (b0, σ) -->b b2 ->
    (<{ b0 ∨ b1 }>, σ) -->b <{ b2 ∨ b1 }>
| S_OrTrue   : forall σ b1, (<{ true ∨ b1 }>, σ) -->b <{ true }>
| S_OrFalse  : forall σ b1, (<{ false ∨ b1 }>, σ) -->b b1
| S_And      : forall σ b0 b2 b1, (b0, σ) -->b b2 ->
    (<{ b0 ∧ b1 }>, σ) -->b <{ b2 ∧ b1 }>
| S_AndTrue  : forall σ b1, (<{ true ∧ b1 }>, σ) -->b b1
| S_AndFalse : forall σ b1, (<{ false ∧ b1 }>, σ) -->b <{ false }>
| S_Not      : forall σ b b2, (b, σ) -->b b2 -> (<{ ¬b }>, σ) -->b <{ ¬b2 }>
| S_NotTrue  : forall σ, (<{ ¬true }>, σ) -->b <{ false }>
| S_NotFalse : forall σ, (<{ ¬false }>, σ) -->b <{ true }>
where "t '-->b' t'" := (bstep t t').

(* Step rules for commands (lecture 7, slides 11-12, with b in place of a):

           <b,σ> -->b b2
      --------------------------- (S-Asgn1)
      <x := b,σ> --> <x := b2,σ>

      ---------------------------------- (S-Asgn)     (v is true or false)
      <x := v,σ> --> <skip,σ[x↦v]>

          <c0,σ> --> <c2,σ2>
      ----------------------------- (S-Seq1)  ------------------------ (S-Seq)
      <c0; c1,σ> --> <c2; c1,σ2>              <skip; c1,σ> --> <c1,σ>

                         <b,σ> -->b b2
      --------------------------------------------------------- (S-If1)
      <if b then c0 else c1,σ> --> <if b2 then c0 else c1,σ>

      -------------------------------------- (S-IfTrue)
      <if true then c0 else c1,σ> --> <c0,σ>

      --------------------------------------- (S-IfFalse)
      <if false then c0 else c1,σ> --> <c1,σ>

      -------------------------------------------------------------- (S-While)
      <while b do c,σ> --> <if b then (c; while b do c) else skip,σ>
*)
Inductive cstep : com * state -> com * state -> Prop :=
| S_Asgn1     : forall σ x b b2, (b, σ) -->b b2 ->
    (<{ x := b }>, σ) --> (<{ x := b2 }>, σ)
| S_Asgn      : forall σ x (v : bool),
    (<{ x := v }>, σ) --> (<{ skip }>, σ[x ↦ v])
| S_Seq1      : forall σ σ2 c0 c2 c1, (c0, σ) --> (c2, σ2) ->
    (<{ c0; c1 }>, σ) --> (<{ c2; c1 }>, σ2)
| S_Seq       : forall σ c1, (<{ skip; c1 }>, σ) --> (c1, σ)
| S_If1       : forall σ b b2 c0 c1, (b, σ) -->b b2 ->
    (<{ if b then c0 else c1 }>, σ) --> (<{ if b2 then c0 else c1 }>, σ)
| S_IfTrue    : forall σ c0 c1, (<{ if true then c0 else c1 }>, σ) --> (c0, σ)
| S_IfFalse   : forall σ c0 c1, (<{ if false then c0 else c1 }>, σ) --> (c1, σ)
| S_While     : forall σ b c,
    (<{ while b do c }>, σ) --> (<{ if b then (c; while b do c) else skip }>, σ)
where "t '-->' t'" := (cstep t t').

(* -->* for commands. *)
Notation "t '-->*' t'" := (multi cstep t t') (at level 40).

Definition X : var := 0.
Definition Y : var := 1.

(* One step, where the state matters (σ(x) = true):

           ----------------- S-Var
           <x,σ> -->b true
      --------------------------- S-Not
      <¬x,σ> -->b ¬true
   ----------------------------------- S-Asgn1
   <y := ¬x,σ> --> <y := ¬true,σ>                                  *)
Example one_step :
  (<{ Y := ¬X }>, σ0[X ↦ true])
    --> (<{ Y := ¬true }>, σ0[X ↦ true]).
Proof.
  apply S_Asgn1. apply S_Not. apply S_Var.
Qed.

(* x := true; while x do x := false

   Write  W  for  while x do x := false.  Starting from the empty
   state σ0 (every variable false):

        <x := true; W, σ0>
    --> <skip; W, σ1>                                  (S-Seq1, S-Asgn)
    --> <W, σ1>                                        (S-Seq)
    --> <if x then (x := false; W) else skip, σ1>      (S-While)
    --> <if true then (x := false; W) else skip, σ1>   (S-If1, S-Var)
    --> <x := false; W, σ1>                            (S-IfTrue)
    --> <skip; W, σ2>                                  (S-Seq1, S-Asgn)
    --> <W, σ2>                                        (S-Seq)
    --> <if x then (x := false; W) else skip, σ2>      (S-While)
    --> <if false then (x := false; W) else skip, σ2>  (S-If1, S-Var)
    --> <skip, σ2>                                     (S-IfFalse)

   where  σ1 = σ0[x↦true]  and  σ2 = σ1[x↦false]. *)
Definition prog : com := <{ X := true; while X do X := false }>.

Example prog_runs :
  (prog, σ0) -->* (<{ skip }>, σ0[X ↦ true][X ↦ false]).
Proof.
  unfold prog.
  eapply ms_step. { apply S_Seq1. apply S_Asgn. }
  eapply ms_step. { apply S_Seq. }
  eapply ms_step. { apply S_While. }
  eapply ms_step. { apply S_If1. apply S_Var. }
  cbn.   (* compute the lookup σ1(x) = true *)
  eapply ms_step. { apply S_IfTrue. }
  eapply ms_step. { apply S_Seq1. apply S_Asgn. }
  eapply ms_step. { apply S_Seq. }
  eapply ms_step. { apply S_While. }
  eapply ms_step. { apply S_If1. apply S_Var. }
  cbn.   (* compute the lookup σ2(x) = false *)
  eapply ms_step. { apply S_IfFalse. }
  apply ms_refl.
Qed.

(* <while true do skip, σ>  -->*  <while true do skip, σ>  (lecture 7) *)
Definition loop : com := <{ while true do skip }>.
Example loop_steps : forall σ,
  (loop, σ) -->* (loop, σ).
Proof.
  intros σ.
  eapply ms_step. { apply S_While. }
  eapply ms_step. { apply S_IfTrue. }
  eapply ms_step. { apply S_Seq. }
  apply ms_refl.
Qed.

End Imp.


(* PAGE:CBV-LAMBDA *)
(* ---------------------------------------------------------------
   7. Lambda calculus: CBV (lecture 6)
   --------------------------------------------------------------- *)

(* Learning objective: the CBV rules from lecture 6 in Coq.  New
   pieces: values, substitution, and a rule (AppR) that only fires
   once the left side is a value. *)

Module Lambda.

(* Syntax: the [utlc] type from Section 4.

   BNF:
      e ::= x | λx.e | e1 e2

   Inference rules:
                       e term          e1 term    e2 term
      ------        ----------        ------------------
      x term        λx.e term             e1 e2 term
*)

(* Simple substitution (fine here: we only substitute closed terms). *)
Fixpoint subst (x : nat) (arg : utlc) (e : utlc) : utlc :=
  match e with
  | var y => if Nat.eqb x y then arg else var y
  | app e1 e2 => app (subst x arg e1) (subst x arg e2)
  | lam y body => if Nat.eqb x y then lam y body else lam y (subst x arg body)
  end.

(* Values:  v ::= λx.e *)
Inductive value : utlc -> Prop :=
| v_lam : forall x e, value (lam x e).

(* Lets us write  e1 -cbv-> e2  for one CBV step. *)
Reserved Notation "t '-cbv->' t'" (at level 40).

(* CBV step rules.

                                    e1 -cbv-> e1'              e -cbv-> e'
      ---------------------- β   ------------------- AppL   -------------- AppR
      (λx.e) v -cbv-> e[x↦v]     e1 e2 -cbv-> e1' e2        v e -cbv-> v e'
*)
Inductive cbv : utlc -> utlc -> Prop :=
| cbv_beta : forall x e v, value v ->
    app (lam x e) v -cbv-> subst x v e
| cbv_appL : forall e1 e1' e2, e1 -cbv-> e1' ->
    app e1 e2 -cbv-> app e1' e2
| cbv_appR : forall v e e', value v -> e -cbv-> e' ->
    app v e -cbv-> app v e'
where "t '-cbv->' t'" := (cbv t t').

Definition x := 0.
Definition y := 1.
Definition z := 2.
Definition Id (x : nat) := lam x (var x).
Definition omega := lam z (app (var z) (var z)).
Definition Omega := app omega omega.

(* The derivation tree from lecture:

       --------------------------- β
       (λx.x)(λz.z) -cbv-> λz.z
   ----------------------------------- AppL
   ((λx.x)(λz.z)) Ω -cbv-> (λz.z) Ω                                  *)
Example lecture_tree :
  app (app (Id x) (Id z)) Omega -cbv-> app (Id z) Omega.
Proof.
  apply cbv_appL.
  apply (cbv_beta x (var x) (Id z)).
  constructor.
Qed.

(* Many CBV steps. *)
Notation "t '-cbv->*' t'" := (multi cbv t t') (at level 40).

(* ((λx.x)(λy.y)) (λz.z)  -cbv->  (λy.y)(λz.z)  -cbv->  λz.z *)
Example run :
  app (app (Id x) (Id y)) (Id z) -cbv->* Id z.
Proof.
  eapply ms_step. { apply cbv_appL. apply (cbv_beta x (var x) (Id y)). constructor. }
  eapply ms_step. { apply (cbv_beta y (var y) (Id z)). constructor. }
  apply ms_refl.
Qed.

(* Ω steps to itself. *)
Example Omega_loops : Omega -cbv-> Omega.
Proof. apply (cbv_beta z (app (var z) (var z)) omega). constructor. Qed.

End Lambda.
