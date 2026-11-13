(* A faithful Rocq translation of Syntax.NamedUntyped.agda, the source
   used for Discussion 1.  Lists provide set-like notation, but duplicates
   are deliberately retained, exactly as in the Agda file. *)

From Coq Require Import String List Bool.
Import ListNotations.
Open Scope string_scope.

Definition Var := string.

Fixpoint memv (x : Var) (xs : list Var) : bool :=
  match xs with
  | [] => false
  | y :: ys => if String.eqb x y then true else memv x ys
  end.

Fixpoint diff (xs ys : list Var) : list Var :=
  match xs with
  | [] => []
  | x :: xs' => if memv x ys then diff xs' ys else x :: diff xs' ys
  end.

Definition fresh (x : Var) (xs : list Var) : Prop := memv x xs = false.
Notation "x ∉ xs" := (fresh x xs) (at level 70).

(* PAGE:SYNTAX *)
Inductive term : Type :=
| TVar (x : Var)
| App (e f : term)
| Lam (x : Var) (e : term).

Notation "⟨ x ⟩" := (TVar x) (at level 0).
Infix "·" := App (at level 59, left associativity).
Notation "'ƛ' x '⇒' e" := (Lam x e) (at level 60, right associativity).

Definition example1 : term := ƛ "x" ⇒ ⟨ "x" ⟩.
Definition example2 : term := ƛ "x" ⇒ ƛ "y" ⇒ ⟨ "x" ⟩.
Definition example3 : term := (ƛ "x" ⇒ ⟨ "x" ⟩) · ⟨ "y" ⟩.
Definition example4 : term := ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "x" ⟩.

(* PAGE:VARS *)
Fixpoint Vars (e : term) : list Var :=
  match e with
  | ⟨ x ⟩ => [x]
  | e · f => Vars e ++ Vars f
  | ƛ x ⇒ e => x :: Vars e
  end.

Example example5 : Vars ⟨ "x" ⟩ = ["x"].
Proof. reflexivity. Qed.

Example example6 : Vars (ƛ "x" ⇒ ⟨ "x" ⟩) = ["x"; "x"].
Proof. reflexivity. Qed.

Example example7 : Vars (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) = ["x"; "x"; "y"].
Proof. reflexivity. Qed.

(* PAGE:FV *)
Fixpoint FV (e : term) : list Var :=
  match e with
  | ⟨ x ⟩ => [x]
  | e · f => FV e ++ FV f
  | ƛ x ⇒ e => diff (FV e) [x]
  end.

Example example8 : FV (ƛ "x" ⇒ ⟨ "x" ⟩) = [].
Proof. reflexivity. Qed.

Example example9 : FV (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) = ["y"].
Proof. reflexivity. Qed.

Example example10 : FV ((ƛ "x" ⇒ ⟨ "x" ⟩) · ⟨ "x" ⟩) = ["x"].
Proof. reflexivity. Qed.

(* PAGE:NAME-SWAP *)
Definition swap_name (z x y : Var) : Var :=
  if String.eqb z x then y else if String.eqb z y then x else z.

Notation "z [ x ↔ y ]ₙ" := (swap_name z x y)
  (at level 7, x at next level, y at next level).

Example example11 : "x" [ "x" ↔ "y" ]ₙ = "y".
Proof. reflexivity. Qed.

Example example12 : "y" [ "x" ↔ "y" ]ₙ = "x".
Proof. reflexivity. Qed.

Example example13 : "z" [ "x" ↔ "y" ]ₙ = "z".
Proof. reflexivity. Qed.

(* PAGE:TERM-SWAP *)
Fixpoint swap (e : term) (x y : Var) : term :=
  match e with
  | ⟨ z ⟩ => ⟨ z [ x ↔ y ]ₙ ⟩
  | e · f => swap e x y · swap f x y
  | ƛ z ⇒ e => ƛ (z [ x ↔ y ]ₙ) ⇒ swap e x y
  end.

Notation "e [ x ↔ y ]" := (swap e x y)
  (at level 7, x at next level, y at next level).

Example example14 :
  (⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ] = ⟨ "y" ⟩ · ⟨ "x" ⟩.
Proof. reflexivity. Qed.

Example example15 :
  (ƛ "x" ⇒ ⟨ "x" ⟩) [ "x" ↔ "y" ] = ƛ "y" ⇒ ⟨ "y" ⟩.
Proof. reflexivity. Qed.

Example example16 :
  (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ]
  = ƛ "y" ⇒ ⟨ "y" ⟩ · ⟨ "x" ⟩.
Proof. reflexivity. Qed.

Example example17 :
  (ƛ "x" ⇒ ƛ "y" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ]
  = ƛ "y" ⇒ ƛ "x" ⇒ ⟨ "y" ⟩ · ⟨ "x" ⟩.
Proof. reflexivity. Qed.

Example example18 :
  (ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "z" ⟩) [ "x" ↔ "y" ]
  = ƛ "y" ⇒ ⟨ "y" ⟩ · ⟨ "z" ⟩.
Proof. reflexivity. Qed.

Example example19 :
  (ƛ "z" ⇒ ⟨ "x" ⟩ · ⟨ "z" ⟩) [ "x" ↔ "y" ]
  = ƛ "z" ⇒ ⟨ "y" ⟩ · ⟨ "z" ⟩.
Proof. reflexivity. Qed.

Example example20 :
  ((ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ]) [ "x" ↔ "y" ]
  = ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩.
Proof. reflexivity. Qed.

Example example21 :
  ((ƛ "x" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩) [ "x" ↔ "y" ]) [ "y" ↔ "z" ]
  = ƛ "z" ⇒ ⟨ "z" ⟩ · ⟨ "x" ⟩.
Proof. reflexivity. Qed.

Example example22 :
  ((ƛ "x" ⇒ ƛ "z" ⇒
      (⟨ "x" ⟩ · ⟨ "y" ⟩) · (⟨ "x" ⟩ · ⟨ "z" ⟩) ·
      (⟨ "w" ⟩ · ⟨ "y" ⟩) · (⟨ "z" ⟩ · ⟨ "w" ⟩))
    [ "x" ↔ "y" ]) [ "z" ↔ "w" ]
  = ƛ "y" ⇒ ƛ "w" ⇒
      (⟨ "y" ⟩ · ⟨ "x" ⟩) · (⟨ "y" ⟩ · ⟨ "w" ⟩) ·
      (⟨ "z" ⟩ · ⟨ "x" ⟩) · (⟨ "w" ⟩ · ⟨ "z" ⟩).
Proof. reflexivity. Qed.

(* PAGE:ALPHA *)
Inductive alpha : term -> term -> Prop :=
| alpha_var : forall x,
    alpha ⟨ x ⟩ ⟨ x ⟩
| alpha_app : forall e1 e2 f1 f2,
    alpha e1 f1 ->
    alpha e2 f2 ->
    alpha (e1 · e2) (f1 · f2)
| alpha_lam : forall x y e f (z : Var),
    z ∉ (Vars (ƛ x ⇒ e) ++ Vars (ƛ y ⇒ f)) ->
    alpha (e [ x ↔ z ]) (f [ y ↔ z ]) ->
    alpha (ƛ x ⇒ e) (ƛ y ⇒ f).

Notation "e ≈α f" := (alpha e f) (at level 70).

Example example23 : ⟨ "x" ⟩ ≈α ⟨ "x" ⟩.
Proof. constructor. Qed.

Example example24 : ~ (⟨ "x" ⟩ ≈α ⟨ "y" ⟩).
Proof. intros H. inversion H. Qed.

Example example25 : (ƛ "x" ⇒ ⟨ "x" ⟩) ≈α (ƛ "y" ⇒ ⟨ "y" ⟩).
Proof.
  eapply alpha_lam with (z := "z").
  - reflexivity.
  - constructor.
Qed.

Example example26 : ⟨ "x" ⟩ · ⟨ "y" ⟩ ≈α ⟨ "x" ⟩ · ⟨ "y" ⟩.
Proof. constructor; constructor. Qed.

Example example27 :
  ~ (⟨ "x" ⟩ · ⟨ "y" ⟩ ≈α ⟨ "w" ⟩ · ⟨ "z" ⟩).
Proof. intros H. inversion H; subst. inversion H3. Qed.

Example example28 :
  (ƛ "x" ⇒ ƛ "y" ⇒ ⟨ "x" ⟩ · ⟨ "y" ⟩)
  ≈α (ƛ "a" ⇒ ƛ "b" ⇒ ⟨ "a" ⟩ · ⟨ "b" ⟩).
Proof.
  eapply alpha_lam with (z := "u").
  - reflexivity.
  - eapply alpha_lam with (z := "v").
    + reflexivity.
    + constructor; constructor.
Qed.

(* The Agda source leaves the false positive as a commented-out hole, then
   proves that any such evidence would be contradictory. *)
Example example30 :
  ~ ((ƛ "x" ⇒ ⟨ "x" ⟩) ≈α (ƛ "y" ⇒ ⟨ "x" ⟩)).
Proof.
  intros H. inversion H; subst.
  simpl in H3, H5.
  assert (Ezx : String.eqb z "x" = false).
  { unfold fresh in H3. simpl in H3.
    destruct (String.eqb z "x") eqn:E; simpl in H3; try discriminate.
    reflexivity. }
  assert (Exz : String.eqb "x" z = false).
  { rewrite String.eqb_sym. exact Ezx. }
  change (⟨ z ⟩ ≈α ⟨ if String.eqb "x" z then "y" else "x" ⟩) in H5.
  rewrite Exz in H5. simpl in H5.
  inversion H5; subst.
  rewrite String.eqb_refl in Ezx. discriminate.
Qed.

(* Navier–Stokes Lean: https://github.com/openai/NavierStokesAndEuler *)
