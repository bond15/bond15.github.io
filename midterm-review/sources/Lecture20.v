(** * Lecture 20: Subtyping — the declarative system

    CSE 590, Fall 2026.  Monday's language and rules, in Rocq:
    the simply typed λ-calculus with records, and the declarative
    subtyping relation of Pierce, chapter 15.

    - Part 1  The language: STLC with records
    - Part 2  Declarative subtyping (chapter 15)
    - Part 3  Typing, with subsumption
    - Part 4  The running example, typed *)

From Coq Require Import ZArith Bool String List Permutation.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* ================================================================= *)
(** * Part 1: The language *)

Definition name := string.
Definition label := string.

(** τ ::= int | bool | τ1 → τ2 | 1 | 0 | {ℓ1:τ1, …, ℓn:τn}

    A record type is a list of labelled types.  1 is the top type and
    0 the bottom type, as in Kozen; Pierce calls them Top and Bot. *)
Inductive ty : Type :=
| TInt
| TBool
| TArr (τ1 τ2 : ty)
| TUnit
| TVoid
| TRcd (fs : list (label * ty)).

(** e ::= n | true | false | () | x | λx:τ. e | e1 e2
        | if e then e1 else e2 | {ℓ1 = e1, …, ℓn = en} | e.ℓ *)
Inductive exp : Type :=
| Num (n : Z)
| Tru
| Fls
| Unit
| Var (x : name)
| Lam (x : name) (τ : ty) (e : exp)
| App (e1 e2 : exp)
| If (e e1 e2 : exp)
| Rcd (fs : list (label * exp))
| Proj (e : exp) (l : label).

(** Notation, so that terms and types read as on the board.  Types get
    their own scope.  A field is written ℓ ∶ τ (a type) or ℓ ∶ e (a
    term), and a record ⦃ f1 , … , fn ⦄. *)
Declare Scope ty_scope.
Delimit Scope ty_scope with ty.
Bind Scope ty_scope with ty.
Notation "'INT'" := TInt.
Notation "'BOOL'" := TBool.
Notation "'ONE'" := TUnit.
Notation "'ZERO'" := TVoid.
Notation "τ1 ⇒ τ2" := (TArr τ1 τ2) (at level 60, right associativity) : ty_scope.
Notation "l ∶ v" := (pair l v) (at level 59, no associativity).
Notation "⦃ ⦄" := (TRcd nil) : ty_scope.
Notation "⦃ f1 , .. , fn ⦄" := (TRcd (cons f1 .. (cons fn nil) ..)) : ty_scope.
Arguments TArr (_ _)%ty.
Arguments TRcd _%ty.
Arguments Lam _ _%ty _.

Notation "'const' n" := (Num n) (at level 1, n at level 0).
Notation "'TRUE'" := Tru.
Notation "'FALSE'" := Fls.
Notation "'UNIT'" := Unit.
Notation "'var' x" := (Var x) (at level 1, x at level 0).
Notation "'λ' x : τ , e" := (Lam x τ e)
  (at level 99, x at level 0, τ at level 99, e at level 99).
Notation "e1 · e2" := (App e1 e2) (at level 40, left associativity).
Notation "'IF' e 'THEN' e1 'ELSE' e2 'FI'" := (If e e1 e2) (at level 80).
Notation "⦃ ⦄" := (Rcd nil).
Notation "⦃ f1 , .. , fn ⦄" := (Rcd (cons f1 .. (cons fn nil) ..)).
Notation "e ∙ l" := (Proj e l) (at level 2, left associativity).

Definition x : name := "x".
Definition y : name := "y".
Definition z : name := "z".
Definition r : name := "r".

(** Monday's two programs: p has an x and a y; getx only reads x. *)
Definition p : exp := ⦃ "x" ∶ const 1 , "y" ∶ const 2 ⦄.
Definition getx : exp := λ r : ⦃ "x" ∶ INT ⦄ , var r ∙ "x".

(* ================================================================= *)
(** * Part 2: Declarative subtyping *)

Reserved Notation "σ <: τ" (at level 70).

(** The rules of chapter 15 (figures 15-1, 15-3, 15-4), with 1 for Top
    and 0 for Bot.  Depth subtyping needs "fieldwise", so it is a
    second relation defined together with the first. *)
Inductive sub : ty -> ty -> Prop :=
| s_refl τ :
    τ <: τ
| s_trans σ τ ρ :
    σ <: τ -> τ <: ρ ->
    σ <: ρ
| s_top τ :
    τ <: ONE
| s_bot τ :
    ZERO <: τ
| s_arrow σ1 σ2 τ1 τ2 :
    τ1 <: σ1 -> σ2 <: τ2 ->
    σ1 ⇒ σ2 <: τ1 ⇒ τ2
| s_width fs gs :
    TRcd (fs ++ gs)%list <: TRcd fs
| s_depth fs gs :
    sub_fields fs gs ->
    TRcd fs <: TRcd gs
| s_perm fs gs :
    Permutation fs gs ->
    TRcd fs <: TRcd gs
with sub_fields : list (label * ty) -> list (label * ty) -> Prop :=
| sf_nil :
    sub_fields [] []
| sf_cons l σ τ fs gs :
    σ <: τ -> sub_fields fs gs ->
    sub_fields ((l ∶ σ) :: fs) ((l ∶ τ) :: gs)
where "σ <: τ" := (sub σ τ).

(** ** Three derivations *)

(** Width: a record with more fields is a subtype.  The rule drops a
    suffix: {x:int, y:int} is {x:int} ++ {y:int}. *)
Example width_xy : ⦃ "x" ∶ INT , "y" ∶ INT ⦄ <: ⦃ "x" ∶ INT ⦄.
Proof.
  apply (s_width [ "x" ∶ INT ] [ "y" ∶ INT ]).
Qed.

(** To drop a field from the front, permute first, then drop:
    {x:int, y:int} <: {y:int, x:int} <: {y:int}. *)
Example width_perm : ⦃ "x" ∶ INT , "y" ∶ INT ⦄ <: ⦃ "y" ∶ INT ⦄.
Proof.
  apply s_trans with (τ := (⦃ "y" ∶ INT , "x" ∶ INT ⦄)%ty).
  - apply s_perm. apply perm_swap.
  - apply (s_width [ "y" ∶ INT ] [ "x" ∶ INT ]).
Qed.

(** Functions: contravariant in the argument, covariant in the result.
    A function on {x:int} can be used on {x:int, y:int} inputs, and its
    int result can be forgotten to 1. *)
Example arrow_ex :
  ⦃ "x" ∶ INT ⦄ ⇒ INT <: ⦃ "x" ∶ INT , "y" ∶ INT ⦄ ⇒ ONE.
Proof.
  apply s_arrow.
  - (* argument side, flipped: {x:int, y:int} <: {x:int} *)
    exact width_xy.
  - (* result side: int <: 1 *)
    apply s_top.
Qed.

(* ================================================================= *)
(** * Part 3: Typing, with subsumption *)

Definition ctx := list (name * ty).

Fixpoint lookup (Γ : ctx) (x : name) : option ty :=
  match Γ with
  | [] => None
  | (y ∶ τ) :: Γ' => if String.eqb x y then Some τ else lookup Γ' x
  end.

(** The type of field ℓ in a record type, if it has one. *)
Fixpoint field (fs : list (label * ty)) (l : label) : option ty :=
  match fs with
  | [] => None
  | (l' ∶ τ) :: fs' => if String.eqb l l' then Some τ else field fs' l
  end.

Reserved Notation "Γ ⊢ e : τ" (at level 70, e at level 99, τ at level 69).

(** Lecture 16's rules, the two record rules, and subsumption.  A
    record is typed fieldwise, so typing is also two relations. *)
Inductive has_type : ctx -> exp -> ty -> Prop :=
| t_num Γ n :
    Γ ⊢ const n : INT
| t_true Γ :
    Γ ⊢ TRUE : BOOL
| t_false Γ :
    Γ ⊢ FALSE : BOOL
| t_unit Γ :
    Γ ⊢ UNIT : ONE
| t_var Γ x τ :
    lookup Γ x = Some τ ->
    Γ ⊢ var x : τ
| t_lam Γ x τ1 e τ2 :
    (x ∶ τ1) :: Γ ⊢ e : τ2 ->
    Γ ⊢ λ x : τ1 , e : τ1 ⇒ τ2
| t_app Γ e1 e2 τ1 τ2 :
    Γ ⊢ e1 : τ1 ⇒ τ2 -> Γ ⊢ e2 : τ1 ->
    Γ ⊢ e1 · e2 : τ2
| t_if Γ e e1 e2 τ :
    Γ ⊢ e : BOOL -> Γ ⊢ e1 : τ -> Γ ⊢ e2 : τ ->
    Γ ⊢ IF e THEN e1 ELSE e2 FI : τ
| t_rcd Γ es τs :
    has_type_fields Γ es τs ->
    Γ ⊢ Rcd es : TRcd τs
| t_proj Γ e τs l τ :
    Γ ⊢ e : TRcd τs -> field τs l = Some τ ->
    Γ ⊢ e ∙ l : τ
| t_sub Γ e σ τ :
    Γ ⊢ e : σ -> σ <: τ ->
    Γ ⊢ e : τ
with has_type_fields : ctx -> list (label * exp) -> list (label * ty) -> Prop :=
| tf_nil Γ :
    has_type_fields Γ [] []
| tf_cons Γ l e τ es τs :
    Γ ⊢ e : τ -> has_type_fields Γ es τs ->
    has_type_fields Γ ((l ∶ e) :: es) ((l ∶ τ) :: τs)
where "Γ ⊢ e : τ" := (has_type Γ e τ).

Notation "⊢ e : τ" := (has_type [] e τ)
  (at level 70, e at level 99, τ at level 69).

(** ** The two operands *)

(** p : {x:int, y:int}, one field at a time. *)
Example p_type : ⊢ p : ⦃ "x" ∶ INT , "y" ∶ INT ⦄.
Proof.
  unfold p.
  apply t_rcd.
  apply tf_cons. { apply t_num. }
  apply tf_cons. { apply t_num. }
  apply tf_nil.
Qed.

(** getx : {x:int} → int.  Under the λ, r : {x:int}, and r.x reads
    the field x of that type. *)
Example getx_type : ⊢ getx : ⦃ "x" ∶ INT ⦄ ⇒ INT.
Proof.
  unfold getx.
  apply t_lam.
  apply t_proj with (τs := [ "x" ∶ INT ]).
  - apply t_var. reflexivity.
  - reflexivity.
Qed.

(* ================================================================= *)
(** * Part 4: The running example *)

(** Without subsumption, getx p is rejected: the application rule
    needs p : {x:int}, and the record rule only gives p : {x:int, y:int}.
    Subsumption bridges the gap with {x:int, y:int} <: {x:int}. *)
Example getx_p : ⊢ getx · p : INT.
Proof.
  apply t_app with (τ1 := (⦃ "x" ∶ INT ⦄)%ty).
  - exact getx_type.
  - apply t_sub with (σ := (⦃ "x" ∶ INT , "y" ∶ INT ⦄)%ty).
    + exact p_type.
    + exact width_xy.
Qed.

Print Assumptions getx_p.
