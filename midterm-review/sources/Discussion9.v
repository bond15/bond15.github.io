(** * Program equivalence

    CSE 590, Fall 2026.  Lectures 17 and 18.

    - Part 0  The language, from Discussion 6
    - Part 1  Contextual equivalence
    - Part 2  Denotational equivalence
    - Part 3  β and η at every type, checked in the model *)

From Coq Require Import ZArith String List.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* ================================================================= *)
(** * Part 0: The language *)

(** Discussion 6's simply typed λ-calculus, without the commentary. *)

Definition name := string.

Inductive ty : Type :=
| TInt
| TBool
| TArr (τ1 τ2 : ty).

Inductive exp : Type :=
| Num (n : Z)
| Tru
| Fls
| Var (x : name)
| Lam (x : name) (τ : ty) (e : exp)
| App (e1 e2 : exp)
| Plus (e1 e2 : exp)
| If (e e1 e2 : exp).

Notation "'INT'" := TInt.
Notation "'BOOL'" := TBool.
Notation "τ1 ⇒ τ2" := (TArr τ1 τ2) (at level 30, right associativity).

Notation "'const' n" := (Num n) (at level 1, n at level 0).
Notation "'TRUE'" := Tru.
Notation "'FALSE'" := Fls.
Notation "'var' x" := (Var x) (at level 1, x at level 0).
Notation "'λ' x : τ , e" := (Lam x τ e)
  (at level 99, x at level 0, τ at level 99, e at level 99).
Notation "e1 · e2" := (App e1 e2) (at level 40, left associativity).
Notation "e1 ⊕ e2" := (Plus e1 e2) (at level 50, left associativity).
Notation "'IF' e 'THEN' e1 'ELSE' e2 'FI'" := (If e e1 e2) (at level 80).

(** ** Values *)

Inductive value : exp -> Prop :=
| v_num n : value (const n)
| v_true : value TRUE
| v_false : value FALSE
| v_lam x τ e : value (λ x : τ , e).

Definition val : Type := { e : exp | value e }.
Definition exp_of (v : val) : exp := proj1_sig v.

(** ** Substitution and redexes *)

Fixpoint subst (x : name) (v : exp) (e : exp) : exp :=
  match e with
  | const n => const n
  | TRUE => TRUE
  | FALSE => FALSE
  | var y => if String.eqb y x then v else var y
  | λ y : τ , body =>
      if String.eqb y x then λ y : τ , body
      else λ y : τ , subst x v body
  | e1 · e2 => subst x v e1 · subst x v e2
  | e1 ⊕ e2 => subst x v e1 ⊕ subst x v e2
  | IF e THEN e1 ELSE e2 FI =>
      IF subst x v e THEN subst x v e1 ELSE subst x v e2 FI
  end.

Notation "e [ x ↦ v ]" := (subst x v e) (at level 2, x at level 99).

Inductive redex : exp -> exp -> Prop :=
| r_beta x τ e v : value v -> redex ((λ x : τ , e) · v) (e [x ↦ v])
| r_plus n1 n2 : redex (const n1 ⊕ const n2) (const (n1 + n2))
| r_if_true e1 e2 : redex (IF TRUE THEN e1 ELSE e2 FI) e1
| r_if_false e1 e2 : redex (IF FALSE THEN e1 ELSE e2 FI) e2.

Notation "e '⟶r' e'" := (redex e e') (at level 70).

(** ** Evaluation contexts and steps *)

Inductive ectx : Type :=
| Hole
| AppL (E : ectx) (e2 : exp)
| AppR (v : val) (E : ectx)
| PlusL (E : ectx) (e2 : exp)
| PlusR (n : Z) (E : ectx)
| IfC (E : ectx) (e1 e2 : exp).

Fixpoint plug (E : ectx) (e : exp) : exp :=
  match E with
  | Hole => e
  | AppL E e2 => plug E e · e2
  | AppR v E => exp_of v · plug E e
  | PlusL E e2 => plug E e ⊕ e2
  | PlusR n E => const n ⊕ plug E e
  | IfC E e1 e2 => IF plug E e THEN e1 ELSE e2 FI
  end.

Notation "E [ e ]" := (plug E e) (at level 2, e at level 99).

Reserved Notation "e '⟶' e'" (at level 70).

Inductive step : exp -> exp -> Prop :=
| s_ctx E r r' : redex r r' -> E [r] ⟶ E [r']
where "e ⟶ e'" := (step e e').

Reserved Notation "e '⟶*' e'" (at level 70).

Inductive multi : exp -> exp -> Prop :=
| m_refl e : e ⟶* e
| m_step e1 e2 e3 : e1 ⟶ e2 -> e2 ⟶* e3 -> e1 ⟶* e3
where "e ⟶* e'" := (multi e e').

(** ** Typing *)

Definition ctx := list (name * ty).

Fixpoint lookup {A : Type} (Γ : list (name * A)) (y : name) : option A :=
  match Γ with
  | nil => None
  | (x, a) :: Γ' => if String.eqb y x then Some a else lookup Γ' y
  end.

Reserved Notation "Γ ⊢ e : τ" (at level 70, e at level 99, τ at level 69).

Inductive has_type : ctx -> exp -> ty -> Prop :=
| t_num Γ n :
    Γ ⊢ const n : INT
| t_true Γ :
    Γ ⊢ TRUE : BOOL
| t_false Γ :
    Γ ⊢ FALSE : BOOL
| t_var Γ x τ :
    lookup Γ x = Some τ ->
    Γ ⊢ var x : τ
| t_lam Γ x τ1 e τ2 :
    (x, τ1) :: Γ ⊢ e : τ2 ->
    Γ ⊢ λ x : τ1 , e : τ1 ⇒ τ2
| t_app Γ e1 e2 τ1 τ2 :
    Γ ⊢ e1 : τ1 ⇒ τ2 -> Γ ⊢ e2 : τ1 ->
    Γ ⊢ e1 · e2 : τ2
| t_plus Γ e1 e2 :
    Γ ⊢ e1 : INT -> Γ ⊢ e2 : INT ->
    Γ ⊢ e1 ⊕ e2 : INT
| t_if Γ e e1 e2 τ :
    Γ ⊢ e : BOOL -> Γ ⊢ e1 : τ -> Γ ⊢ e2 : τ ->
    Γ ⊢ IF e THEN e1 ELSE e2 FI : τ
where "Γ ⊢ e : τ" := (has_type Γ e τ).

Notation "⊢ e : τ" := (has_type nil e τ)
  (at level 70, e at level 99, τ at level 69).

(* ================================================================= *)
(** * Part 1: Contextual equivalence *)

(** ** Closed Booleans *)

(** Two closed Boolean programs are equivalent when running them gives
    the same answer: both true, or both false. *)
Definition cl_bool (e e' : exp) : Prop :=
  (e ⟶* TRUE /\ e' ⟶* TRUE) \/ (e ⟶* FALSE /\ e' ⟶* FALSE).

(** true and (λx:int. true) 5: one is a value, the other reduces to it
    in one step. *)
Example cl_bool_ex : cl_bool TRUE ((λ "x" : INT , TRUE) · const 5).
Proof.
  left. split.
  - apply m_refl.
  - apply m_step with (e2 := TRUE).
    + apply (s_ctx Hole). apply r_beta. apply v_num.
    + apply m_refl.
Qed.

(** ** Contexts *)

(** C ::= [] | λx:τ. C | C e | e C | C + e | e + C
        | if C then e1 else e2 | if e then C else e2 | if e then e1 else C

    A term with one hole, anywhere.  Unlike an evaluation context, the
    hole may sit under a λ, and the other positions are any e, not v. *)
Inductive gctx : Type :=
| GHole
| GLam (x : name) (τ : ty) (C : gctx)
| GAppL (C : gctx) (e2 : exp)
| GAppR (e1 : exp) (C : gctx)
| GPlusL (C : gctx) (e2 : exp)
| GPlusR (e1 : exp) (C : gctx)
| GIf (C : gctx) (e1 e2 : exp)
| GIfL (e : exp) (C : gctx) (e2 : exp)
| GIfR (e e1 : exp) (C : gctx).

(** C⟨e⟩ puts e in the hole.  Under λx the hole captures: a free x in
    e is bound by the context's λ. *)
Fixpoint gplug (C : gctx) (e : exp) : exp :=
  match C with
  | GHole => e
  | GLam x τ C => λ x : τ , gplug C e
  | GAppL C e2 => gplug C e · e2
  | GAppR e1 C => e1 · gplug C e
  | GPlusL C e2 => gplug C e ⊕ e2
  | GPlusR e1 C => e1 ⊕ gplug C e
  | GIf C e1 e2 => IF gplug C e THEN e1 ELSE e2 FI
  | GIfL e0 C e2 => IF e0 THEN gplug C e ELSE e2 FI
  | GIfR e0 e1 C => IF e0 THEN e1 ELSE gplug C e FI
  end.

Notation "C ⟨ e ⟩" := (gplug C e) (at level 2, e at level 99).

(** Capture: (λx:int. [])⟨x⟩ = λx:int. x. *)
Example capture : (GLam "x" INT GHole) ⟨ var "x" ⟩ = λ "x" : INT , var "x".
Proof. reflexivity. Qed.

(** C : (Γ ⊢ τ) ⇒ (Γ' ⊢ τ'): plugging a term of type τ under Γ gives a
    term of type τ' under Γ'. *)
Definition ctx_type (C : gctx) (Γ : ctx) (τ : ty) (Γ' : ctx) (τ' : ty) : Prop :=
  forall e, Γ ⊢ e : τ -> Γ' ⊢ C ⟨ e ⟩ : τ'.

(** ** The definition *)

(** Γ ⊢ e, e' : τ are contextually equivalent when every closing
    Boolean context gives them the same answer. *)
Definition ctx_equiv (Γ : ctx) (τ : ty) (e e' : exp) : Prop :=
  forall C, ctx_type C Γ τ nil BOOL -> cl_bool (C ⟨ e ⟩) (C ⟨ e' ⟩).

(** ** Congruence and adequacy *)

(** A context inside a context.  (compose C C')⟨e⟩ = C⟨C'⟨e⟩⟩. *)
Fixpoint gcompose (C C' : gctx) : gctx :=
  match C with
  | GHole => C'
  | GLam x τ C => GLam x τ (gcompose C C')
  | GAppL C e2 => GAppL (gcompose C C') e2
  | GAppR e1 C => GAppR e1 (gcompose C C')
  | GPlusL C e2 => GPlusL (gcompose C C') e2
  | GPlusR e1 C => GPlusR e1 (gcompose C C')
  | GIf C e1 e2 => GIf (gcompose C C') e1 e2
  | GIfL e0 C e2 => GIfL e0 (gcompose C C') e2
  | GIfR e0 e1 C => GIfR e0 e1 (gcompose C C')
  end.

Lemma gplug_compose C C' e : (gcompose C C') ⟨ e ⟩ = C ⟨ C' ⟨ e ⟩ ⟩.
Proof.
  induction C; simpl; try rewrite IHC; reflexivity.
Qed.

(** Congruence: equivalent terms stay equivalent inside any context.
    Given a closing context C' for the results, C' with C inside it
    is a closing context for the originals. *)
Theorem congruence Γ τ Γ' τ' e e' C :
  ctx_type C Γ τ Γ' τ' ->
  ctx_equiv Γ τ e e' ->
  ctx_equiv Γ' τ' (C ⟨ e ⟩) (C ⟨ e' ⟩).
Proof.
  intros HC He C' HC'.
  rewrite <- (gplug_compose C' C e), <- (gplug_compose C' C e').
  apply He.
  intros e0 He0. rewrite gplug_compose. apply HC'. apply HC. apply He0.
Qed.

(** Adequacy: at closed Booleans, contextual equivalence is the
    closed equivalence.  Take the context to be the hole. *)
Theorem adequacy e e' : ctx_equiv nil BOOL e e' -> cl_bool e e'.
Proof.
  intros H. apply (H GHole). intros e0 He0. apply He0.
Qed.

(* ================================================================= *)
(** * Part 2: Denotational equivalence *)

(** The meanings of true and (λx:int. true) 5, as functions out of the
    one-element set ⟦·⟧ = unit.  Equal functions: Rocq computes the
    application. *)
Definition den_true : unit -> bool := fun _ => true.
Definition den_app : unit -> bool := fun _ => (fun (x : Z) => true) 5.

Example den_equal : den_true = den_app.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** * Part 3: β and η at every type, checked in the model *)

(** The model is Rocq's own types, as in Discussion 7: a type τ is
    a Rocq type, a term with a free variable is a Rocq function of
    that variable.  Each β or η law is then an equation between
    Rocq terms, and the proof is to compute, or to take a value apart. *)
Section BetaEta.

Variables A B C : Type.

(** ** Functions: intro λ, elim application *)

(** β: a λ applied to anything is its body with the argument put in.
    Any argument e', not only a value: Rocq computes it either way. *)
Lemma beta_fun (e : A -> B) (e' : A) : (fun x => e x) e' = e e'.
Proof. reflexivity. Qed.

(** η: a function is the λ that applies it. *)
Lemma eta_fun (e : A -> B) : e = fun x => e x.
Proof. reflexivity. Qed.

(** η', the extensionality form: two functions are equal when they
    agree on a fresh variable x.  Rocq's own equality does not include
    this, so it is assumed, as in Discussion 7. *)
Axiom funext : forall (f g : A -> B), (forall x, f x = g x) -> f = g.

(** ** Products: intro pairing, elim projections *)

Lemma beta_prod_1 (e1 : A) (e2 : B) : fst (e1, e2) = e1.
Proof. reflexivity. Qed.

Lemma beta_prod_2 (e1 : A) (e2 : B) : snd (e1, e2) = e2.
Proof. reflexivity. Qed.

(** η: a pair is the pair of its projections.  Take e apart. *)
Lemma eta_prod (e : A * B) : e = (fst e, snd e).
Proof. destruct e as [a b]. reflexivity. Qed.

(** η': equal projections, equal pairs. *)
Lemma eta_prod' (e e' : A * B) : fst e = fst e' -> snd e = snd e' -> e = e'.
Proof.
  destruct e as [a b]. destruct e' as [a' b']. simpl.
  intros H1 H2. rewrite H1, H2. reflexivity.
Qed.

(** ** Unit: intro (), no elim *)

(** No β.  η: every e : 1 is (). *)
Lemma eta_unit (e : unit) : e = tt.
Proof. destruct e. reflexivity. Qed.

Lemma eta_unit' (e e' : unit) : e = e'.
Proof. destruct e. destruct e'. reflexivity. Qed.

(** ** Sums: intro inl, inr, elim case *)

Lemma beta_sum_l (e : A) (e1 : A -> C) (e2 : B -> C) :
  match inl e with inl x1 => e1 x1 | inr x2 => e2 x2 end = e1 e.
Proof. reflexivity. Qed.

Lemma beta_sum_r (e : B) (e1 : A -> C) (e2 : B -> C) :
  match inr e with inl x1 => e1 x1 | inr x2 => e2 x2 end = e2 e.
Proof. reflexivity. Qed.

(** Weak η: a sum is the case that rebuilds it. *)
Lemma eta_sum_weak (e : A + B) :
  e = match e with inl x1 => inl x1 | inr x2 => inr x2 end.
Proof. destruct e as [a | b]; reflexivity. Qed.

(** Strong η.  A term e with a free variable x of sum type is a
    function f of x.  Then e[e'/x] is f e', and it equals a case on
    e' whose branches are e with inl x1, inr x2 for x. *)
Lemma eta_sum_strong (e' : A + B) (f : A + B -> C) :
  f e' = match e' with inl x1 => f (inl x1) | inr x2 => f (inr x2) end.
Proof. destruct e' as [a | b]; reflexivity. Qed.

(** The commuting conversion for Booleans: an if inside e moves out,
    with e pushed into both branches. *)
Lemma commute_if (b : bool) (e2 e3 : A) (f : A -> C) :
  f (if b then e2 else e3) = if b then f e2 else f e3.
Proof. destruct b; reflexivity. Qed.

(** ** Zero: no intro, elim the empty case *)

(** No β.  Strong η: a term with a free variable of type 0, at any
    e' : 0, is the empty case on e'.  Nothing to compute: there is no
    e' to take apart. *)
Lemma eta_zero (e' : Empty_set) (f : Empty_set -> C) :
  f e' = match e' with end.
Proof. destruct e'. Qed.

(** The dead-code reading: with any way to make a 0 in scope, every
    term is equal to the empty case, whether or not it mentions 0. *)
Lemma dead_code (g : unit -> Empty_set) (e : C) : e = match g tt with end.
Proof. destruct (g tt). Qed.

End BetaEta.

(** The lecture's first example, in the model: (λx:int. true) 5 = true. *)
Example first_example : (fun (x : Z) => true) 5 = true.
Proof. reflexivity. Qed.

Print Assumptions eta_sum_strong.
