(** * The simply typed λ-calculus

    CSE 590, Fall 2026.  Lectures 12 and 13.

    - Part 1  Expressions                                    (slide 5)
    - Part 2  Evaluation                                     (slides 6-7)
    - Part 3  Typing                                         (slide 8)
    - Part 4  Type soundness                                 (slide 9) *)

From Coq Require Import ZArith String List.
Open Scope Z_scope.
Open Scope string_scope.

(* ================================================================= *)
(** * Part 1: Expressions *)

(** Variables are names, written as strings: "x", "f", ... *)
Definition name := string.

(** τ ::= int | bool | τ1 → τ2

    A λ says what type its argument has, so the expressions mention
    types.  That is all we use types for here. *)
Inductive ty : Type :=
| TInt
| TBool
| TArr (τ1 τ2 : ty).

(** e ::= n | true | false | x | λx:τ. e | e1 e2 | e1 + e2
        | if e then e1 else e2

    One constructor per form:

        n                      Num n
        true, false            Tru, Fls
        x                      Var x
        λx:τ. e                Lam x τ e
        e1 e2                  App e1 e2      (apply e1 to e2)
        e1 + e2                Plus e1 e2
        if e then e1 else e2   If e e1 e2                             *)
Inductive exp : Type :=
| Num (n : Z)
| Tru
| Fls
| Var (x : name)
| Lam (x : name) (τ : ty) (e : exp)
| App (e1 e2 : exp)
| Plus (e1 e2 : exp)
| If (e e1 e2 : exp).

(** Concrete syntax, in the same style as Discussion 5.  [const n] is
    the number n and [var x] is the variable x, as expressions.  The
    language's symbols are different from Rocq's, so they can't be
    confused:

        in the language     in Rocq
        ⊕                   +           (addition)
        TRUE, FALSE         true, false (Booleans)
        INT, BOOL           Z, bool     (types)
        ⇒                   ->          (function types)

    Application e1 e2 is written e1 · e2. *)
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

(** ** Examples *)

(** 1 + 2 *)
Definition one_plus_two : exp := const 1 ⊕ const 2.

(** λx:int. x + 1, the function that adds one *)
Definition succ : exp := λ "x" : INT , var "x" ⊕ const 1.

(** (λx:int. x + 1) 2, the function applied to 2 *)
Definition succ_two : exp := succ · const 2.

(** λf:int → int. λx:int. f (f x), apply f twice *)
Definition twice : exp :=
  λ "f" : INT ⇒ INT , λ "x" : INT , var "f" · (var "f" · var "x").

(** The notation is only a way of writing the constructors: *)
Example succ_is : succ = Lam "x" TInt (Plus (Var "x") (Num 1)).
Proof. reflexivity. Qed.

(** The grammar also allows expressions that make no sense, like
    true + 1.  Ruling those out is what the type system is for. *)
Definition nonsense : exp := TRUE ⊕ const 1.

(* ================================================================= *)
(** * Part 2: Evaluation *)

(** v ::= n | true | false | λx:τ. e

    A value is a finished answer: there is nothing left to compute.
    [value e] says that e is one of these four forms.  Note that a λ is
    a value whatever its body is: evaluation doesn't look inside it. *)
Inductive value : exp -> Prop :=
| v_num n : value (const n)
| v_true : value TRUE
| v_false : value FALSE
| v_lam x τ e : value (λ x : τ , e).

(** Values are a subset of expressions.  This is how Rocq represents a
    subset: for a type A and a property P,

        { x : A | P x }

    is the type of the x's in A that have property P (a "sigma type",
    or subset type).  An element of it is a pair: an x, together with a
    proof of P x.

    So the values, as a type, are { e : exp | value e }: an expression
    together with a proof that it is a value.  [exp_of v] forgets the
    proof and gives back the expression. *)
Definition val : Type := { e : exp | value e }.

Definition exp_of (v : val) : exp := proj1_sig v.

(** ** Redexes *)

(** e[x ↦ v] puts v in place of the free x's in e.  We only ever
    substitute closed values, so no bound variable needs renaming. *)
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

(** The four rules that do the real work, as their own step.  The
    expression on the left is a REDEX (a "reducible expression"). *)
Inductive redex : exp -> exp -> Prop :=
| r_beta x τ e v : value v -> redex ((λ x : τ , e) · v) (e [x ↦ v])
| r_plus n1 n2 : redex (const n1 ⊕ const n2) (const (n1 + n2))
| r_if_true e1 e2 : redex (IF TRUE THEN e1 ELSE e2 FI) e1
| r_if_false e1 e2 : redex (IF FALSE THEN e1 ELSE e2 FI) e2.

(** e ⟶r e' is the redex step. *)
Notation "e '⟶r' e'" := (redex e e') (at level 70).

(** ** Evaluation contexts *)

(** E ::= • | E e | v E | E + e | n + E | if E then e1 else e2

    An evaluation context is an expression with one hole • in it, at
    the place where the next step happens.  There is no λx:τ. E:
    evaluation never looks inside a λ.

    In Rocq each kind of context gets a constructor.  The hole is
    [Hole].  In v E the v has to be a value, so it is a [val]. *)
Inductive ectx : Type :=
| Hole                               (* •                     *)
| AppL (E : ectx) (e2 : exp)         (* E e2                  *)
| AppR (v : val) (E : ectx)          (* v E                   *)
| PlusL (E : ectx) (e2 : exp)        (* E + e2                *)
| PlusR (n : Z) (E : ectx)           (* n + E                 *)
| IfC (E : ectx) (e1 e2 : exp).      (* if E then e1 else e2  *)

(** E[e] fills the hole of E with e. *)
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

(** ** Steps, with evaluation contexts *)

(** One rule: take the redex r out of its context E, do the work, and
    put the result back.

        r ⟶redex r'
        ──────────────
        E[r] ⟶ E[r']

    With E = • this is one of the four redex rules.  Every other kind
    of E is one of the five rules that only say where to look. *)
Reserved Notation "e '⟶' e'" (at level 70).

Inductive step : exp -> exp -> Prop :=
| s_ctx E r r' : redex r r' -> E [r] ⟶ E [r']
where "e ⟶ e'" := (step e e').

(** (1 + 2) + 3 ⟶ 3 + 3, with E = • + 3 and the redex 1 + 2 ⟶redex 3. *)
Example step_ex : (const 1 ⊕ const 2) ⊕ const 3 ⟶ const 3 ⊕ const 3.
Proof.
  apply (s_ctx (PlusL Hole (const 3))).
  apply r_plus.
Qed.

(** *** A run

    Each step is one use of s_ctx: choose E; the redex is whatever
    fills its hole.  This run uses both holes of an application: first
    the function (E e), then, once it is a value, the argument (v E).

    (λx:int. λy:int. x + y) 1 (1 + 1)
      ⟶ (λy:int. 1 + y) (1 + 1)    E = • (1 + 1)            left hole
      ⟶ (λy:int. 1 + y) 2          E = (λy:int. 1 + y) •    right hole
      ⟶ 1 + 2                      E = •
      ⟶ 3                          E = •

    In the second step the [val] in E is the function together with
    the proof [v_lam] that it is a value. *)
Example run :
  (λ "x" : INT , λ "y" : INT , var "x" ⊕ var "y") · const 1 · (const 1 ⊕ const 1)
    ⟶ (λ "y" : INT , const 1 ⊕ var "y") · (const 1 ⊕ const 1)
  /\ (λ "y" : INT , const 1 ⊕ var "y") · (const 1 ⊕ const 1)
    ⟶ (λ "y" : INT , const 1 ⊕ var "y") · const 2
  /\ (λ "y" : INT , const 1 ⊕ var "y") · const 2 ⟶ const 1 ⊕ const 2
  /\ const 1 ⊕ const 2 ⟶ const 3.
Proof.
  split.
  { (* E = • (1 + 1), redex β (x ↦ 1) *)
    apply (s_ctx (AppL Hole (const 1 ⊕ const 1))). apply r_beta. apply v_num. }
  split.
  { (* E = (λy:int. 1 + y) •, redex 1 + 1 ⟶ 2 *)
    apply (s_ctx (AppR (exist _ _ (v_lam "y" INT (const 1 ⊕ var "y"))) Hole)).
    apply r_plus. }
  split.
  { (* E = •, redex β (y ↦ 2) *)
    apply (s_ctx Hole). apply r_beta. apply v_num. }
  (* E = •, redex 1 + 2 ⟶ 3 *)
  apply (s_ctx Hole). apply r_plus.
Qed.

(** ** Multi-step *)

(** e ⟶* e' : zero or more steps.

        ─────── (refl)        e1 ⟶ e2    e2 ⟶* e3
        e ⟶* e                ──────────────────── (step)
                                   e1 ⟶* e3                          *)
Reserved Notation "e '⟶*' e'" (at level 70).

Inductive multi : exp -> exp -> Prop :=
| m_refl e : e ⟶* e
| m_step e1 e2 e3 : e1 ⟶ e2 -> e2 ⟶* e3 -> e1 ⟶* e3
where "e ⟶* e'" := (multi e e').

(** The run above, as one multi-step: its four steps, then (refl). *)
Example run_multi :
  (λ "x" : INT , λ "y" : INT , var "x" ⊕ var "y") · const 1 · (const 1 ⊕ const 1)
    ⟶* const 3.
Proof.
  destruct run as [s1 [s2 [s3 s4]]].
  apply (m_step _ _ _ s1).
  apply (m_step _ _ _ s2).
  apply (m_step _ _ _ s3).
  apply (m_step _ _ _ s4).
  apply m_refl.
Qed.

(** ** Stuck *)

(** A one-off definition for the example below, so it lives in its own
    Section: a [Let] exists only until [End Stuck].

    e is STUCK when it is not a value and it can't step: evaluation
    hasn't finished, but no rule applies. *)
Section Stuck.

  Let stuck (e : exp) : Prop := ~ value e /\ ~ (exists e', e ⟶ e').

  (** true + 1 is stuck: it is not a value, and it can't step.  For the
      step, go through the ways to write it as E[r]: no redex rule adds a
      Boolean. *)
  Lemma true_plus_one_stuck : stuck (TRUE ⊕ const 1).
  Proof.
    (* stuck means two things; prove each *)
    split.
    - (* not a value: assume it is one; but no value is a sum *)
      intros Hv. inversion Hv.
    - (* can't step: assume a step e'; look at how it was made *)
      intros [e' Hstep].
      inversion Hstep as [E r r' Hr Heq].
      destruct E as [ | E e2 | v E | E e2 | n E | E e1 e2 ]; simpl in Heq.
      + (* E = •: r = true + 1, and no redex rule adds a Boolean *)
        subst r. inversion Hr.
      + (* E e2 is an application, not a sum *)
        discriminate Heq.
      + discriminate Heq.
      + (* E + 1 with E[r] = true: but r is a redex, so E[r] isn't true *)
        injection Heq as Htrue _.
        destruct E; simpl in Htrue; try discriminate Htrue.
        subst r. inversion Hr.
      + (* n + E: n would be true *)
        discriminate Heq.
      + discriminate Heq.
  Qed.

  (** (λx:int. x + 1) true ⟶ true + 1, and true + 1 is stuck: the run
      gets stuck.

      The β step doesn't look at the annotation x:int: evaluation never
      checks types.  Ruling out runs like this is the type system's job. *)
  Example stuck_run :
    (λ "x" : INT , var "x" ⊕ const 1) · TRUE ⟶* TRUE ⊕ const 1
    /\ stuck (TRUE ⊕ const 1).
  Proof.
    split.
    - apply m_step with (e2 := TRUE ⊕ const 1).
      + apply (s_ctx Hole). apply r_beta. apply v_true.
      + apply m_refl.
    - apply true_plus_one_stuck.
  Qed.

End Stuck.

(* ================================================================= *)
(** * Part 3: Typing *)

(** ** Contexts *)

(** Γ ::= · | Γ, x:τ

    A context lists the variables in scope with their types.  In Rocq
    it is a list of (variable, type) pairs: Γ, x:τ puts x:τ at the
    FRONT, written (x, τ) :: Γ, and the empty context · is nil.

    x:τ ∈ Γ means: the first x in Γ, from the front, has type τ.  So in
    Γ, x:int, x:bool the later x:bool wins, just as an inner λx hides
    an outer one. *)
Definition ctx := list (name * ty).

Fixpoint lookup (Γ : ctx) (y : name) : option ty :=
  match Γ with
  | nil => None
  | (x, τ) :: Γ' => if String.eqb y x then Some τ else lookup Γ' y
  end.

(** ** Typing rules *)

(** Γ ⊢ e : τ, "in context Γ, e has type τ": the rules of slide 8,
    one constructor each. *)
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

(** ⊢ e : τ means e has type τ in the empty context: e is closed. *)
Notation "⊢ e : τ" := (has_type nil e τ)
  (at level 70, e at level 99, τ at level 69).

(** ** Examples *)

(**     x:int ∈ x:int
        ───────────────── t_var   ─────────────── t_num
        x:int ⊢ x : int           x:int ⊢ 1 : int
        ───────────────────────────────────────── t_plus
        x:int ⊢ x + 1 : int
        ─────────────────────────── t_lam
        ⊢ λx:int. x + 1 : int → int                                  *)
Example succ_type : ⊢ λ "x" : INT , var "x" ⊕ const 1 : INT ⇒ INT.
Proof.
  apply t_lam.
  apply t_plus.
  - apply t_var. reflexivity.
  - apply t_num.
Qed.

(** The stuck term true + 1 from Part 2 (true_plus_one_stuck) has no
    type: t_plus needs ⊢ true : int, and the only rule for TRUE gives
    bool. *)
Example stuck_untyped : ~ exists τ, ⊢ TRUE ⊕ const 1 : τ.
Proof.
  intros [τ H].
  inversion H as [ | | | | | | Γ e1 e2 Htrue Hone | ]; subst.
  inversion Htrue.
Qed.

(* ================================================================= *)
(** * Part 4: Type soundness *)

(** ** Not stuck, and safe *)

(** The lecture's notion (slide 9): e is NOT STUCK when it is a value
    or it steps. *)
Definition not_stuck (e : exp) : Prop := value e \/ exists e', e ⟶ e'.

(** e is SAFE when everything it can reach is not stuck. *)
Definition safe (e : exp) : Prop := forall e', e ⟶* e' -> not_stuck e'.

(** ** Soundness, assuming progress and preservation

    Type soundness: well-typed expressions are safe.

        if ⊢ e : τ, then safe e

    Unfolding safe, this is the lecture's statement (slide 9): if
    ⊢ e : τ and e ⟶* e', then e' is not stuck: it is a value or it
    steps.

    We prove it from two facts about a single step, progress and
    preservation.  Inside this Section they are assumptions
    ([Hypothesis]).  When the Section ends, Rocq turns [soundness] into
    a theorem that takes them as arguments, so the assumptions stay
    visible in its type.  The rest of Part 4 proves them. *)
Section Soundness.

  (** Progress: a closed, well-typed expression is not stuck.
      Unfolding not_stuck, this is the lecture's statement: e is a
      value or e ⟶ e' for some e'. *)
  Hypothesis progress :
    forall e τ, ⊢ e : τ -> not_stuck e.

  (** Preservation: a step keeps the type. *)
  Hypothesis preservation :
    forall e e' τ, ⊢ e : τ -> e ⟶ e' -> ⊢ e' : τ.

  (** By induction on the run e ⟶* e'.  Preservation carries the type
      along each step; progress applies at the end. *)
  Theorem soundness e τ : ⊢ e : τ -> safe e.
  Proof.
    (* Assume ⊢ e : τ (call it Ht).  "safe e" means: for every e' with
       e ⟶* e', e' is not stuck.  So also take any such e' and the run
       e ⟶* e' (call it Hrun).  Goal: e' is not stuck. *)
    intros Ht e' Hrun.
    (* Induction on the run: one case for each rule of ⟶*, (refl) and
       (step).  In both cases the goal is about the end of the run. *)
    induction Hrun as [e | e1 e2 e3 Hs Hrest IH].
    - (* Case (refl): the run takes no steps, so it ends at e itself,
         and Ht says ⊢ e : τ.  Progress says exactly that e is not
         stuck. *)
      apply (progress e τ Ht).
    - (* Case (step): the run is one step e1 ⟶ e2 (Hs), followed by the
         rest of the run e2 ⟶* e3 (Hrest).  Ht says ⊢ e1 : τ.
         The induction hypothesis IH is about the shorter run Hrest:
         if ⊢ e2 : τ, then e3 is not stuck.  So it is enough to show
         ⊢ e2 : τ. *)
      apply IH.
      (* Use preservation: a step keeps the type.  For e1 ⟶ e2 it needs
         two things, ⊢ e1 : τ and the step itself. *)
      apply preservation with (e := e1).
      + (* ⊢ e1 : τ is Ht. *)
        apply Ht.
      + (* e1 ⟶ e2 is Hs. *)
        apply Hs.
  Qed.

End Soundness.

(** Outside the Section, the assumptions are arguments: *)
Check soundness.

(** ** Canonical forms *)

(** A closed value's type tells you its shape (slide 9):
    - if ⊢ v : int, then v is a number;
    - if ⊢ v : bool, then v is true or false;
    - if ⊢ v : τ1 → τ2, then v is λx:τ1. e.
    Each proof goes through the four kinds of value: for the wrong
    kinds, no typing rule gives that type. *)
Lemma canonical_int v : value v -> ⊢ v : INT -> exists n, v = const n.
Proof.
  intros Hv Ht.
  (* the four kinds of value *)
  destruct Hv as [n | | | x τ e].
  - (* a number: this is the one *)
    exists n. reflexivity.
  - (* TRUE: only t_true types it, at BOOL, not INT *)
    inversion Ht.
  - (* FALSE: the same *)
    inversion Ht.
  - (* a λ: only t_lam types it, at a function type, not INT *)
    inversion Ht.
Qed.

Lemma canonical_bool v : value v -> ⊢ v : BOOL -> v = TRUE \/ v = FALSE.
Proof.
  intros Hv Ht.
  destruct Hv as [n | | | x τ e].
  - (* a number: only t_num types it, at INT *)
    inversion Ht.
  - left. reflexivity.
  - right. reflexivity.
  - (* a λ: only t_lam types it, at a function type *)
    inversion Ht.
Qed.

Lemma canonical_arr v τ1 τ2 :
  value v -> ⊢ v : τ1 ⇒ τ2 -> exists x e, v = λ x : τ1 , e.
Proof.
  intros Hv Ht.
  destruct Hv as [n | | | x τ e].
  - inversion Ht.
  - inversion Ht.
  - inversion Ht.
  - (* a λ: t_lam says its annotation τ is the argument type τ1 *)
    inversion Ht; subst. exists x, e. reflexivity.
Qed.

(** ** Steps inside a context (congruence) *)

(** If e ⟶ e', then E[e] ⟶ E[e'] for any evaluation context E.

    The step e ⟶ e' is E'[r] ⟶ E'[r'] for some context E' and redex r.
    Put E' inside the hole of E to get one bigger context, written
    compose E E'; then E[e] is (compose E E')[r], and the step rule
    applies with that context. *)

(** compose E E' puts E' into the hole of E. *)
Fixpoint compose (E E' : ectx) : ectx :=
  match E with
  | Hole => E'
  | AppL E e2 => AppL (compose E E') e2
  | AppR v E => AppR v (compose E E')
  | PlusL E e2 => PlusL (compose E E') e2
  | PlusR n E => PlusR n (compose E E')
  | IfC E e1 e2 => IfC (compose E E') e1 e2
  end.

(** Plugging into a composed context is plugging twice:
    (compose E E')[e] = E[E'[e]].  By induction on E; every case is the
    IH inside one layer. *)
Lemma plug_compose E E' e : (compose E E') [e] = E [E' [e]].
Proof.
  induction E as [ | E IH e2 | v E IH | E IH e2 | n E IH | E IH e1 e2 ];
    simpl.
  - (* E = •: both sides are E'[e] *)
    reflexivity.
  (* every other layer: rewrite with the IH underneath it *)
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma step_in_context E e e' : e ⟶ e' -> E [e] ⟶ E [e'].
Proof.
  intros Hs.
  (* the step e ⟶ e' was made by the one rule: e = E'[r], e' = E'[r'] *)
  destruct Hs as [E' r r' Hr].
  (* rewrite both sides as plugs into the composed context *)
  rewrite <- (plug_compose E E' r).
  rewrite <- (plug_compose E E' r').
  (* now it is the step rule, with context compose E E' *)
  apply s_ctx. apply Hr.
Qed.

(** ** Progress *)

(** If ⊢ e : τ, then e is not stuck: e is a value, or e ⟶ e' for some
    e'.

    By induction on the typing derivation.  For an application, a sum
    or an if, look at the subterm in evaluation position: if it steps,
    the whole expression steps, by steps inside a context; if it is a
    value, canonical forms says what it looks like, and the whole
    expression is a redex, with E = •. *)
Theorem progress e τ : ⊢ e : τ -> not_stuck e.
Proof.
  intros Ht.
  (* Induction on the typing derivation needs the context to be a
     variable, so name the empty context Γ and remember that Γ = nil. *)
  remember (@nil (name * ty)) as Γ.
  induction Ht as [ Γ n | Γ | Γ | Γ x τ Hx | Γ x τ1 e τ2 He IH
                  | Γ e1 e2 τ1 τ2 H1 IH1 H2 IH2 | Γ e1 e2 H1 IH1 H2 IH2
                  | Γ e e1 e2 τ H IH H1 IH1 H2 IH2 ];
    subst Γ; unfold not_stuck in *.
  - (* Case n: a value *)
    left. apply v_num.
  - (* Case true: a value *)
    left. apply v_true.
  - (* Case false: a value *)
    left. apply v_false.
  - (* Case x: impossible.  t_var needs x:τ in the context, but the
       context is empty, so the lookup Hx can't succeed. *)
    discriminate Hx.
  - (* Case λx:τ1. e: a value *)
    left. apply v_lam.
  - (* Case e1 e2.  It steps, so prove the right side. *)
    right.
    (* The IH for e1: e1 is a value, or it steps. *)
    destruct (IH1 eq_refl) as [Hv1 | Hs1].
    + (* e1 is a value.  Now the IH for e2. *)
      destruct (IH2 eq_refl) as [Hv2 | Hs2].
      * (* Both values.  Canonical forms: e1 has a function type, so it
           is some λx:τ1. e.  Then e1 e2 is a β-redex, with E = •. *)
        destruct (canonical_arr e1 τ1 τ2 Hv1 H1) as [x [e Heq]]. subst.
        exists (e [x ↦ e2]).
        apply (s_ctx Hole). apply r_beta. apply Hv2.
      * (* e2 steps to some e2'.  Then e1 e2 ⟶ e1 e2', by steps inside
           a context with the context e1 • (a right hole); the val in
           it is e1 with the proof Hv1. *)
        destruct Hs2 as [e2' Hs2].
        exists (e1 · e2').
        apply (step_in_context (AppR (exist _ e1 Hv1) Hole)). apply Hs2.
    + (* e1 steps to some e1'.  Then e1 e2 ⟶ e1' e2, by steps inside a
         context with the context • e2 (a left hole). *)
      destruct Hs1 as [e1' Hs1].
      exists (e1' · e2).
      apply (step_in_context (AppL Hole e2)). apply Hs1.
  - (* Case e1 + e2.  It steps. *)
    right.
    destruct (IH1 eq_refl) as [Hv1 | Hs1].
    + (* e1 is a value of type int: canonical forms makes it a number *)
      destruct (canonical_int e1 Hv1 H1) as [n1 Heq1]. subst.
      destruct (IH2 eq_refl) as [Hv2 | Hs2].
      * (* both numbers: n1 + n2 is a redex, with E = • *)
        destruct (canonical_int e2 Hv2 H2) as [n2 Heq2]. subst.
        exists (const (n1 + n2)).
        apply (s_ctx Hole). apply r_plus.
      * (* e2 steps: steps inside the context n1 + • *)
        destruct Hs2 as [e2' Hs2].
        exists (const n1 ⊕ e2').
        apply (step_in_context (PlusR n1 Hole)). apply Hs2.
    + (* e1 steps: steps inside the context • + e2 *)
      destruct Hs1 as [e1' Hs1].
      exists (e1' ⊕ e2).
      apply (step_in_context (PlusL Hole e2)). apply Hs1.
  - (* Case if e then e1 else e2.  It steps. *)
    right.
    destruct (IH eq_refl) as [Hv | Hs].
    + (* the condition is a value of type bool: TRUE or FALSE, and
         either way the if is a redex, with E = • *)
      destruct (canonical_bool e Hv H) as [Heq | Heq]; subst.
      * exists e1. apply (s_ctx Hole). apply r_if_true.
      * exists e2. apply (s_ctx Hole). apply r_if_false.
    + (* the condition steps: steps inside the context
         if • then e1 else e2 *)
      destruct Hs as [e' Hs].
      exists (IF e' THEN e1 ELSE e2 FI).
      apply (step_in_context (IfC Hole e1 e2)). apply Hs.
Qed.

(** ** Weakening *)

(** Γ ⊆ Γ' means every x:τ ∈ Γ is also x:τ ∈ Γ'. *)
Definition incl (Γ Γ' : ctx) : Prop :=
  forall x τ, lookup Γ x = Some τ -> lookup Γ' x = Some τ.

(** A bigger context types at least as much.  By induction on the
    typing derivation; only t_var and t_lam look at the context. *)
Lemma weakening Γ Γ' e τ : incl Γ Γ' -> Γ ⊢ e : τ -> Γ' ⊢ e : τ.
Proof.
  intros Hincl Ht.
  revert Γ' Hincl.
  induction Ht as [ Γ n | Γ | Γ | Γ x τ Hx | Γ x τ1 e τ2 He IH
                  | Γ e1 e2 τ1 τ2 H1 IH1 H2 IH2 | Γ e1 e2 H1 IH1 H2 IH2
                  | Γ e e1 e2 τ H IH H1 IH1 H2 IH2 ];
    intros Γ' Hincl.
  - apply t_num.
  - apply t_true.
  - apply t_false.
  - (* Case x: x:τ ∈ Γ ⊆ Γ' *)
    apply t_var. apply Hincl. apply Hx.
  - (* Case λx:τ1. e: the body is checked in Γ, x:τ1, so show
       Γ, x:τ1 ⊆ Γ', x:τ1 and use the IH *)
    apply t_lam. apply IH.
    intros y σ. simpl.
    destruct (String.eqb y x).
    + (* y is x: both sides find x:τ1 at the front *)
      intros Hy. apply Hy.
    + (* y is not x: both sides look further, in Γ and Γ' *)
      apply Hincl.
  - (* the remaining rules just pass the context to their premises *)
    apply t_app with (τ1 := τ1).
    + apply IH1. apply Hincl.
    + apply IH2. apply Hincl.
  - apply t_plus.
    + apply IH1. apply Hincl.
    + apply IH2. apply Hincl.
  - apply t_if.
    + apply IH. apply Hincl.
    + apply IH1. apply Hincl.
    + apply IH2. apply Hincl.
Qed.

(** ** The substitution lemma *)

(** If Γ, x:τ1 ⊢ e : τ and ⊢ v : τ1, then Γ ⊢ e[x ↦ v] : τ.  The value
    v is typed in the EMPTY context, so it is closed.

    By induction on e.  The interesting cases are the variable and the
    λ; the others push the IH into the pieces. *)
Lemma substitution Γ x τ1 v e τ :
  (x, τ1) :: Γ ⊢ e : τ -> ⊢ v : τ1 -> Γ ⊢ e [x ↦ v] : τ.
Proof.
  intros Ht Hv.
  revert Γ τ Ht.
  induction e as [ n | | | y | y τy body IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2
                 | e IH e1 IH1 e2 IH2 ];
    intros Γ τ Ht; simpl.
  - inversion Ht; subst. apply t_num.
  - inversion Ht; subst. apply t_true.
  - inversion Ht; subst. apply t_false.
  - (* Case y.  Ht says y:τ ∈ Γ, x:τ1 *)
    inversion Ht as [ | | | Γ0 y0 τ0 Hy | | | | ]; subst.
    simpl in Hy.
    destruct (String.eqb y x).
    + (* y = x: then τ = τ1, and e[x ↦ v] = v.  v is closed, so it has
         type τ in any Γ: weaken from the empty context. *)
      injection Hy as Hτ. subst.
      apply weakening with (Γ := nil).
      * intros z σ Hz. discriminate Hz.
      * apply Hv.
    + (* y ≠ x: the variable stays, and y:τ ∈ Γ *)
      apply t_var. apply Hy.
  - (* Case λy:τy. body.  Ht says  Γ, x:τ1, y:τy ⊢ body : τ2 *)
    inversion Ht as [ | | | | Γ0 y0 τ0 body0 τ2 Hbody | | | ]; subst.
    destruct (String.eqb_spec y x) as [Hyx | Hyx].
    + (* y = x: substitution stops.  The inner x hides the outer one, so
         Γ, x:τ1, x:τy types the same as Γ, x:τy *)
      subst y. apply t_lam.
      apply weakening with (Γ := (x, τy) :: (x, τ1) :: Γ).
      * intros z σ. simpl.
        destruct (String.eqb z x).
        -- intros Hz. apply Hz.
        -- intros Hz. apply Hz.
      * apply Hbody.
    + (* y ≠ x: swap the order to Γ, y:τy, x:τ1, then use the IH *)
      apply t_lam. apply IH.
      apply weakening with (Γ := (y, τy) :: (x, τ1) :: Γ).
      * intros z σ. simpl.
        destruct (String.eqb_spec z y) as [Hzy | Hzy];
          destruct (String.eqb_spec z x) as [Hzx | Hzx].
        -- (* z = y and z = x: but y ≠ x *)
           subst. contradiction.
        -- intros Hz. apply Hz.
        -- intros Hz. apply Hz.
        -- intros Hz. apply Hz.
      * apply Hbody.
  - (* the remaining forms: invert the typing, use the IH on each piece *)
    inversion Ht as [ | | | | | Γ0 e10 e20 τa τb Hfun Harg | | ]; subst.
    apply t_app with (τ1 := τa).
    + apply IH1. apply Hfun.
    + apply IH2. apply Harg.
  - inversion Ht as [ | | | | | | Γ0 e10 e20 H1 H2 | ]; subst.
    apply t_plus.
    + apply IH1. apply H1.
    + apply IH2. apply H2.
  - inversion Ht as [ | | | | | | | Γ0 e0 e10 e20 τ0 Hb H1 H2 ]; subst.
    apply t_if.
    + apply IH. apply Hb.
    + apply IH1. apply H1.
    + apply IH2. apply H2.
Qed.

(** ** Redex preservation *)

(** If ⊢ e : τ and e ⟶r e', then ⊢ e' : τ.  One case per redex rule;
    only β needs real work, and that is the substitution lemma. *)
Theorem redex_preservation e e' τ : ⊢ e : τ -> e ⟶r e' -> ⊢ e' : τ.
Proof.
  intros Ht Hr.
  destruct Hr as [x τx body v Hv | n1 n2 | e1 e2 | e1 e2].
  - (* β: (λx:τx. body) v ⟶ body[x ↦ v].
       t_app gives ⊢ λx:τx. body : τ1 ⇒ τ and ⊢ v : τ1;
       t_lam then gives τx = τ1 and x:τ1 ⊢ body : τ. *)
    inversion Ht as [ | | | | | Γ e1 e2 τ1 τ2 Hlam Harg | | ]; subst.
    inversion Hlam as [ | | | | Γ0 x0 τ0 body0 τ0' Hbody | | | ]; subst.
    (* the substitution lemma, with Γ empty *)
    apply substitution with (τ1 := τ1).
    + apply Hbody.
    + apply Harg.
  - (* n1 + n2 ⟶ n3: the sum has type int, and so does the number *)
    inversion Ht; subst. apply t_num.
  - (* if true then e1 else e2 ⟶ e1: t_if types e1 at τ *)
    inversion Ht as [ | | | | | | | Γ e0 e10 e20 τ0 Hb H1 H2 ]; subst.
    apply H1.
  - (* if false then e1 else e2 ⟶ e2: t_if types e2 at τ *)
    inversion Ht as [ | | | | | | | Γ e0 e10 e20 τ0 Hb H1 H2 ]; subst.
    apply H2.
Qed.
