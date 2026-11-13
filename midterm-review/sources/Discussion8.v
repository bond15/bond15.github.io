(** * Termination and denotations

    CSE 590, Fall 2026.  Lectures 15 and 16.

    - Part 0  The language, from Discussion 6
    - Part 1  Termination: two attempts, then a logical relation
    - Part 2  Types as sets, terms as functions
    - Part 3  Soundness and adequacy *)

From Coq Require Import ZArith String List.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* ================================================================= *)
(** * Part 0: The language *)

(** Discussion 6's simply typed λ-calculus, without the commentary.
    Syntax, values, substitution, the step relation with evaluation
    contexts, typing, and the lemmas Part 1 needs. *)

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

(** ** Lemmas from Discussion 6 *)

Lemma canonical_arr v τ1 τ2 :
  value v -> ⊢ v : τ1 ⇒ τ2 -> exists x e, v = λ x : τ1 , e.
Proof.
  intros Hv Ht.
  destruct Hv as [n | | | x τ e]; try (inversion Ht; fail).
  inversion Ht; subst. exists x, e. reflexivity.
Qed.

Fixpoint compose (E E' : ectx) : ectx :=
  match E with
  | Hole => E'
  | AppL E e2 => AppL (compose E E') e2
  | AppR v E => AppR v (compose E E')
  | PlusL E e2 => PlusL (compose E E') e2
  | PlusR n E => PlusR n (compose E E')
  | IfC E e1 e2 => IfC (compose E E') e1 e2
  end.

Lemma plug_compose E E' e : (compose E E') [e] = E [E' [e]].
Proof.
  induction E as [ | E IH e2 | v E IH | E IH e2 | n E IH | E IH e1 e2 ];
    simpl; try rewrite IH; reflexivity.
Qed.

Lemma step_in_context E e e' : e ⟶ e' -> E [e] ⟶ E [e'].
Proof.
  intros Hs. destruct Hs as [E' r r' Hr].
  rewrite <- (plug_compose E E' r), <- (plug_compose E E' r').
  apply s_ctx. apply Hr.
Qed.

(** Runs compose, and a run inside a context is a run. *)
Lemma multi_trans e1 e2 e3 : e1 ⟶* e2 -> e2 ⟶* e3 -> e1 ⟶* e3.
Proof.
  intros H12 H23. induction H12 as [ | e1 e2 e3' Hs Hrest IH].
  - apply H23.
  - apply (m_step _ _ _ Hs). apply IH. apply H23.
Qed.

Lemma multi_in_context E e e' : e ⟶* e' -> E [e] ⟶* E [e'].
Proof.
  intros Hrun. induction Hrun as [ | e1 e2 e3 Hs Hrest IH].
  - apply m_refl.
  - apply (m_step _ _ _ (step_in_context E _ _ Hs)). apply IH.
Qed.

Definition incl (Γ Γ' : ctx) : Prop :=
  forall x τ, lookup Γ x = Some τ -> lookup Γ' x = Some τ.

Lemma weakening Γ Γ' e τ : incl Γ Γ' -> Γ ⊢ e : τ -> Γ' ⊢ e : τ.
Proof.
  intros Hincl Ht. revert Γ' Hincl.
  induction Ht as [ Γ n | Γ | Γ | Γ x τ Hx | Γ x τ1 e τ2 He IH
                  | Γ e1 e2 τ1 τ2 H1 IH1 H2 IH2 | Γ e1 e2 H1 IH1 H2 IH2
                  | Γ e e1 e2 τ H IH H1 IH1 H2 IH2 ];
    intros Γ' Hincl.
  - apply t_num.
  - apply t_true.
  - apply t_false.
  - apply t_var. apply Hincl. apply Hx.
  - apply t_lam. apply IH.
    intros y σ. simpl. destruct (String.eqb y x).
    + intros Hy. apply Hy.
    + apply Hincl.
  - apply t_app with (τ1 := τ1).
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

Lemma substitution Γ x τ1 v e τ :
  (x, τ1) :: Γ ⊢ e : τ -> ⊢ v : τ1 -> Γ ⊢ e [x ↦ v] : τ.
Proof.
  intros Ht Hv. revert Γ τ Ht.
  induction e as [ n | | | y | y τy body IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2
                 | e IH e1 IH1 e2 IH2 ];
    intros Γ τ Ht; simpl.
  - inversion Ht; subst. apply t_num.
  - inversion Ht; subst. apply t_true.
  - inversion Ht; subst. apply t_false.
  - inversion Ht as [ | | | Γ0 y0 τ0 Hy | | | | ]; subst.
    simpl in Hy. destruct (String.eqb y x).
    + injection Hy as Hτ. subst.
      apply weakening with (Γ := nil).
      * intros z σ Hz. discriminate Hz.
      * apply Hv.
    + apply t_var. apply Hy.
  - inversion Ht as [ | | | | Γ0 y0 τ0 body0 τ2 Hbody | | | ]; subst.
    destruct (String.eqb_spec y x) as [Hyx | Hyx].
    + subst y. apply t_lam.
      apply weakening with (Γ := (x, τy) :: (x, τ1) :: Γ).
      * intros z σ. simpl. destruct (String.eqb z x); intros Hz; apply Hz.
      * apply Hbody.
    + apply t_lam. apply IH.
      apply weakening with (Γ := (y, τy) :: (x, τ1) :: Γ).
      * intros z σ. simpl.
        destruct (String.eqb_spec z y) as [Hzy | Hzy];
          destruct (String.eqb_spec z x) as [Hzx | Hzx];
          try (intros Hz; apply Hz).
        subst. contradiction.
      * apply Hbody.
  - inversion Ht as [ | | | | | Γ0 e10 e20 τa τb Hfun Harg | | ]; subst.
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

(* ================================================================= *)
(** * Part 1: Termination *)

(** ** The theorem *)

(** Every closed well-typed expression reduces to a value:

        if ⊢ e : τ then e ⟶* v for some value v.                     *)

Definition terminates (e : exp) : Prop := exists v, e ⟶* v /\ value v.

(** ** Attempt 1: induction on the typing derivation *)

(** Preservation along a run is Discussion 6's preservation, iterated.
    It is assumed here: the attempt fails for a different reason. *)
Section Attempt1.

  Hypothesis preservation_multi :
    forall e e' τ, ⊢ e : τ -> e ⟶* e' -> ⊢ e' : τ.

  Theorem termination_attempt_1 e τ : ⊢ e : τ -> terminates e.
  Proof.
    (* Induction on the typing derivation needs the context to be a
       variable: prove the statement for any Γ that happens to be empty. *)
    enough (H : forall Γ, Γ ⊢ e : τ -> Γ = @nil (name * ty) -> terminates e)
      by (intros Ht; apply (H nil Ht eq_refl)).
    intros Γ Ht.
    induction Ht as [ Γ n | Γ | Γ | Γ x τ Hx | Γ x τ1 e τ2 He IH
                    | Γ e1 e2 τ1 τ2 H1 IH1 H2 IH2 | Γ e1 e2 H1 IH1 H2 IH2
                    | Γ e e1 e2 τ H IH H1 IH1 H2 IH2 ];
      intros HΓ; subst Γ.
    - (* n: already a value *)
      exists (const n). split. apply m_refl. apply v_num.
    - exists TRUE. split. apply m_refl. apply v_true.
    - exists FALSE. split. apply m_refl. apply v_false.
    - (* x: no closed variable *)
      discriminate Hx.
    - (* λ: already a value *)
      exists (λ x : τ1 , e). split. apply m_refl. apply v_lam.
    - (* e1 e2: the IH gives values v1, v2 ... *)
      destruct (IH1 eq_refl) as [v1 [Hr1 Hv1]].
      destruct (IH2 eq_refl) as [v2 [Hr2 Hv2]].
      (* ... v1 is well typed, so by canonical forms it is a λ ... *)
      assert (Ht1 : ⊢ v1 : τ1 ⇒ τ2) by (apply (preservation_multi e1); assumption).
      destruct (canonical_arr v1 τ1 τ2 Hv1 Ht1) as [x [e1' Heq]]. subst v1.
      (* ... and e1 e2 ⟶* (λx:τ1. e1') v2 ⟶ e1'[x ↦ v2].  To finish we
         would need: e1'[x ↦ v2] terminates.  Nothing says so. *)
      unfold terminates.
      assert (Hrun : e1 · e2 ⟶* e1' [x ↦ v2]).
      { apply multi_trans with (e2 := (λ x : τ1 , e1') · e2).
        - apply (multi_in_context (AppL Hole e2)). apply Hr1.
        - apply multi_trans with (e2 := (λ x : τ1 , e1') · v2).
          + apply (multi_in_context (AppR (exist _ _ (v_lam x τ1 e1')) Hole)).
            apply Hr2.
          + apply (m_step _ _ _ (s_ctx Hole _ _ (r_beta x τ1 e1' v2 Hv2))).
            apply m_refl. }
      (* The goal asks for a value that e1'[x ↦ v2] reaches.  The
         hypotheses say nothing about e1'[x ↦ v2]: stuck. *)
  Abort.

End Attempt1.

(** ** The logical relation *)

(** 𝒱 τ: the good values at type τ, by recursion on τ.  Then
    ℰ τ: the good expressions, the ones that reduce to a good value.

    At function type a good value is one that sends good arguments to
    good results.  The Rocq version also records that it is a closed
    well-typed value; the lecture takes that for granted. *)
Fixpoint V (τ : ty) (v : exp) : Prop :=
  match τ with
  | INT => exists n, v = const n
  | BOOL => v = TRUE \/ v = FALSE
  | τ1 ⇒ τ2 =>
      ⊢ v : τ1 ⇒ τ2 /\ value v /\
      forall v', V τ1 v' -> exists v'', v · v' ⟶* v'' /\ V τ2 v''
  end.

Definition E (τ : ty) (e : exp) : Prop := exists v, e ⟶* v /\ V τ v.

(** A good value is a value, and is well typed. *)
Lemma V_value τ v : V τ v -> value v.
Proof.
  destruct τ as [ | | τ1 τ2 ]; simpl; intros H.
  - destruct H as [n Hn]. subst. apply v_num.
  - destruct H as [H | H]; subst. apply v_true. apply v_false.
  - destruct H as [_ [Hv _]]. apply Hv.
Qed.

Lemma V_typed τ v : V τ v -> ⊢ v : τ.
Proof.
  destruct τ as [ | | τ1 τ2 ]; simpl; intros H.
  - destruct H as [n Hn]. subst. apply t_num.
  - destruct H as [H | H]; subst. apply t_true. apply t_false.
  - destruct H as [Ht _]. apply Ht.
Qed.

(** ** Anti-reduction *)

(** If e' is good and e ⟶ e', then e is good: it reaches the same
    value, one step later.  The same for a run. *)
Lemma E_step_back τ e e' : e ⟶ e' -> E τ e' -> E τ e.
Proof.
  intros Hs [v [Hrun Hv]].
  exists v. split.
  - apply (m_step _ _ _ Hs). apply Hrun.
  - apply Hv.
Qed.

Lemma E_multi_back τ e e' : e ⟶* e' -> E τ e' -> E τ e.
Proof.
  intros Hrun [v [Hrun' Hv]].
  exists v. split.
  - apply multi_trans with (e2 := e'). apply Hrun. apply Hrun'.
  - apply Hv.
Qed.

(** ** Attempt 2: the stronger statement, for closed terms *)

Theorem termination_attempt_2 e τ : ⊢ e : τ -> E τ e.
Proof.
  intros Ht.
  remember (@nil (name * ty)) as Γ.
  induction Ht as [ Γ n | Γ | Γ | Γ x τ Hx | Γ x τ1 e τ2 He IH
                  | Γ e1 e2 τ1 τ2 H1 IH1 H2 IH2 | Γ e1 e2 H1 IH1 H2 IH2
                  | Γ e e1 e2 τ H IH H1 IH1 H2 IH2 ];
    subst Γ.
  - exists (const n). split. apply m_refl. exists n. reflexivity.
  - exists TRUE. split. apply m_refl. left. reflexivity.
  - exists FALSE. split. apply m_refl. right. reflexivity.
  - discriminate Hx.
  - (* λ: it is a value, so it reaches itself.  But now 𝒱 asks more:
       applied to any good v1, the λ must reduce to a good value.  That
       is about e[x ↦ v1], and e is not closed: no IH for it. *)
    exists (λ x : τ1 , e). split. apply m_refl.
    simpl. split. { apply t_lam. apply He. } split. { apply v_lam. }
    intros v1 Hv1.
    (* The goal: (λx:τ1. e) v1 reaches a good value.  One β step leaves
       e[x ↦ v1].  The IH is about e under the context x:τ1, where
       Γ = nil was required: it does not apply.  Stuck. *)
    clear IH.
Abort.

(** ** Closing substitutions *)

(** The fix: an inductive hypothesis for open terms.  e[γ] closes e by
    substituting a value for every variable in Γ.  Here γ is a list of
    (variable, value) pairs, applied in order. *)
Definition env := list (name * exp).

Fixpoint msubst (γ : env) (e : exp) : exp :=
  match γ with
  | nil => e
  | (x, v) :: γ' => msubst γ' (e [x ↦ v])
  end.

(** γ with its entries for x removed: what a λx hides. *)
Fixpoint drop {A : Type} (x : name) (l : list (name * A)) : list (name * A) :=
  match l with
  | nil => nil
  | (y, a) :: l' => if String.eqb y x then drop x l' else (y, a) :: drop x l'
  end.

(** 𝒢 Γ: the good closing substitutions for Γ, one good value for each
    variable, by recursion on Γ. *)
Inductive G : ctx -> env -> Prop :=
| G_nil : G nil nil
| G_cons x τ v Γ γ : V τ v -> G Γ γ -> G ((x, τ) :: Γ) ((x, v) :: γ).

(** ** Facts about substitution *)

(** x is free in e when it occurs outside every λx. *)
Fixpoint free (x : name) (e : exp) : Prop :=
  match e with
  | const _ | TRUE | FALSE => False
  | var y => y = x
  | λ y : _ , b => y <> x /\ free x b
  | e1 · e2 | e1 ⊕ e2 => free x e1 \/ free x e2
  | IF e THEN e1 ELSE e2 FI => free x e \/ free x e1 \/ free x e2
  end.

Definition closed (e : exp) : Prop := forall x, ~ free x e.

(** A free variable of a well-typed term is in its context; so a
    closed well-typed term has no free variables. *)
Lemma free_in_context x e Γ τ :
  free x e -> Γ ⊢ e : τ -> exists σ, lookup Γ x = Some σ.
Proof.
  intros Hf Ht. revert Hf.
  induction Ht as [ Γ n | Γ | Γ | Γ y τ Hy | Γ y τ1 e τ2 He IH
                  | Γ e1 e2 τ1 τ2 H1 IH1 H2 IH2 | Γ e1 e2 H1 IH1 H2 IH2
                  | Γ e e1 e2 τ H IH H1 IH1 H2 IH2 ];
    simpl; intros Hf; try contradiction.
  - subst. exists τ. apply Hy.
  - destruct Hf as [Hyx Hf].
    destruct (IH Hf) as [σ Hσ]. simpl in Hσ.
    destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + subst. contradiction.
    + exists σ. apply Hσ.
  - destruct Hf as [Hf | Hf]. apply IH1, Hf. apply IH2, Hf.
  - destruct Hf as [Hf | Hf]. apply IH1, Hf. apply IH2, Hf.
  - destruct Hf as [Hf | [Hf | Hf]]. apply IH, Hf. apply IH1, Hf. apply IH2, Hf.
Qed.

Lemma typed_closed e τ : ⊢ e : τ -> closed e.
Proof.
  intros Ht x Hf.
  destruct (free_in_context x e nil τ Hf Ht) as [σ Hσ].
  discriminate Hσ.
Qed.

(** Substituting for a variable that is not free changes nothing. *)
Lemma subst_not_free x v e : ~ free x e -> e [x ↦ v] = e.
Proof.
  induction e as [ n | | | y | y τ b IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2
                 | e IH e1 IH1 e2 IH2 ];
    simpl; intros Hnf.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (String.eqb_spec y x) as [Hyx | Hyx].
    + subst. exfalso. apply Hnf. reflexivity.
    + reflexivity.
  - destruct (String.eqb_spec y x) as [Hyx | Hyx].
    + reflexivity.
    + rewrite IH. reflexivity. intros Hf. apply Hnf. split; assumption.
  - rewrite IH1, IH2. reflexivity.
    intros Hf; apply Hnf; right; apply Hf.
    intros Hf; apply Hnf; left; apply Hf.
  - rewrite IH1, IH2. reflexivity.
    intros Hf; apply Hnf; right; apply Hf.
    intros Hf; apply Hnf; left; apply Hf.
  - rewrite IH, IH1, IH2. reflexivity.
    intros Hf; apply Hnf; right; right; apply Hf.
    intros Hf; apply Hnf; right; left; apply Hf.
    intros Hf; apply Hnf; left; apply Hf.
Qed.

Lemma subst_closed x v e : closed e -> e [x ↦ v] = e.
Proof. intros Hc. apply subst_not_free. apply Hc. Qed.

(** After e[x ↦ v] with v closed, x is no longer free. *)
Lemma subst_kills_free x v e : closed v -> ~ free x (e [x ↦ v]).
Proof.
  intros Hc.
  induction e as [ n | | | y | y τ b IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2
                 | e IH e1 IH1 e2 IH2 ];
    simpl.
  - intros H. apply H.
  - intros H. apply H.
  - intros H. apply H.
  - destruct (String.eqb_spec y x) as [Hyx | Hyx].
    + apply Hc.
    + simpl. intros H. apply Hyx. apply H.
  - destruct (String.eqb_spec y x) as [Hyx | Hyx].
    + simpl. intros [H _]. apply H. apply Hyx.
    + simpl. intros [_ H]. apply IH. apply H.
  - intros [H | H]. apply IH1, H. apply IH2, H.
  - intros [H | H]. apply IH1, H. apply IH2, H.
  - intros [H | [H | H]]. apply IH, H. apply IH1, H. apply IH2, H.
Qed.

(** Two substitutions for different variables, both closed, commute. *)
Lemma swap_subst x y v w e :
  x <> y -> closed v -> closed w ->
  (e [x ↦ v]) [y ↦ w] = (e [y ↦ w]) [x ↦ v].
Proof.
  intros Hxy Hv Hw.
  induction e as [ n | | | z | z τ b IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2
                 | e IH e1 IH1 e2 IH2 ];
    simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (String.eqb_spec z x) as [Hzx | Hzx];
      destruct (String.eqb_spec z y) as [Hzy | Hzy]; simpl.
    + subst. contradiction.
    + rewrite (subst_closed y w v Hv).
      destruct (String.eqb_spec z x) as [H | H]. reflexivity. contradiction.
    + rewrite (subst_closed x v w Hw).
      destruct (String.eqb_spec z y) as [H | H]. reflexivity. contradiction.
    + destruct (String.eqb_spec z y) as [H | H]. contradiction.
      destruct (String.eqb_spec z x) as [H' | H']. contradiction. reflexivity.
  - destruct (String.eqb_spec z x) as [Hzx | Hzx];
      destruct (String.eqb_spec z y) as [Hzy | Hzy]; simpl.
    + subst. contradiction.
    + destruct (String.eqb_spec z y) as [H | H]. contradiction.
      destruct (String.eqb_spec z x) as [H' | H']. reflexivity. contradiction.
    + destruct (String.eqb_spec z x) as [H | H]. contradiction.
      destruct (String.eqb_spec z y) as [H' | H']. reflexivity. contradiction.
    + destruct (String.eqb_spec z y) as [H | H]. contradiction.
      destruct (String.eqb_spec z x) as [H' | H']. contradiction.
      rewrite IH. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH1, IH2. reflexivity.
  - rewrite IH, IH1, IH2. reflexivity.
Qed.

(** A closed term is unchanged by a closing substitution. *)
Lemma msubst_closed γ e : closed e -> msubst γ e = e.
Proof.
  revert e. induction γ as [ | [x v] γ IH ]; intros e Hc; simpl.
  - reflexivity.
  - rewrite (subst_closed x v e Hc). apply IH. apply Hc.
Qed.

Definition closed_env (γ : env) : Prop := Forall (fun p => closed (snd p)) γ.

(** The single substitution e[x ↦ v] can be done before or after a
    closing substitution that does not mention x. *)
Lemma subst_msubst x v γ e :
  closed v -> closed_env γ ->
  (msubst (drop x γ) e) [x ↦ v] = msubst (drop x γ) (e [x ↦ v]).
Proof.
  intros Hv Hγ. revert e.
  induction γ as [ | [y w] γ IH ]; intros e; simpl.
  - reflexivity.
  - inversion Hγ as [ | p γ' Hw Hγ' ]; subst. simpl in Hw.
    destruct (String.eqb_spec y x) as [Hyx | Hyx].
    + apply IH. apply Hγ'.
    + simpl. rewrite IH by apply Hγ'.
      rewrite (swap_subst y x w v e) by assumption. reflexivity.
Qed.

(** How e[γ] goes through each form of e. *)
Lemma msubst_var γ x :
  closed_env γ ->
  msubst γ (var x) = match lookup γ x with Some v => v | None => var x end.
Proof.
  intros Hγ.
  induction γ as [ | [y v] γ IH ]; simpl.
  - reflexivity.
  - inversion Hγ as [ | p γ' Hv Hγ' ]; subst. simpl in Hv.
    destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + apply msubst_closed. apply Hv.
    + apply IH. apply Hγ'.
Qed.

Lemma msubst_num γ n : msubst γ (const n) = const n.
Proof. induction γ as [ | [y v] γ IH ]; simpl. reflexivity. apply IH. Qed.

Lemma msubst_true γ : msubst γ TRUE = TRUE.
Proof. induction γ as [ | [y v] γ IH ]; simpl. reflexivity. apply IH. Qed.

Lemma msubst_false γ : msubst γ FALSE = FALSE.
Proof. induction γ as [ | [y v] γ IH ]; simpl. reflexivity. apply IH. Qed.

Lemma msubst_lam γ x τ b :
  msubst γ (λ x : τ , b) = λ x : τ , msubst (drop x γ) b.
Proof.
  revert b. induction γ as [ | [y v] γ IH ]; intros b; simpl.
  - reflexivity.
  - destruct (String.eqb_spec x y) as [Hxy | Hxy];
      destruct (String.eqb_spec y x) as [Hyx | Hyx].
    + apply IH.
    + subst. contradiction.
    + subst. contradiction.
    + simpl. apply IH.
Qed.

Lemma msubst_app γ e1 e2 : msubst γ (e1 · e2) = msubst γ e1 · msubst γ e2.
Proof.
  revert e1 e2. induction γ as [ | [y v] γ IH ]; intros e1 e2; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma msubst_plus γ e1 e2 : msubst γ (e1 ⊕ e2) = msubst γ e1 ⊕ msubst γ e2.
Proof.
  revert e1 e2. induction γ as [ | [y v] γ IH ]; intros e1 e2; simpl.
  - reflexivity.
  - apply IH.
Qed.

Lemma msubst_if γ e e1 e2 :
  msubst γ (IF e THEN e1 ELSE e2 FI)
  = IF msubst γ e THEN msubst γ e1 ELSE msubst γ e2 FI.
Proof.
  revert e e1 e2. induction γ as [ | [y v] γ IH ]; intros e e1 e2; simpl.
  - reflexivity.
  - apply IH.
Qed.

(** ** Facts about good substitutions *)

Lemma G_closed Γ γ : G Γ γ -> closed_env γ.
Proof.
  intros HG. induction HG as [ | x τ v Γ γ Hv HG IH ].
  - apply Forall_nil.
  - apply Forall_cons.
    + apply (typed_closed v τ). apply V_typed. apply Hv.
    + apply IH.
Qed.

(** A variable of Γ is sent to a good value of its type. *)
Lemma G_lookup Γ γ x τ :
  G Γ γ -> lookup Γ x = Some τ ->
  exists v, lookup γ x = Some v /\ V τ v.
Proof.
  intros HG. induction HG as [ | y σ v Γ γ Hv HG IH ]; simpl; intros Hx.
  - discriminate Hx.
  - destruct (String.eqb_spec x y) as [Hxy | Hxy].
    + injection Hx as Hστ. subst. exists v. split. reflexivity. apply Hv.
    + apply IH. apply Hx.
Qed.

Lemma G_drop x Γ γ : G Γ γ -> G (drop x Γ) (drop x γ).
Proof.
  intros HG. induction HG as [ | y τ v Γ γ Hv HG IH ]; simpl.
  - apply G_nil.
  - destruct (String.eqb y x).
    + apply IH.
    + apply G_cons. apply Hv. apply IH.
Qed.

(** Dropping x leaves the other variables alone. *)
Lemma lookup_drop {A : Type} (l : list (name * A)) x y :
  lookup (drop x l) y = if String.eqb y x then None else lookup l y.
Proof.
  induction l as [ | [z a] l IH ]; simpl.
  - destruct (String.eqb y x); reflexivity.
  - destruct (String.eqb_spec z x) as [Hzx | Hzx].
    + subst z. rewrite IH. destruct (String.eqb_spec y x); reflexivity.
    + simpl. destruct (String.eqb_spec y z) as [Hyz | Hyz].
      * subst z. destruct (String.eqb_spec y x) as [Hyx | Hyx].
        contradiction. reflexivity.
      * apply IH.
Qed.

Lemma lookup_app {A : Type} (l1 l2 : list (name * A)) y :
  lookup (l1 ++ l2)%list y
  = match lookup l1 y with Some a => Some a | None => lookup l2 y end.
Proof.
  induction l1 as [ | [z a] l1 IH ]; simpl.
  - reflexivity.
  - destruct (String.eqb y z). reflexivity. apply IH.
Qed.

(** A closing substitution for Γ turns a term typed under Γ (plus
    whatever Δ is left over) into one typed under Δ: the substitution
    lemma, once per variable. *)
Lemma msubst_typed Γ γ :
  G Γ γ -> forall Δ e τ, (Γ ++ Δ)%list ⊢ e : τ -> Δ ⊢ msubst γ e : τ.
Proof.
  intros HG. induction HG as [ | x σ v Γ γ Hv HG IH ]; intros Δ e τ Ht; simpl.
  - apply Ht.
  - apply IH. apply substitution with (τ1 := σ).
    + apply Ht.
    + apply V_typed. apply Hv.
Qed.

(** Under a λx, the context Γ, x:τ1 can be read as drop x Γ, x:τ1:
    the inner x hides any outer one. *)
Lemma incl_drop x τ1 Γ : incl ((x, τ1) :: Γ) (drop x Γ ++ (x, τ1) :: nil)%list.
Proof.
  intros y σ. simpl. rewrite lookup_app, lookup_drop.
  destruct (String.eqb_spec y x) as [Hyx | Hyx]; simpl.
  - destruct (String.eqb_spec y x) as [H | H].
    + intros Hσ. apply Hσ.
    + contradiction.
  - intros H. rewrite H. reflexivity.
Qed.

(** ** The fundamental theorem *)

(** If Γ ⊢ e : τ, then for every good γ for Γ, e[γ] is a good
    expression of type τ.

    The lecture's proof is by induction on the typing derivation.  In
    Rocq it is by induction on e, inverting the typing rule at each
    step, so that at a λ the context can be changed to drop x Γ, x:τ1. *)
Theorem fundamental e : forall Γ τ γ, Γ ⊢ e : τ -> G Γ γ -> E τ (msubst γ e).
Proof.
  induction e as [ n | | | x | x τ1 b IH | e1 IH1 e2 IH2 | e1 IH1 e2 IH2
                 | e IH e1 IH1 e2 IH2 ];
    intros Γ τ γ Ht HG.
  - (* n *)
    inversion Ht; subst. rewrite msubst_num.
    exists (const n). split. apply m_refl. exists n. reflexivity.
  - (* true *)
    inversion Ht; subst. rewrite msubst_true.
    exists TRUE. split. apply m_refl. left. reflexivity.
  - (* false *)
    inversion Ht; subst. rewrite msubst_false.
    exists FALSE. split. apply m_refl. right. reflexivity.
  - (* x: no longer vacuous.  x[γ] is the value γ gives x, which is
       good because γ is. *)
    inversion Ht as [ | | | Γ0 x0 τ0 Hx | | | | ]; subst.
    destruct (G_lookup Γ γ x τ HG Hx) as [v [Hv HV]].
    rewrite (msubst_var γ x (G_closed Γ γ HG)). rewrite Hv.
    exists v. split. apply m_refl. apply HV.
  - (* λx:τ1. b *)
    inversion Ht as [ | | | | Γ0 x0 τ0 b0 τ2 Hb | | | ]; subst.
    rewrite msubst_lam.
    (* the body, closed by γ except for x, is typed under x:τ1 alone *)
    assert (Hb' : (x, τ1) :: nil ⊢ msubst (drop x γ) b : τ2).
    { apply (msubst_typed (drop x Γ) (drop x γ) (G_drop x Γ γ HG)).
      apply (weakening ((x, τ1) :: Γ)). apply incl_drop. apply Hb. }
    exists (λ x : τ1 , msubst (drop x γ) b). split. apply m_refl.
    simpl. split. { apply t_lam. apply Hb'. } split. { apply v_lam. }
    (* now the λ has to be good: take any good v1 *)
    intros v1 Hv1.
    assert (Hval1 : value v1) by (apply (V_value τ1), Hv1).
    assert (Hcl1 : closed v1) by (apply (typed_closed v1 τ1), V_typed, Hv1).
    (* β: (λx:τ1. b[γ-x]) v1 ⟶ b[γ-x][x ↦ v1] = b[γ-x, x ↦ v1] *)
    assert (Hstep : (λ x : τ1 , msubst (drop x γ) b) · v1
                    ⟶ msubst ((x, v1) :: drop x γ) b).
    { simpl. rewrite <- subst_msubst by (assumption || apply (G_closed Γ γ HG)).
      apply (s_ctx Hole). apply r_beta. apply Hval1. }
    (* the IH for b, with the closing substitution γ-x, x ↦ v1 *)
    assert (HE : E τ2 (msubst ((x, v1) :: drop x γ) b)).
    { apply (IH ((x, τ1) :: drop x Γ)).
      - apply (weakening ((x, τ1) :: Γ)).
        + intros y σ. simpl. destruct (String.eqb_spec y x) as [Hyx | Hyx].
          * intros H. apply H.
          * rewrite lookup_drop. destruct (String.eqb_spec y x) as [H | H].
            contradiction. intros H'. apply H'.
        + apply Hb.
      - apply G_cons. apply Hv1. apply (G_drop x Γ γ HG). }
    destruct HE as [v [Hrun Hv]].
    exists v. split.
    + apply (m_step _ _ _ Hstep). apply Hrun.
    + apply Hv.
  - (* e1 e2: both parts reach good values; a good function value sends
       the good argument to a good result; anti-reduction. *)
    inversion Ht as [ | | | | | Γ0 e10 e20 τ1 τ2 H1 H2 | | ]; subst.
    rewrite msubst_app.
    destruct (IH1 Γ (τ1 ⇒ τ) γ H1 HG) as [v1 [Hrun1 Hv1]].
    destruct (IH2 Γ τ1 γ H2 HG) as [v2 [Hrun2 Hv2]].
    destruct Hv1 as [Ht1 [Hval1 Hgood]].
    destruct (Hgood v2 Hv2) as [v [Hrun Hv]].
    exists v. split.
    + apply multi_trans with (e2 := v1 · msubst γ e2).
      { apply (multi_in_context (AppL Hole _)). apply Hrun1. }
      apply multi_trans with (e2 := v1 · v2).
      { apply (multi_in_context (AppR (exist _ v1 Hval1) Hole)). apply Hrun2. }
      apply Hrun.
    + apply Hv.
  - (* e1 + e2: both reach numbers; their sum is a number *)
    inversion Ht as [ | | | | | | Γ0 e10 e20 H1 H2 | ]; subst.
    rewrite msubst_plus.
    destruct (IH1 Γ INT γ H1 HG) as [v1 [Hrun1 [n1 Hn1]]]. subst v1.
    destruct (IH2 Γ INT γ H2 HG) as [v2 [Hrun2 [n2 Hn2]]]. subst v2.
    exists (const (n1 + n2)). split.
    + apply multi_trans with (e2 := const n1 ⊕ msubst γ e2).
      { apply (multi_in_context (PlusL Hole _)). apply Hrun1. }
      apply multi_trans with (e2 := const n1 ⊕ const n2).
      { apply (multi_in_context (PlusR n1 Hole)). apply Hrun2. }
      apply (m_step _ _ _ (s_ctx Hole _ _ (r_plus n1 n2))). apply m_refl.
    + exists (n1 + n2). reflexivity.
  - (* if: the condition reaches true or false; then the branch *)
    inversion Ht as [ | | | | | | | Γ0 e0 e10 e20 τ0 H H1 H2 ]; subst.
    rewrite msubst_if.
    destruct (IH Γ BOOL γ H HG) as [v [Hrun Hv]].
    destruct Hv as [Hv | Hv]; subst v.
    + destruct (IH1 Γ τ γ H1 HG) as [v1 [Hrun1 Hv1]].
      exists v1. split.
      * apply multi_trans with (e2 := IF TRUE THEN msubst γ e1 ELSE msubst γ e2 FI).
        { apply (multi_in_context (IfC Hole _ _)). apply Hrun. }
        apply (m_step _ _ _ (s_ctx Hole _ _ (r_if_true _ _))). apply Hrun1.
      * apply Hv1.
    + destruct (IH2 Γ τ γ H2 HG) as [v2 [Hrun2 Hv2]].
      exists v2. split.
      * apply multi_trans with (e2 := IF FALSE THEN msubst γ e1 ELSE msubst γ e2 FI).
        { apply (multi_in_context (IfC Hole _ _)). apply Hrun. }
        apply (m_step _ _ _ (s_ctx Hole _ _ (r_if_false _ _))). apply Hrun2.
      * apply Hv2.
Qed.

(** ** Termination *)

(** The closed case: Γ and γ empty, and e[] = e. *)
Theorem termination e τ : ⊢ e : τ -> terminates e.
Proof.
  intros Ht.
  destruct (fundamental e nil τ nil Ht G_nil) as [v [Hrun Hv]].
  exists v. split. apply Hrun. apply (V_value τ). apply Hv.
Qed.

Print Assumptions termination.

(* ================================================================= *)
(** * Part 2: Types as sets, terms as functions *)

(** ** Types as sets *)

(** ⟦τ⟧ is a Rocq type: int is Z, bool is bool, and a function type
    is the type of Rocq functions. *)
Fixpoint den_ty (τ : ty) : Type :=
  match τ with
  | INT => Z
  | BOOL => bool
  | τ1 ⇒ τ2 => den_ty τ1 -> den_ty τ2
  end.

Notation "⟦ τ ⟧" := (den_ty τ) (at level 0).

(** ⟦Γ⟧: a value for each variable.  ⟦·⟧ has one element, and
    ⟦Γ, x:τ⟧ = ⟦Γ⟧ × ⟦τ⟧. *)
Fixpoint den_ctx (Γ : ctx) : Type :=
  match Γ with
  | nil => unit
  | (x, τ) :: Γ' => den_ctx Γ' * ⟦ τ ⟧
  end.

Notation "⟦ Γ ⟧c" := (den_ctx Γ) (at level 0).

(** ** Terms as functions *)

(** ⟦e⟧ is defined on a typing derivation, so it needs the derivation
    as data.  [deriv] is [has_type] again, in Type instead of Prop,
    with the variable rule pointing at x's position in Γ. *)
Inductive member : name -> ty -> ctx -> Type :=
| here x τ Γ : member x τ ((x, τ) :: Γ)
| there x τ y σ Γ : y <> x -> member x τ Γ -> member x τ ((y, σ) :: Γ).

Inductive deriv : ctx -> exp -> ty -> Type :=
| d_num Γ n : deriv Γ (const n) INT
| d_true Γ : deriv Γ TRUE BOOL
| d_false Γ : deriv Γ FALSE BOOL
| d_var Γ x τ : member x τ Γ -> deriv Γ (var x) τ
| d_lam Γ x τ1 e τ2 : deriv ((x, τ1) :: Γ) e τ2 -> deriv Γ (λ x : τ1 , e) (τ1 ⇒ τ2)
| d_app Γ e1 e2 τ1 τ2 : deriv Γ e1 (τ1 ⇒ τ2) -> deriv Γ e2 τ1 -> deriv Γ (e1 · e2) τ2
| d_plus Γ e1 e2 : deriv Γ e1 INT -> deriv Γ e2 INT -> deriv Γ (e1 ⊕ e2) INT
| d_if Γ e e1 e2 τ : deriv Γ e BOOL -> deriv Γ e1 τ -> deriv Γ e2 τ ->
    deriv Γ (IF e THEN e1 ELSE e2 FI) τ.

(** γ(x): read x's value out of γ ∈ ⟦Γ⟧. *)
Fixpoint fetch {x τ Γ} (m : member x τ Γ) : ⟦ Γ ⟧c -> ⟦ τ ⟧ :=
  match m with
  | here _ _ _ => fun γ => snd γ
  | there _ _ _ _ _ _ m' => fun γ => fetch m' (fst γ)
  end.

(** ⟦e⟧ : ⟦Γ⟧ → ⟦τ⟧, one clause per rule:

        ⟦x⟧ γ          = γ(x)
        ⟦λx:τ1. e⟧ γ   = z ↦ ⟦e⟧ (γ, x ↦ z)          (currying)
        ⟦e1 e2⟧ γ      = (⟦e1⟧ γ) (⟦e2⟧ γ)
        ⟦n⟧ γ          = n
        ⟦e1 + e2⟧ γ    = ⟦e1⟧ γ + ⟦e2⟧ γ
        ⟦if e then e1 else e2⟧ γ = if ⟦e⟧ γ then ⟦e1⟧ γ else ⟦e2⟧ γ     *)
Fixpoint den {Γ e τ} (d : deriv Γ e τ) : ⟦ Γ ⟧c -> ⟦ τ ⟧ :=
  match d with
  | d_num _ n => fun γ => n
  | d_true _ => fun γ => true
  | d_false _ => fun γ => false
  | d_var _ _ _ m => fun γ => fetch m γ
  | d_lam _ _ _ _ _ d' => fun γ z => den d' (γ, z)
  | d_app _ _ _ _ _ d1 d2 => fun γ => (den d1 γ) (den d2 γ)
  | d_plus _ _ _ d1 d2 => fun γ => den d1 γ + den d2 γ
  | d_if _ _ _ _ _ d0 d1 d2 => fun γ => if den d0 γ then den d1 γ else den d2 γ
  end.

(** ** Examples *)

(** succ = λx:int. x + 1, and its derivation, in any context Γ. *)
Definition succ : exp := λ "x" : INT , var "x" ⊕ const 1.

Definition d_succ_in (Γ : ctx) : deriv Γ succ (INT ⇒ INT) :=
  d_lam _ _ _ _ _ (d_plus _ _ _ (d_var _ _ _ (here _ _ _)) (d_num _ 1)).

Definition d_succ : deriv nil succ (INT ⇒ INT) := d_succ_in nil.

(** Its meaning is a Rocq function Z → Z: apply it. *)
Check (den d_succ tt).
Compute (den d_succ tt 41).

(** twice = λf:int→int. λx:int. f (f x), and its derivation.  The
    variable f sits one position past x in the context. *)
Definition twice : exp :=
  λ "f" : INT ⇒ INT , λ "x" : INT , var "f" · (var "f" · var "x").

Definition d_twice : deriv nil twice ((INT ⇒ INT) ⇒ INT ⇒ INT) :=
  d_lam _ _ _ _ _ (d_lam _ _ _ _ _
    (d_app _ _ _ _ _
      (d_var _ _ _ (there _ _ _ _ _ (proj1 (String.eqb_neq "x" "f") eq_refl) (here _ _ _)))
      (d_app _ _ _ _ _
        (d_var _ _ _ (there _ _ _ _ _ (proj1 (String.eqb_neq "x" "f") eq_refl) (here _ _ _)))
        (d_var _ _ _ (here _ _ _))))).

(** ⟦twice⟧ is a function of a function. *)
Check (den d_twice tt).
Compute (den d_twice tt (den d_succ tt) 2).

(** The running example, twice succ 2, means 4. *)
Definition twice_succ_two : exp := twice · succ · const 2.

Definition d_twice_succ_two : deriv nil twice_succ_two INT :=
  d_app _ _ _ _ _ (d_app _ _ _ _ _ d_twice d_succ) (d_num _ 2).

Compute (den d_twice_succ_two tt).

(** An open term: x:int, y:int ⊢ if true then x else y.  Its meaning
    takes a γ with values for y and x. *)
Definition d_open : deriv (("y", INT) :: ("x", INT) :: nil)
                          (IF TRUE THEN var "x" ELSE var "y" FI) INT :=
  d_if _ _ _ _ _ (d_true _)
       (d_var _ _ _ (there _ _ _ _ _ (proj1 (String.eqb_neq "y" "x") eq_refl) (here _ _ _)))
       (d_var _ _ _ (here _ _ _)).

Compute (den d_open (tt, 10, 20)).

(* ================================================================= *)
(** * Part 3: Soundness and adequacy *)

(** ** Soundness: a step keeps the meaning *)

(** The if case: ⟦if true then e1 else e2⟧ γ = ⟦e1⟧ γ, by unfolding. *)
Lemma den_if_true Γ e1 e2 τ (d1 : deriv Γ e1 τ) (d2 : deriv Γ e2 τ) γ :
  den (d_if _ _ _ _ _ (d_true _) d1 d2) γ = den d1 γ.
Proof. reflexivity. Qed.

(** The plus case: ⟦n1 + n2⟧ γ = ⟦n1 + n2⟧ γ, the same number. *)
Lemma den_plus Γ n1 n2 γ :
  den (d_plus Γ _ _ (d_num _ n1) (d_num _ n2)) γ = den (d_num Γ (n1 + n2)) γ.
Proof. reflexivity. Qed.

(** The β case needs compositionality, ⟦e[x ↦ v]⟧ γ = ⟦e⟧ (γ, x ↦ ⟦v⟧ γ),
    stated in the page.  On the example it is a computation.  The first
    step of twice succ 2 is a β step: *)
Definition after_step : exp := (λ "x" : INT , succ · (succ · var "x")) · const 2.

Example twice_step : twice_succ_two ⟶ after_step.
Proof.
  apply (s_ctx (AppL Hole (const 2))). apply r_beta. apply v_lam.
Qed.

(** Both sides of the step mean 4. *)
Definition d_after_step : deriv nil after_step INT :=
  d_app _ _ _ _ _
    (d_lam _ _ _ _ _
      (d_app _ _ _ _ _ (d_succ_in _)
        (d_app _ _ _ _ _ (d_succ_in _) (d_var _ _ _ (here _ _ _)))))
    (d_num _ 2).

Example beta_sound : den d_twice_succ_two tt = den d_after_step tt.
Proof. reflexivity. Qed.

(** ** Adequacy: the meaning is what the program computes *)

(** At int and bool, a denotation is a value, so the statement is
    direct: a closed Boolean program reduces to its meaning. *)
Definition exp_of_bool (b : bool) : exp := if b then TRUE else FALSE.

Theorem adequacy_bool e (d : deriv nil e BOOL) : e ⟶* exp_of_bool (den d tt).
Proof.
  (* Proved with a logical relation between values and denotations,
     the binary version of Part 1's.  Its definition is below; the
     proof is the fundamental theorem again, and is not in this file. *)
Admitted.

(** The relation: v ≈ x at type τ, between a closed value and an
    element of ⟦τ⟧.  At int and bool they are the same number or
    Boolean; at function type, related arguments go to related
    results. *)
Fixpoint Vd (τ : ty) : exp -> ⟦ τ ⟧ -> Prop :=
  match τ return exp -> ⟦ τ ⟧ -> Prop with
  | INT => fun v n => v = const n
  | BOOL => fun v b => v = exp_of_bool b
  | τ1 ⇒ τ2 => fun v f =>
      value v /\
      forall v' x, Vd τ1 v' x -> exists v'', v · v' ⟶* v'' /\ Vd τ2 v'' (f x)
  end.

Definition Ed (τ : ty) (e : exp) (x : ⟦ τ ⟧) : Prop :=
  exists v, e ⟶* v /\ Vd τ v x.
