(* PAGE:ARITH-PRELUDE *)
Module Arithmetic.
(** * Arithmetic expressions

    CSE 590, Fall 2026.  The arithmetic fragment of IMP from Lectures 8
    (9/28) and 9 (9/30). *)

(** ** Getting started

    This file is written in Rocq (previously named Coq), a proof
    assistant: you state something, prove it, and Rocq checks every step.

    *** Running it in your browser (jsCoq)

    - Go to https://coq.vercel.app/scratchpad.html.  Nothing to install.
    - Paste this whole file into the editor on the left.
    - The first time, it takes a few seconds to download the libraries
      we import.
    - Rocq reads the file one sentence at a time.  Sentences end with a
      period.  To move through the file:
        Alt-↓      check the next sentence
        Alt-↑      go back one sentence
        Alt-Enter  check everything up to the cursor
    - Checked text is highlighted.  If something is wrong it turns red,
      and the error shows up on the right.
    - Inside a proof, the right panel shows the goal: what is left to
      prove.  Watching the goal change is the main way to follow a proof.
    - jsCoq draws -> as an arrow, →.  Don't mix it up with →a.

    *** Reading the file

    - [Definition] gives a name to something.

    - [Inductive] defines a relation by its rules.  Each line starting
      with | is one inference rule: premises above the bar, conclusion
      below it, as on the slides.  The bar is just a comment.

    - [Example] states a fact, and the proof goes between [Proof.] and
      [Qed.].  The proof is a list of tactics: commands that build the
      proof one step at a time.

    *** The tactics we use

    - [apply R]: "use rule R".  If R's conclusion matches the goal, the
      goal is replaced by R's premises.  This is building a derivation
      tree from the bottom up, like on the board.

    - [apply R with (n0 := 5)]: the same, but we tell Rocq a value it
      can't guess on its own, e.g. what a subexpression evaluates to.

    - [reflexivity]: proves an equation whose two sides compute to the
      same thing, like 5 = 3 + 2.

    - [unfold e]: replaces the name e with what it stands for.

    - [-], [+], [*], and [{ }]: when a rule leaves several premises to
      prove, each bullet (or pair of braces) handles one of them.

    - [intros H]: the goal says "if P then Q".  This assumes P, names it H,
      and leaves Q to prove.

    - [induction H as [...]]: rule induction on H.  You get one case per
      rule that could have built H, and in each case an induction
      hypothesis (IH) for every premise that is the same kind of
      judgment.  The [as [...]] part just names things; each | starts
      the names for the next rule.

    - [inversion H]: "how could H have been built?"  Rocq looks at every
      rule whose conclusion could match H, keeps only the ones that
      fit, and gives you their premises as new hypotheses.

    - [subst]: after [inversion] there are often equations like n = n3;
      this replaces one side with the other everywhere, so they go away.

    - [rewrite E]: E is an equation x = y; this replaces x by y in the
      goal.  [rewrite E in H] does it in hypothesis H instead.

    - [split]: the goal is "A if and only if B"; this splits it into two
      goals, one for each direction. *)

From Coq Require Import ZArith String.
Open Scope Z_scope.
Open Scope string_scope.




























(* ================================================================= *)
(* PAGE:ARITH-SYNTAX *)
(** ** Syntax *)

Definition name := string.

(** AExp : a ::= n | x | a0 + a1 | a0 ∗ a1 *)
Inductive aexp : Type :=
| ANum (n : Z)
| AId (x : name)
| APlus (a0 a1 : aexp)
| AMult (a0 a1 : aexp).






















(** Concrete syntax.  [const n] is the number n and [var x] is the
    variable x, as expressions.  ⊕ and ⊗ are + and ∗ in the language,
    so they can't be confused with + and * on integers. *)
Notation "'const' n" := (ANum n) (at level 1, n at level 0).
Notation "'var' x" := (AId x) (at level 1, x at level 0).
Notation "a0 ⊕ a1" := (APlus a0 a1) (at level 50, no associativity).
Notation "a0 ⊗ a1" := (AMult a0 a1) (at level 50, no associativity).
Reserved Notation "⟨ a , σ ⟩ '⇓a' n"
  (at level 70, a at level 99, σ at level 99, n at level 69).
Reserved Notation "⟨ a , σ ⟩ '→a' a'"
  (at level 70, a at level 99, σ at level 99, a' at level 69).
Reserved Notation "⟨ a , σ ⟩ '→*a' a'"
  (at level 70, a at level 99, σ at level 99, a' at level 69).






































(* ================================================================= *)
(** ** States *)

(** σ : Var → Z, total. *)
Definition state := name -> Z.

(* ================================================================= *)
(* PAGE:ARITH-BIG *)
(** ** Big-step semantics *)

(** ⇓a ⊆ (AExp × State) × Z, written ⟨a, σ⟩ ⇓a n. *)
Inductive aeval (σ : state) : aexp -> Z -> Prop :=
| AE_Num (n : Z) :

    (*──────────────────*)
         ⟨const n, σ⟩ ⇓a n

| AE_Id (x : name) :

    (*──────────────────*)
        ⟨var x, σ⟩ ⇓a σ x

| AE_Plus a0 a1 n0 n1 n2 :

        ⟨a0, σ⟩ ⇓a n0 ->
        ⟨a1, σ⟩ ⇓a n1 ->
        n2 = (n0 + n1) ->
    (*──────────────────────*)
      ⟨a0 ⊕ a1, σ⟩ ⇓a n2

| AE_Mult a0 a1 n0 n1 n2 :

        ⟨a0, σ⟩ ⇓a n0 ->
        ⟨a1, σ⟩ ⇓a n1 ->
        n2 = (n0 * n1) ->
    (*──────────────────────*)
      ⟨a0 ⊗ a1, σ⟩ ⇓a n2

where "⟨ a , σ ⟩ '⇓a' n" := (aeval σ a n).
















(* ================================================================= *)
(* PAGE:ARITH-BIG-EXAMPLE *)
(** ** Example: big-step *)

Definition X : name := "X".
Definition Y : name := "Y".

(** X = 3, Y = 2 *)
Definition σ0 : state :=
  fun x => if String.eqb x X then 3 else if String.eqb x Y then 2 else 0.

Definition e : aexp := ((var X ⊕ var Y) ⊗ (var X ⊕ var Y)) ⊕ (var X ⊗ var Y).

(** One rule per subexpression, no intermediate expressions. *)
Example e_big : ⟨e, σ0⟩ ⇓a 31.
Proof.
  unfold e.
  apply AE_Plus with (n0 := 25) (n1 := 6).
  - apply AE_Mult with (n0 := 5) (n1 := 5).
    + apply AE_Plus with (n0 := 3) (n1 := 2).
      * apply AE_Id.
      * apply AE_Id.
      * reflexivity.
    + apply AE_Plus with (n0 := 3) (n1 := 2).
      * apply AE_Id.
      * apply AE_Id.
      * reflexivity.
    + reflexivity.
  - apply AE_Mult with (n0 := 3) (n1 := 2).
    + apply AE_Id.
    + apply AE_Id.
    + reflexivity.
  - reflexivity.
Qed.














(* ================================================================= *)
(* PAGE:ARITH-SMALL *)
(** ** Small-step semantics *)

(** →a ⊆ (AExp × State) × AExp, written ⟨a, σ⟩ →a a'.  Variables and
    constants; then left operand first, then right. *)

Inductive astep (σ : state) : aexp -> aexp -> Prop :=
| AS_Id (x : name) :

    (*──────────────────────*)
         ⟨var x, σ⟩ →a const (σ x)

| AS_Plus_result (n1 n2 n3 : Z) :

         n3 = (n1 + n2) ->
    (*──────────────────────*)
        ⟨const n1 ⊕ const n2, σ⟩ →a const n3

| AS_Plus_left a1 a1' a2 :

            ⟨a1, σ⟩ →a a1' ->
    (*──────────────────────────────*)
        ⟨a1 ⊕ a2, σ⟩ →a a1' ⊕ a2

| AS_Plus_right (n1 : Z) a2 a2' :

            ⟨a2, σ⟩ →a a2' ->
    (*──────────────────────────────*)
        ⟨const n1 ⊕ a2, σ⟩ →a const n1 ⊕ a2'

| AS_Mult_result (n1 n2 n3 : Z) :

         n3 = (n1 * n2) ->
    (*──────────────────────*)
        ⟨const n1 ⊗ const n2, σ⟩ →a const n3

| AS_Mult_left a1 a1' a2 :

            ⟨a1, σ⟩ →a a1' ->
    (*──────────────────────────────*)
        ⟨a1 ⊗ a2, σ⟩ →a a1' ⊗ a2

| AS_Mult_right (n1 : Z) a2 a2' :

            ⟨a2, σ⟩ →a a2' ->
    (*──────────────────────────────*)
        ⟨const n1 ⊗ a2, σ⟩ →a const n1 ⊗ a2'

where "⟨ a , σ ⟩ '→a' a'" := (astep σ a a').

















(* ================================================================= *)
(** ** Multi-step *)

(** →*a; the state is carried along. *)
Inductive amulti (σ : state) : aexp -> aexp -> Prop :=
| AM_Refl a :

    (*──────────────────*)
        ⟨a, σ⟩ →*a a

| AM_Step a a' a'' :

        ⟨a, σ⟩ →a a' ->
        ⟨a', σ⟩ →*a a'' ->
    (*──────────────────*)
        ⟨a, σ⟩ →*a a''

where "⟨ a , σ ⟩ '→*a' a'" := (amulti σ a a').















(* ================================================================= *)
(* PAGE:ARITH-SMALL-EXAMPLE *)
(** ** Example: the same expression, small-step *)

(** By hand: every step names the next expression and applies the rules
    all the way down to the redex.  Compare with [e_big]. *)
Example e_small_by_hand : ⟨e, σ0⟩ →*a const 31.
Proof.
  unfold e.
  (* 1. X ↦ 3 *)
  apply AM_Step with (a' := ((const 3 ⊕ var Y) ⊗ (var X ⊕ var Y)) ⊕ (var X ⊗ var Y)).
  { apply AS_Plus_left. apply AS_Mult_left. apply AS_Plus_left. apply AS_Id. }
  (* 2. Y ↦ 2 *)
  apply AM_Step with (a' := ((const 3 ⊕ const 2) ⊗ (var X ⊕ var Y)) ⊕ (var X ⊗ var Y)).
  { apply AS_Plus_left. apply AS_Mult_left. apply AS_Plus_right. apply AS_Id. }
  (* 3. 3 + 2 ↦ 5 *)
  apply AM_Step with (a' := (const 5 ⊗ (var X ⊕ var Y)) ⊕ (var X ⊗ var Y)).
  { apply AS_Plus_left. apply AS_Mult_left. apply AS_Plus_result. reflexivity. }
  (* 4. X ↦ 3 *)
  apply AM_Step with (a' := (const 5 ⊗ (const 3 ⊕ var Y)) ⊕ (var X ⊗ var Y)).
  { apply AS_Plus_left. apply AS_Mult_right. apply AS_Plus_left. apply AS_Id. }
  (* 5. Y ↦ 2 *)
  apply AM_Step with (a' := (const 5 ⊗ (const 3 ⊕ const 2)) ⊕ (var X ⊗ var Y)).
  { apply AS_Plus_left. apply AS_Mult_right. apply AS_Plus_right. apply AS_Id. }
  (* 6. 3 + 2 ↦ 5 *)
  apply AM_Step with (a' := (const 5 ⊗ const 5) ⊕ (var X ⊗ var Y)).
  { apply AS_Plus_left. apply AS_Mult_right. apply AS_Plus_result. reflexivity. }
  (* 7. 5 ∗ 5 ↦ 25 *)
  apply AM_Step with (a' := const 25 ⊕ (var X ⊗ var Y)).
  { apply AS_Plus_left. apply AS_Mult_result. reflexivity. }
  (* 8. X ↦ 3 *)
  apply AM_Step with (a' := const 25 ⊕ (const 3 ⊗ var Y)).
  { apply AS_Plus_right. apply AS_Mult_left. apply AS_Id. }
  (* 9. Y ↦ 2 *)
  apply AM_Step with (a' := const 25 ⊕ (const 3 ⊗ const 2)).
  { apply AS_Plus_right. apply AS_Mult_right. apply AS_Id. }
  (* 10. 3 ∗ 2 ↦ 6 *)
  apply AM_Step with (a' := (const 25 ⊕ const 6)).
  { apply AS_Plus_right. apply AS_Mult_result. reflexivity. }
  (* 11. 25 + 6 ↦ 31 *)
  apply AM_Step with (a' := const 31).
  { apply AS_Plus_result. reflexivity. }
  apply AM_Refl.
Qed.

















(** [step]: "do the next step for me."
    1. It finds the rules: it tries the small-step rules one by one,
       going down into the expression until something fits.  For the
       first step that's [AS_Plus_left], [AS_Mult_left], [AS_Plus_left],
       [AS_Id], the same chain we typed in [e_small_by_hand].  If a
       choice leads nowhere, it backs up and tries another rule.
    2. Then the goal moves on to the rest of the run, starting from the
       new expression.
    3. Finally it tidies up, looking up variables in the state, so
       const (σ0 X) shows as const 3. *)
Global Hint Constructors astep : core.
Ltac step := eapply AM_Step; [solve [eauto] | cbn].

(** Eleven steps to 31; step through and watch the goal. *)
Example e_small : ⟨e, σ0⟩ →*a const 31.
Proof.
  unfold e.
  step. step. step. step. step. step. step. step. step. step. step.
  apply AM_Refl.
Qed.



























(** [run]: "just finish it."  Hit [step] until there's nothing left
    but a number. *)
Ltac run := repeat step; apply AM_Refl.

Example e_small_auto : ⟨e, σ0⟩ →*a const 31.
Proof. unfold e. run. Qed.
































(* ================================================================= *)
(* PAGE:ARITH-AGREEMENT *)
(** ** Small-step and big-step agree

    Theorem: ⟨a, σ⟩ →*a n  if and only if  ⟨a, σ⟩ ⇓a n.

    Roadmap
    1. Facts about →*a: a single step is a run; transitivity.
    2. Congruence: runs lift through a0 + a1 and n0 + a1, for every rule.
    3. Big ⇒ small, by rule induction on ⇓a.
    4. Anti-reduction: a step followed by a big-step evaluation.
    5. Small ⇒ big, by rule induction on →*a.
    6. The iff.

    On the homework (HW3 Exercise 1: the same proof for a short-circuit
    ∨ on Boolean expressions):
    1. You can assume these.  Transitivity is allowed by the handout,
       and "one step is a run" follows from the two →*b rules.
    2. You can assume these, but state the ones you use.
    3. You must do this, for the ∨ cases (Exercise 1(c)).
    4. You must do this, for the ∨ cases (Exercise 1(d)), saying where
       you use inversion and where you use the IH.
    5. and 6. Not asked. *)
































Section Agreement.
  Variable σ : state.

  (* ----------------------------------------------------------------- *)
  (** *** 1. Facts about →*a *)

  (** A single step is a run: (step) then (refl). *)
  (* HW: you can assume this for boolean expressions in the HW. *)
  Lemma amulti_one a a' :

        ⟨a, σ⟩ →a a' ->
    (*─────────────────*)
        ⟨a, σ⟩ →*a a'.
  Proof.
    intros H.
    apply AM_Step with (a' := a').
    - apply H.
    - apply AM_Refl.
  Qed.

  (** Transitivity, by rule induction on the first run. *)
  (* HW: you can assume this for boolean expressions in the HW. *)
  Lemma amulti_trans a a' a'' :

        ⟨a, σ⟩ →*a a' ->
        ⟨a', σ⟩ →*a a'' ->
    (*───────────────────*)
        ⟨a, σ⟩ →*a a''.
  Proof.
    intros H1 H2.
    induction H1 as [a | a a1 a' Hstep Hrest IH].
    - (* Case (refl): a = a' *)
      apply H2.
    - (* Case (step): a →a a1 →*a a'.  IH: a1 →*a a'' *)
      apply AM_Step with (a' := a1).
      + apply Hstep.
      + apply IH. apply H2.
  Qed.





























  (* ----------------------------------------------------------------- *)
  (** *** 2. Congruence, for every rule

      The rule AS_Plus_left moves ONE step inside a ⊕:
        if a1 takes a step, then a1 ⊕ a2 takes the same step,
        with a2 just along for the ride.

      The lemma cong_plus_left does the same for a WHOLE RUN:
        if a1 runs to a1', then a1 ⊕ a2 runs to a1' ⊕ a2.

      Example, with X = 3 and Y = 2:

          a1 on its own               inside _ ⊕ const 7
          var X ⊕ var Y               (var X ⊕ var Y) ⊕ const 7
          const 3 ⊕ var Y             (const 3 ⊕ var Y) ⊕ const 7
          const 3 ⊕ const 2           (const 3 ⊕ const 2) ⊕ const 7
          const 5                     const 5 ⊕ const 7

      Each line on the right comes from the line on the left by
      AS_Plus_left.  The lemma says we can always build the right
      column from the left one.

      Why we need it: in Big ⇒ small, the IH gives a run for a0 on its
      own, but we need a run for a0 ⊕ a1.  This lemma bridges the gap.

      Each congruence lemma is rule induction on the run of the
      subterm.  The first is written out; the rest are the same proof
      with a different rule, so a tactic [lift] repeats it. *)

  (* HW: you can assume this for boolean expressions in the HW. *)
  Lemma cong_plus_left a1 a1' a2 :

        ⟨a1, σ⟩ →*a a1' ->
    (*─────────────────────────────*)
        ⟨a1 ⊕ a2, σ⟩ →*a a1' ⊕ a2.
  Proof.
    intros H.
    induction H as [a1 | a1 a1'' a1' Hstep Hrest IH].
    - (* Case (refl): the run of a1 is empty, so a1 is already a1'.
         So a1 ⊕ a2 is already a1' ⊕ a2.  Empty run. *)
      apply AM_Refl.
    - (* Case (step): the run of a1 is a first step a1 → a1'' and then
         the rest.
           First step:  ⟨a1 ⊕ a2, σ⟩ →a a1'' ⊕ a2       by AS_Plus_left
           The rest:    ⟨a1'' ⊕ a2, σ⟩ →*a a1' ⊕ a2     by the IH
                        (the IH is this same lemma, for the shorter run) *)
      apply AM_Step with (a' := APlus a1'' a2).
      + apply AS_Plus_left. apply Hstep.
      + apply IH.
  Qed.

  (** The other congruence lemmas are the same proof with a different
      rule: AS_Plus_right lets a step happen on the right of a ⊕, once
      the left side is a number. *)
  Ltac lift rule :=
    intros H;
    induction H as [? | ? ? ? Hstep Hrest IH];
    [ apply AM_Refl
    | eapply AM_Step; [ apply rule; apply Hstep | apply IH ] ].

  (* HW: you can assume this for boolean expressions in the HW. *)
  Lemma cong_plus_right (n1 : Z) a2 a2' :

        ⟨a2, σ⟩ →*a a2' ->
    (*─────────────────────────────*)
        ⟨const n1 ⊕ a2, σ⟩ →*a const n1 ⊕ a2'.
  Proof. lift AS_Plus_right. Qed.

  (* HW: you can assume this for boolean expressions in the HW. *)
  Lemma cong_mult_left a1 a1' a2 :

        ⟨a1, σ⟩ →*a a1' ->
    (*─────────────────────────────*)
        ⟨a1 ⊗ a2, σ⟩ →*a a1' ⊗ a2.
  Proof. lift AS_Mult_left. Qed.

  (* HW: you can assume this for boolean expressions in the HW. *)
  Lemma cong_mult_right (n1 : Z) a2 a2' :

        ⟨a2, σ⟩ →*a a2' ->
    (*─────────────────────────────*)
        ⟨const n1 ⊗ a2, σ⟩ →*a const n1 ⊗ a2'.
  Proof. lift AS_Mult_right. Qed.































  (* ----------------------------------------------------------------- *)
  (** *** 3. Big ⇒ small, by rule induction on ⟨a, σ⟩ ⇓a n

      If the big-step tree says a evaluates to n, then there is a
      small-step run from a to n.

      Idea: the big-step tree is a recipe, and we follow it one step at
      a time.  To evaluate a0 ⊕ a1, the tree says: evaluate a0 to n0,
      evaluate a1 to n1, then add.  The small-step run does the same,
      in order:

          a0 ⊕ a1  →*  const n0 ⊕ a1          simplify the left side
                   →*  const n0 ⊕ const n1    then the right side
                   →   const n2               then add

      Example, with X = 3 and Y = 2, for (var X ⊕ var Y) ⊕ var X:

          (var X ⊕ var Y) ⊕ var X  →*  const 5 ⊕ var X     left side
                                   →*  const 5 ⊕ const 3   right side
                                   →   const 8             add

      Proof: rule induction on the big-step tree, one case per big-step
      rule.  The IH gives us a run for each subexpression ON ITS OWN;
      congruence puts those runs inside the ⊕, and transitivity glues
      the three pieces into one run. *)

  (* HW: you will have to demonstrate this for boolean expressions in the HW
     (the ∨ cases). *)




































  Lemma aeval_amulti a (n : Z) :

        ⟨a, σ⟩ ⇓a n ->
    (*────────────────*)
        ⟨a, σ⟩ →*a const n.
  Proof.
    intros H.
    induction H as [ n | x
                   | a0 a1 n0 n1 n2 H0 IH0 H1 IH1 E
                   | a0 a1 n0 n1 n2 H0 IH0 H1 IH1 E ].
    - (* Case ⟨n, σ⟩ ⇓a n.  WTS ⟨n, σ⟩ →*a n: by (refl) *)
      apply AM_Refl.
    - (* Case ⟨x, σ⟩ ⇓a σ(x).  WTS ⟨x, σ⟩ →*a σ(x): one step *)
      apply amulti_one. apply AS_Id.
    - (* we know n2 = n0 + n1 *)
      rewrite E.
      (* from ⟨ a0 + a1, σ ⟩,
         we know we can reduce to n0 + a1
         since IH0 : ⟨ a0, σ ⟩ →*a n0

         so we use transitivity to show this first part
      *)
      apply amulti_trans with (a' := const n0 ⊕ a1).
      { (* to show ⟨ a0 + a1, σ ⟩ →*a n0 + a1,
           we run a0 inside the +, leaving a1 alone.
           cong_plus_left turns a run of a0 into a run of a0 + a1 *)
        apply cong_plus_left.
        (* and the run of a0 is exactly IH0 *)
        apply IH0. }
      (* now we are at ⟨ n0 + a1, σ ⟩,
         and we know we can reduce to n0 + n1
         since IH1 : ⟨ a1, σ ⟩ →*a n1

         so we use transitivity again for this second part
      *)
      apply amulti_trans with (a' := const n0 ⊕ const n1).
      { (* to show ⟨ n0 + a1, σ ⟩ →*a n0 + n1,
           we run a1 inside the +.  The left side is already a number,
           so cong_plus_right lets us work on the right side *)
        apply cong_plus_right.
        (* and the run of a1 is exactly IH1 *)
        apply IH1. }
      (* now we are at ⟨ n0 + n1, σ ⟩, and want to reach n0 + n1 as a
         number.  That is one step, so we turn a single step into a run *)
      apply amulti_one.
      (* the step adds two numbers *)
      apply AS_Plus_result.
      (* the rule asks that the result is the sum, which it is *)
      reflexivity.
    - (* Case a0 ∗ a1: the same as +, with the ∗ rules *)
      rewrite E.
      apply amulti_trans with (a' := const n0 ⊗ a1).
      { apply cong_mult_left. apply IH0. }
      apply amulti_trans with (a' := const n0 ⊗ const n1).
      { apply cong_mult_right. apply IH1. }
      apply amulti_one. apply AS_Mult_result. reflexivity.
  Qed.




























  (* ----------------------------------------------------------------- *)
  (** *** 4. Anti-reduction

      If ⟨a, σ⟩ →a a' and ⟨a', σ⟩ ⇓a n, then ⟨a, σ⟩ ⇓a n.
      Rule induction on ⟨a, σ⟩ →a a'; in each case, invert the
      derivation of ⟨a', σ⟩ ⇓a n. *)

  (* HW: you will have to demonstrate this for boolean expressions in the HW
     (the ∨ cases). *)
  Lemma astep_antired a a' :

        ⟨a, σ⟩ →a a' ->
        forall n,
        ⟨a', σ⟩ ⇓a n ->
    (*────────────────*)
        ⟨a, σ⟩ ⇓a n.
  Proof.
    intros H.
    induction H as [ x
                   | n1 n2 n3 E | a1 a1' a2 Hstep IH | n1 a2 a2' Hstep IH
                   | n1 n2 n3 E | a1 a1' a2 Hstep IH | n1 a2 a2' Hstep IH ];
      intros n Hn.
    - (* Case ⟨var x, σ⟩ →a const (σ x).
         WTS ⟨var x, σ⟩ ⇓a n.

         Our hypothesis is  Hn : ⟨const (σ x), σ⟩ ⇓a n.
         What does this tell us?

         INVERSION.  Hn is a big-step tree, so its bottom line is the
         conclusion of one of the big-step rules.  Here are the
         conclusions of all four:

             AE_Num    ⟨const m, σ⟩ ⇓a m
             AE_Id     ⟨var y, σ⟩ ⇓a σ y
             AE_Plus   ⟨a0 ⊕ a1, σ⟩ ⇓a n2
             AE_Mult   ⟨a0 ⊗ a1, σ⟩ ⇓a n2

         Hn's expression is const (σ x), a number.  It is not a var, a
         ⊕ or a ⊗, so only AE_Num matches.  So Hn must be this rule:

             ─────────────────────────────── AE_Num   (with m = σ x)
               ⟨const (σ x), σ⟩ ⇓a σ x

         Lining that up with Hn,  ⟨const (σ x), σ⟩ ⇓a n,  tells us
         n = σ x.  Then the goal is exactly the lookup rule AE_Id. *)
      inversion Hn; subst. apply AE_Id.
    - (* Case ⟨const n1 ⊕ const n2, σ⟩ →a const n3, where n3 = n1 + n2.
         WTS ⟨const n1 ⊕ const n2, σ⟩ ⇓a n.

         Our hypothesis is  Hn : ⟨const n3, σ⟩ ⇓a n.

         INVERSION, as in the case above: const n3 is a number, so the
         only rule that can end Hn is

             ─────────────────────── AE_Num   (with m = n3)
               ⟨const n3, σ⟩ ⇓a n3

         and so n = n3.  Now build a ⊕ tree: both operands are numbers
         (AE_Num twice), and n3 = n1 + n2 is the hypothesis E. *)
      inversion Hn; subst.
      apply AE_Plus with (n0 := n1) (n1 := n2).
      + apply AE_Num.
      + apply AE_Num.
      + reflexivity.
    - (* Case ⟨a1 ⊕ a2, σ⟩ →a a1' ⊕ a2, from Hstep : ⟨a1, σ⟩ →a a1'.
         WTS ⟨a1 ⊕ a2, σ⟩ ⇓a n.

         Our hypothesis is  Hn : ⟨a1' ⊕ a2, σ⟩ ⇓a n.

         INVERSION.  Hn's expression is a ⊕.  Of the four conclusions
         listed in the first case, only AE_Plus ends in a ⊕.  So the
         bottom of Hn must be this rule:

               ⟨a1', σ⟩ ⇓a m1     ⟨a2, σ⟩ ⇓a m2     n = m1 + m2
             ───────────────────────────────────────────────── AE_Plus
                            ⟨a1' ⊕ a2, σ⟩ ⇓a n

         A rule only applies if its premises hold, so Hn tells us all
         three premises, for some values m1 and m2.  [inversion] adds
         them to our hypotheses:

             H1 : ⟨a1', σ⟩ ⇓a m1
             H2 : ⟨a2, σ⟩ ⇓a m2
             E  : n = m1 + m2

         Now rebuild a ⊕ tree, but for a1 instead of a1'.  The only
         missing piece is ⟨a1, σ⟩ ⇓a m1, and the IH gives it from H1. *)
      inversion Hn as [| | a1'' a2' m1 m2 n' H1 H2 E |]; subst.
      apply AE_Plus with (n0 := m1) (n1 := m2).
      + apply IH. apply H1.
      + apply H2.
      + reflexivity.
    - (* Case ⟨const n1 ⊕ a2, σ⟩ →a const n1 ⊕ a2'.
         Same as the case above, with the IH used on the right operand:
         inverting Hn with AE_Plus gives ⟨const n1, σ⟩ ⇓a m1,
         ⟨a2', σ⟩ ⇓a m2 and n = m1 + m2, and the IH turns the second
         into ⟨a2, σ⟩ ⇓a m2. *)
      inversion Hn as [| | a1' a2'' m1 m2 n' H1 H2 E |]; subst.
      apply AE_Plus with (n0 := m1) (n1 := m2).
      + apply H1.
      + apply IH. apply H2.
      + reflexivity.
    - (* ∗: the same three cases *)
      inversion Hn; subst.
      apply AE_Mult with (n0 := n1) (n1 := n2).
      + apply AE_Num.
      + apply AE_Num.
      + reflexivity.
    - inversion Hn as [| | | a1'' a2' m1 m2 n' H1 H2 E]; subst.
      apply AE_Mult with (n0 := m1) (n1 := m2).
      + apply IH. apply H1.
      + apply H2.
      + reflexivity.
    - inversion Hn as [| | | a1' a2'' m1 m2 n' H1 H2 E]; subst.
      apply AE_Mult with (n0 := m1) (n1 := m2).
      + apply H1.
      + apply IH. apply H2.
      + reflexivity.
  Qed.




























  (* ----------------------------------------------------------------- *)
  (** *** 5. Small ⇒ big, by rule induction on ⟨a, σ⟩ →*a n

      The (step) rule lets a run end anywhere, so Rocq needs the end
      point as a separate name a'' with the equation a'' = n. *)

  (* HW: not asked for in the HW. *)
  Lemma amulti_aeval a a'' :

        ⟨a, σ⟩ →*a a'' ->
        forall n,
        a'' = const n ->
    (*──────────────────*)
        ⟨a, σ⟩ ⇓a n.
  Proof.
    intros H.
    induction H as [a | a a' a'' Hstep Hrest IH]; intros n E.
    - (* Case (refl): a = n.  WTS ⟨n, σ⟩ ⇓a n *)
      subst. apply AE_Num.
    - (* Case (step): ⟨a, σ⟩ →a a' →*a n.
         Assume the step and IH : ⟨a', σ⟩ ⇓a n.
         WTS ⟨a, σ⟩ ⇓a n: anti-reduction. *)
      apply astep_antired with (a' := a').
      + apply Hstep.
      + apply IH. apply E.
  Qed.




























  (* ----------------------------------------------------------------- *)
  (** *** 6. The theorem *)

  (* HW: not asked for in the HW. *)
  Theorem aexp_agree a (n : Z) :

        ⟨a, σ⟩ →*a const n
    (*════════════════*) <->
        ⟨a, σ⟩ ⇓a n.
  Proof.
    split.
    - intros H. apply amulti_aeval with (a'' := const n).
      + apply H.
      + reflexivity.
    - apply aeval_amulti.
  Qed.
End Agreement.

Print Assumptions aexp_agree.

End Arithmetic.

(* PAGE:INVERSION-PRELUDE *)
Module InversionDemo.
(** * Inversion

    An inductive definition is a list of rules, and those rules are the
    ONLY ways to build evidence for a fact.  There are two ways to use
    them:

    - Forwards, with [apply]: to PROVE a fact, pick a rule whose
      conclusion matches it and prove the rule's premises.  This builds
      a derivation tree from the bottom up.

    - Backwards, with [inversion]: we are GIVEN evidence H for a fact,
      and ask "how could H have been built?"  Rocq checks every rule
      whose conclusion could match, keeps only the ones that fit, and in
      each case gives us that rule's premises.  If no rule fits, H
      cannot exist. *)

(* ================================================================= *)
(* PAGE:INVERSION-ONE *)
(** ** One rule: IsTen *)

(** There is only one rule, and it is about 10. *)
Inductive IsTen : nat -> Prop :=
| ten : IsTen 10.

(** Claim: if IsTen n, then n = 10.

    Suppose we are given H : IsTen n.  How could H have been built?
    The only rule is [ten], whose conclusion is IsTen 10.  So for H to
    exist, n must be 10.

    Notice that we learn this from the EVIDENCE H, rather than by
    looking at n alone (is it 0? is it 1? ...). *)
Theorem IsTen_inv : forall n, IsTen n -> n = 10.
Proof.
  intros n H.
  (* Only [ten] can have built H, so Rocq replaces n by 10. *)
  inversion H.
  (* The goal is now 10 = 10. *)
  reflexivity.
Qed.

(* ================================================================= *)
(* PAGE:INVERSION-EVEN *)
(** ** Two rules: even numbers

    In words: 0 is even, and if n is even, then n + 2 is even.

    S n means n + 1, so S (S n) means n + 2.  We write the second rule
    with S (S n) because then Rocq can see, for example, that 4 is
    S (S 2). *)
Inductive even : nat -> Prop :=
| Even_0 :
    (*──────────*)
       even 0

| Even_plus2 n :
       even n ->
    (*──────────────────*)
       even (S (S n)).

(** Forwards: 4 is even.  We build the tree from the bottom up:

          ────── Even_0
          even 0
          ────── Even_plus2
          even 2
          ────── Even_plus2
          even 4                                                    *)
Example four_even : even 4.
Proof.
  (* 4 is S (S 2), so Even_plus2 fits.  Its premise is the new goal:
     even 2. *)
  apply Even_plus2.
  (* 2 is S (S 0), so Even_plus2 fits again.  New goal: even 0. *)
  apply Even_plus2.
  (* even 0 is exactly the rule Even_0, which has no premises. *)
  apply Even_0.
Qed.

(** Backwards: if even (n + 2) then even n.

    Suppose we are given H : even (S (S n)).  How could H have been
    built?
    - Even_0 concludes even 0, and S (S n) is not 0.  It does not fit.
    - Even_plus2 concludes even (S (S m)) for some m.  It fits, with
      m = n.
    So H must end in Even_plus2.  A rule only applies when its premises
    hold, so its premise, even n, holds too.

    Again, knowing what n is tells us nothing here; only the evidence H
    contains the fact that n is even. *)
Theorem even_plus2_inv : forall n, even (S (S n)) -> even n.
Proof.
  intros n H.
  (* Only Even_plus2 fits, so inversion gives us its premise, even n, as
     a new hypothesis.  It also produces an equation saying which n the
     rule was used with; [subst] uses it to tidy up. *)
  inversion H. subst.
  (* The premise we got is exactly the goal. *)
  assumption.
Qed.

(** No rule fits: 1 is not even.

    Suppose we are given H : even 1.  How could H have been built?
    - Even_0 concludes even 0, and 1 is not 0.
    - Even_plus2 concludes even (S (S m)), which is at least 2, and 1
      is less than 2.
    No rule fits, so H cannot exist.  Inversion sees this and finishes
    the proof. *)
Theorem one_not_even : even 1 -> False.
Proof.
  intros H.
  inversion H.
Qed.

(* ================================================================= *)
(* PAGE:INVERSION-BIGSTEP *)
(** ** Back to big-step semantics

    Anti-reduction uses exactly this move.  Here is a tiny version of
    our arithmetic expressions, with just numbers, variables and +, and
    its big-step semantics. *)

From Coq Require Import String.

Inductive aexp : Type :=
| ANum (n : nat)
| AId (x : string)
| APlus (a1 a2 : aexp).

(** σ : Var → nat *)
Definition state := string -> nat.

(** ⟨a, σ⟩ ⇓a n: in state σ, expression a evaluates to n. *)
Reserved Notation "⟨ a , σ ⟩ '⇓a' n"
  (at level 70, a at level 99, σ at level 99, n at level 69).

Inductive aeval (σ : state) : aexp -> nat -> Prop :=
| AE_Num n :
    (*──────────────────*)
       ⟨ANum n, σ⟩ ⇓a n

| AE_Id x :
    (*──────────────────*)
       ⟨AId x, σ⟩ ⇓a σ x

| AE_Plus a1 a2 m1 m2 :
       ⟨a1, σ⟩ ⇓a m1 ->
       ⟨a2, σ⟩ ⇓a m2 ->
    (*──────────────────────────────────*)
       ⟨APlus a1 a2, σ⟩ ⇓a m1 + m2

where "⟨ a , σ ⟩ '⇓a' n" := (aeval σ a n).

(** Suppose we are given H : ⟨a1 + a2, σ⟩ ⇓a n.  How could H have been
    built?
    - AE_Num is about a number, not a +.
    - AE_Id is about a variable, not a +.
    - AE_Plus is about a +.  It fits.
    So, just as with even (S (S n)), H must end in AE_Plus, and both of
    its premises hold: a1 and a2 evaluate to some m1 and m2, with
    n = m1 + m2. *)
Theorem plus_inv : forall σ a1 a2 n,
    ⟨APlus a1 a2, σ⟩ ⇓a n ->
    exists m1 m2, ⟨a1, σ⟩ ⇓a m1 /\ ⟨a2, σ⟩ ⇓a m2 /\ n = m1 + m2.
Proof.
  intros σ a1 a2 n H.
  (* Only AE_Plus fits.  Inversion hands us its premises:
       H2 : ⟨a1, σ⟩ ⇓a m1      H4 : ⟨a2, σ⟩ ⇓a m2
     and replaces n by m1 + m2. *)
  inversion H. subst.
  (* Now we just say which m1 and m2, and show the three facts. *)
  exists m1, m2.
  split.
  - assumption.
  - split.
    + assumption.
    + reflexivity.
Qed.

End InversionDemo.

(* PAGE:FULL-IMP *)
Module FullIMP.
(** * CSE 590 discussion: big-step and small-step IMP in Coq

    Companion to Lectures 8 (9/28) and 9 (9/30).

    Plan
    - Part 1  Concrete runs: Euclid both ways, step by step.
    - Part 2  Divergence: W∞ loops in small-step and has no big-step
              derivation (the [remember] trick).
    - Part 3  The agreement theorem for commands, end to end.

    Boolean expressions only have constants, comparisons, and negation;
    ∧ and ∨ are left out on purpose (HW3 Exercise 1).  The bexp lemmas of
    Part 3 are [Admitted]; [Print Assumptions] at the end shows exactly
    what the command theorem rests on. *)

From Coq Require Import ZArith Bool.
Open Scope Z_scope.

(* ================================================================= *)
(** ** Syntax *)

(** A small fixed set of variables keeps goals readable. *)
Inductive var := M | N | X | Y.

Definition var_eqb (x y : var) : bool :=
  match x, y with
  | M, M | N, N | X, X | Y, Y => true
  | _, _ => false
  end.

Inductive aop := Plus | Minus | Mult.
Inductive cop := Eq | Le.

(** One binary-operator constructor stands for all of + − ∗: the slides'
    "analogous rules for ∗ and −" become a single set of rules. *)
Inductive aexp :=
| ANum (n : Z)
| AId (x : var)
| ABin (op : aop) (a1 a2 : aexp).

Inductive bexp :=
| BConst (t : bool)
| BCmp (op : cop) (a1 a2 : aexp)
| BNot (b : bexp).

Inductive com :=
| CSkip
| CAsgn (x : var) (a : aexp)
| CSeq (c1 c2 : com)
| CIf (b : bexp) (c1 c2 : com)
| CWhile (b : bexp) (c : com).

Coercion ANum : Z >-> aexp.
Coercion AId : var >-> aexp.

Notation "x '::=' a" := (CAsgn x a) (at level 60).
Notation "c1 ;; c2" := (CSeq c1 c2) (at level 80, right associativity).
Notation "'WHILE' b 'DO' c 'END'" := (CWhile b c) (at level 80).
Notation "'IF' b 'THEN' c1 'ELSE' c2 'FI'" := (CIf b c1 c2) (at level 80).

Definition aden (op : aop) : Z -> Z -> Z :=
  match op with Plus => Z.add | Minus => Z.sub | Mult => Z.mul end.

Definition cden (op : cop) : Z -> Z -> bool :=
  match op with Eq => Z.eqb | Le => Z.leb end.

(* ================================================================= *)
(** ** States: total functions [var -> Z] *)

Definition state := var -> Z.

Definition empty : state := fun _ => 0.

(** σ[x ↦ n] *)
Definition upd (s : state) (x : var) (n : Z) : state :=
  fun y => if var_eqb y x then n else s y.

(* ================================================================= *)
(** ** Big-step semantics *)

(** Side conditions such as [n = n1 + n2] come last, as on the slides, so
    that by the time Coq reaches them [n1] and [n2] are known. *)
Inductive aeval (s : state) : aexp -> Z -> Prop :=
| AE_Num n : aeval s (ANum n) n
| AE_Id x : aeval s (AId x) (s x)
| AE_Bin op a1 a2 n1 n2 n :
    aeval s a1 n1 -> aeval s a2 n2 -> n = aden op n1 n2 ->
    aeval s (ABin op a1 a2) n.

Inductive beval (s : state) : bexp -> bool -> Prop :=
| BE_Const t : beval s (BConst t) t
| BE_Cmp op a1 a2 n1 n2 t :
    aeval s a1 n1 -> aeval s a2 n2 -> t = cden op n1 n2 ->
    beval s (BCmp op a1 a2) t
| BE_Not b t t' :
    beval s b t -> t' = negb t ->
    beval s (BNot b) t'.

(** ⟨c, σ⟩ ⇓ τ, on configurations, as in ⇓ ⊆ (Com × State) × State. *)
Inductive ceval : com * state -> state -> Prop :=
| CE_Skip s :
    ceval (CSkip, s) s
| CE_Asgn x a s n :
    aeval s a n ->
    ceval (x ::= a, s) (upd s x n)
| CE_Seq c1 c2 s s' s'' :
    ceval (c1, s) s' -> ceval (c2, s') s'' ->
    ceval (c1 ;; c2, s) s''
| CE_IfT b c1 c2 s s' :
    beval s b true -> ceval (c1, s) s' ->
    ceval (IF b THEN c1 ELSE c2 FI, s) s'
| CE_IfF b c1 c2 s s' :
    beval s b false -> ceval (c2, s) s' ->
    ceval (IF b THEN c1 ELSE c2 FI, s) s'
| CE_WhileF b c s :
    beval s b false ->
    ceval (WHILE b DO c END, s) s
| CE_WhileT b c s s' s'' :
    beval s b true -> ceval (c, s) s' -> ceval (WHILE b DO c END, s') s'' ->
    ceval (WHILE b DO c END, s) s''.

(* ================================================================= *)
(** ** Small-step semantics *)

(** Expressions: the state is carried along, so it is a parameter. *)
Inductive astep (s : state) : aexp -> aexp -> Prop :=
| AS_Id x : astep s (AId x) (ANum (s x))
| AS_Bin op n1 n2 n :
    n = aden op n1 n2 ->
    astep s (ABin op (ANum n1) (ANum n2)) (ANum n)
| AS_Bin1 op a1 a1' a2 :
    astep s a1 a1' ->
    astep s (ABin op a1 a2) (ABin op a1' a2)
| AS_Bin2 op n1 a2 a2' :
    astep s a2 a2' ->
    astep s (ABin op (ANum n1) a2) (ABin op (ANum n1) a2').

Inductive bstep (s : state) : bexp -> bexp -> Prop :=
| BS_Cmp op n1 n2 t :
    t = cden op n1 n2 ->
    bstep s (BCmp op (ANum n1) (ANum n2)) (BConst t)
| BS_Cmp1 op a1 a1' a2 :
    astep s a1 a1' ->
    bstep s (BCmp op a1 a2) (BCmp op a1' a2)
| BS_Cmp2 op n1 a2 a2' :
    astep s a2 a2' ->
    bstep s (BCmp op (ANum n1) a2) (BCmp op (ANum n1) a2')
| BS_Not t :
    bstep s (BNot (BConst t)) (BConst (negb t))
| BS_Not1 b b' :
    bstep s b b' ->
    bstep s (BNot b) (BNot b').

Inductive cstep : com * state -> com * state -> Prop :=
| CS_Asgn1 x a a' s :
    astep s a a' ->
    cstep (x ::= a, s) (x ::= a', s)
| CS_Asgn x n s :
    cstep (x ::= ANum n, s) (CSkip, upd s x n)
| CS_Seq1 c1 c1' c2 s s' :
    cstep (c1, s) (c1', s') ->
    cstep (c1 ;; c2, s) (c1' ;; c2, s')
| CS_SeqSkip c2 s :
    cstep (CSkip ;; c2, s) (c2, s)
| CS_If1 b b' c1 c2 s :
    bstep s b b' ->
    cstep (IF b THEN c1 ELSE c2 FI, s) (IF b' THEN c1 ELSE c2 FI, s)
| CS_IfT c1 c2 s :
    cstep (IF BConst true THEN c1 ELSE c2 FI, s) (c1, s)
| CS_IfF c1 c2 s :
    cstep (IF BConst false THEN c1 ELSE c2 FI, s) (c2, s)
| CS_While b c s :
    cstep (WHILE b DO c END, s)
          (IF b THEN (c ;; WHILE b DO c END) ELSE CSkip FI, s).

(** →* as rules (refl) and (step), once for every relation. *)
Inductive multi {A : Type} (R : A -> A -> Prop) : A -> A -> Prop :=
| multi_refl x : multi R x x
| multi_step x y z : R x y -> multi R y z -> multi R x z.

Arguments multi_refl {A R x}.
Arguments multi_step {A R x y z}.

Notation "k '-->*' k'" := (multi cstep k k') (at level 40).

Global Hint Constructors aeval beval ceval astep bstep cstep : imp.

(* ================================================================= *)
(** * Part 1: concrete runs *)

(** Euclid, from Winskel Ch. 2. *)
Definition B : com :=
  IF BCmp Le M N
  THEN N ::= ABin Minus N M
  ELSE M ::= ABin Minus M N FI.

Definition W : com := WHILE BNot (BCmp Eq M N) DO B END.

Definition s0 : state := upd (upd empty M 6) N 4.
Definition s1 : state := upd s0 M 2.
Definition s2 : state := upd s1 N 2.

(** *** A warm-up: one assignment, small-step

    Watch [1 + X] go left operand first, then the variable lookup, then
    the addition, then the assignment itself.  Each [eapply multi_step]
    leaves the next configuration as an evar; [eauto with imp] finds the
    one rule that applies, and [simpl] tidies the goal. *)

Example asgn_small :
  (Y ::= ABin Plus 1 X, upd empty X 41) -->* (CSkip, upd (upd empty X 41) Y 42).
Proof.
  eapply multi_step. { eauto with imp. } simpl.
  (* goal: (Y ::= ABin Plus 1 41, ...) -->* ... *)
  eapply multi_step. { eauto with imp. } simpl.
  (* goal: (Y ::= ANum 42, ...) -->* ... *)
  eapply multi_step. { eauto with imp. } simpl.
  (* goal: (CSkip, upd (upd empty X 41) Y 42) -->* ... *)
  apply multi_refl.
Qed.

(** The same, big-step: one derivation tree, no intermediate configurations. *)
Example asgn_big :
  ceval (Y ::= ABin Plus 1 X, upd empty X 41) (upd (upd empty X 41) Y 42).
Proof.
  apply CE_Asgn.
  eapply AE_Bin.
  - apply AE_Num.
  - apply AE_Id.
  - reflexivity.     (* 42 = 1 + 41 *)
Qed.

(** *** Euclid, big-step: the derivation on slides 10–12

    Build the outer while by hand, choosing the rules, then let [eauto]
    fill the expression-level leaves. *)

Example euclid_big : ceval (W, s0) s2.
Proof.
  unfold W.
  (* ¬(M = N) is true at s0, so the loop runs: rule while-true,
     with intermediate state s1. *)
  apply CE_WhileT with (s' := s1).
  - eauto with imp.                          (* ⟨¬(M = N), s0⟩ ⇓b true *)
  - unfold B, s1. apply CE_IfF.              (* M ≤ N is false at s0 *)
    + eauto with imp.
    + apply CE_Asgn. eauto with imp.
  - apply CE_WhileT with (s' := s2).         (* (2) in the slides *)
    + eauto with imp.
    + unfold B, s2. apply CE_IfT.            (* M ≤ N is true at s1 *)
      * eauto with imp.
      * apply CE_Asgn. eauto with imp.
    + apply CE_WhileF.                       (* (3): the loop exits *)
      eauto with imp.
Qed.

(** Try: [Print euclid_big.] — that term *is* the tree on slide 12. *)

(** The same choices, automated.  Big-step is syntax-directed except at
    [if] and [while], where we try the rule whose guard evaluates the
    right way.  (Plain [eauto 20 with imp] also finds the tree, but the
    blind search takes ~25 s.)  On W∞ this tactic would never stop: it
    keeps applying while-true, which is the missing derivation in action. *)
Ltac big :=
  repeat match goal with
  | |- ceval (WHILE _ DO _ END, _) _ =>
      first [ apply CE_WhileF; solve [eauto with imp] | eapply CE_WhileT ]
  | |- ceval (IF _ THEN _ ELSE _ FI, _) _ =>
      first [ apply CE_IfT; [solve [eauto with imp] |]
            | apply CE_IfF; [solve [eauto with imp] |] ]
  | |- ceval (_ ;; _, _) _ => eapply CE_Seq
  | |- ceval (_ ::= _, _) _ => apply CE_Asgn
  | |- ceval (CSkip, _) _ => apply CE_Skip
  | |- beval _ _ _ => solve [eauto with imp]
  | |- aeval _ _ _ => solve [eauto with imp]
  end.

Example euclid_big_auto : ceval (W, s0) s2.
Proof. unfold W, B, s2, s1. big. Qed.

(** *** Euclid, small-step: "about thirty steps"

    Step the first few by hand, looking at each configuration, then
    finish the remaining 30.  Change [do 30] to see where it gets stuck. *)

Ltac step := eapply multi_step; [solve [eauto with imp] | simpl].

Example euclid_small : (W, s0) -->* (CSkip, s2).
Proof.
  unfold W, B.
  step.   (* unfold while into if *)
  step.   (* M ↦ 6 inside ¬(M = N) *)
  step.   (* N ↦ 4 *)
  step.   (* 6 = 4 ↦ false *)
  step.   (* ¬false ↦ true *)
  step.   (* if true: run the body, then the loop again *)
  do 30 step.   (* 36 steps in all *)
  apply multi_refl.
Qed.

(* ================================================================= *)
(* PAGE:FULL-DIVERGENCE *)
(** * Part 2: divergence *)

Definition Winf : com := WHILE BConst true DO CSkip END.

(** Small-step: W∞ comes back to itself in three steps, forever:
    while ↦ if true then (skip ; W∞) else skip ↦ skip ; W∞ ↦ W∞. *)
Example Winf_loops : forall s, (Winf, s) -->* (Winf, s).
Proof.
  intros s. unfold Winf.
  step. step. step.
  apply multi_refl.
Qed.

(** Big-step: there is *no* τ with ⟨W∞, σ⟩ ⇓ τ.

    Proof by rule induction on the (hypothetical) derivation.  First try
    the naive [induction H] below and look at the goals: Coq's [induction]
    forgets that the configuration was (Winf, s), so the cases are
    unprovable.  The fix is the same move as in lecture 9: generalize the
    index first ([remember]), then induct. *)

Theorem Winf_no_bigstep : forall s t, ~ ceval (Winf, s) t.
Proof.
  intros s t H.
  (* induction H.   <- try this first, then Undo *)
  remember (Winf, s) as k eqn:Ek.
  revert s Ek.
  induction H; intros s0 Ek; inversion Ek; subst.
  - (* while-false: needs ⟨true, s⟩ ⇓b false — impossible, by inversion *)
    inversion H.
  - (* while-true: the third premise is a smaller derivation for W∞ *)
    eapply IHceval2. reflexivity.
Qed.

(* ================================================================= *)
(* PAGE:FULL-AGREEMENT *)
(** * Part 3: small-step and big-step agree, for commands *)

(** *** Facts about →* *)

Lemma multi_one {A} {R : A -> A -> Prop} x y : R x y -> multi R x y.
Proof. intros H. eapply multi_step; [exact H | apply multi_refl]. Qed.

Lemma multi_trans {A} {R : A -> A -> Prop} x y z :
  multi R x y -> multi R y z -> multi R x z.
Proof.
  intros H1 H2. induction H1.
  - exact H2.
  - eapply multi_step; eauto.
Qed.

(** Every congruence lemma ("runs lift through a0 + a1, c0 ; c1, ...") is
    the same induction on →*.  Prove it once: if [f] maps steps to steps,
    it maps runs to runs. *)
Lemma multi_map {A A'} (R : A -> A -> Prop) (R' : A' -> A' -> Prop) (f : A -> A') :
  (forall x y, R x y -> R' (f x) (f y)) ->
  forall x y, multi R x y -> multi R' (f x) (f y).
Proof.
  intros Hf x y H. induction H.
  - apply multi_refl.
  - eapply multi_step; eauto.
Qed.

Lemma cong_bin1 s op a1 a1' a2 :
  multi (astep s) a1 a1' -> multi (astep s) (ABin op a1 a2) (ABin op a1' a2).
Proof.
  intros H. exact (multi_map _ _ (fun a => ABin op a a2)
                     (fun x y Hxy => AS_Bin1 s op x y a2 Hxy) _ _ H).
Qed.

Lemma cong_bin2 s op n1 a2 a2' :
  multi (astep s) a2 a2' ->
  multi (astep s) (ABin op (ANum n1) a2) (ABin op (ANum n1) a2').
Proof.
  intros H. exact (multi_map _ _ (fun a => ABin op (ANum n1) a)
                     (fun x y Hxy => AS_Bin2 s op n1 x y Hxy) _ _ H).
Qed.

Lemma cong_asgn s x a a' :
  multi (astep s) a a' -> (x ::= a, s) -->* (x ::= a', s).
Proof.
  intros H. exact (multi_map _ _ (fun a => (x ::= a, s))
                     (fun u v Huv => CS_Asgn1 x u v s Huv) _ _ H).
Qed.

Lemma cong_if s b b' c1 c2 :
  multi (bstep s) b b' ->
  (IF b THEN c1 ELSE c2 FI, s) -->* (IF b' THEN c1 ELSE c2 FI, s).
Proof.
  intros H. exact (multi_map _ _ (fun b => (IF b THEN c1 ELSE c2 FI, s))
                     (fun u v Huv => CS_If1 u v c1 c2 s Huv) _ _ H).
Qed.

Lemma cong_seq c1 c2 s c1' s' :
  (c1, s) -->* (c1', s') -> (c1 ;; c2, s) -->* (c1' ;; c2, s').
Proof.
  intros H.
  exact (multi_map _ _ (fun k => (fst k ;; c2, snd k))
           (fun u v Huv => match u, v return cstep u v ->
                                 cstep (fst u ;; c2, snd u) (fst v ;; c2, snd v) with
                           | (_, _), (_, _) => fun H => CS_Seq1 _ _ _ _ _ H
                           end Huv)
           _ _ H).
Qed.

(** *** Arithmetic expressions (done in lecture 9) *)

Lemma aeval_multi s a n : aeval s a n -> multi (astep s) a (ANum n).
Proof.
  intros H. induction H.
  - apply multi_refl.
  - apply multi_one. apply AS_Id.
  - subst. eapply multi_trans. { apply cong_bin1. exact IHaeval1. }
    eapply multi_trans. { apply cong_bin2. exact IHaeval2. }
    apply multi_one. apply AS_Bin. reflexivity.
Qed.

(** Anti-reduction for aexps: induction on the step, inversion on the
    big-step derivation. *)
Lemma astep_antired s a a' : astep s a a' -> forall n, aeval s a' n -> aeval s a n.
Proof.
  intros H. induction H; intros m Hm.
  - inversion Hm; subst. apply AE_Id.
  - inversion Hm; subst. eauto with imp.
  - inversion Hm; subst. eauto with imp.
  - inversion Hm; subst. eauto with imp.
Qed.

(** *** Boolean expressions: HW3 territory, so admitted here *)

Lemma beval_multi s b t : beval s b t -> multi (bstep s) b (BConst t).
Admitted.

Lemma bstep_antired s b b' : bstep s b b' -> forall t, beval s b' t -> beval s b t.
Admitted.

(** *** ⇓ implies →*: rule induction on the big-step derivation *)

Theorem ceval_multi : forall k t, ceval k t -> k -->* (CSkip, t).
Proof.
  intros k t H. induction H.
  - (* skip *)
    apply multi_refl.
  - (* x := a:  ⟨x := a, σ⟩ →* ⟨x := n, σ⟩ → ⟨skip, σ[x ↦ n]⟩ *)
    eapply multi_trans. { apply cong_asgn. apply aeval_multi. eassumption. }
    apply multi_one. apply CS_Asgn.
  - (* c1 ; c2:  →* ⟨skip ; c2, σ'⟩ → ⟨c2, σ'⟩ →* ⟨skip, σ''⟩ *)
    eapply multi_trans. { apply cong_seq. exact IHceval1. }
    eapply multi_step. { apply CS_SeqSkip. }
    exact IHceval2.
  - (* if, true *)
    eapply multi_trans. { apply cong_if. apply beval_multi. eassumption. }
    eapply multi_step. { apply CS_IfT. }
    exact IHceval.
  - (* if, false *)
    eapply multi_trans. { apply cong_if. apply beval_multi. eassumption. }
    eapply multi_step. { apply CS_IfF. }
    exact IHceval.
  - (* while, false *)
    eapply multi_step. { apply CS_While. }
    eapply multi_trans. { apply cong_if. apply beval_multi. eassumption. }
    apply multi_one. apply CS_IfF.
  - (* while, true: the long chain from lecture 9 *)
    eapply multi_step. { apply CS_While. }
    eapply multi_trans. { apply cong_if. apply beval_multi. eassumption. }
    eapply multi_step. { apply CS_IfT. }
    eapply multi_trans. { apply cong_seq. exact IHceval1. }
    eapply multi_step. { apply CS_SeqSkip. }
    exact IHceval2.
Qed.

(** *** Anti-reduction: κ → κ' and κ' ⇓ τ imply κ ⇓ τ

    Induction on the single step; in each case, invert the big-step
    derivation of κ'. *)

Lemma cstep_antired : forall k k', cstep k k' -> forall t, ceval k' t -> ceval k t.
Proof.
  intros k k' H. induction H; intros t Ht.
  - (* x := a → x := a' *)
    inversion Ht; subst.
    apply CE_Asgn. eapply astep_antired; eassumption.
  - (* x := n → skip:  invert ⟨skip, σ[x ↦ n]⟩ ⇓ τ to get τ = σ[x ↦ n] *)
    inversion Ht; subst.
    apply CE_Asgn. apply AE_Num.
  - (* c1 ; c2 → c1' ; c2:  invert the seq, use the IH on c1 *)
    inversion Ht; subst.
    eapply CE_Seq; eauto.
  - (* skip ; c2 → c2:  no IH needed *)
    eapply CE_Seq. { apply CE_Skip. } exact Ht.
  - (* guard steps:  invert, two cases *)
    inversion Ht; subst.
    + apply CE_IfT; [eapply bstep_antired|]; eassumption.
    + apply CE_IfF; [eapply bstep_antired|]; eassumption.
  - (* if true *)
    apply CE_IfT; [apply BE_Const | exact Ht].
  - (* if false *)
    apply CE_IfF; [apply BE_Const | exact Ht].
  - (* while unfolds: an axiom of →, so no IH; invert twice *)
    inversion Ht; subst.
    + (* guard true: invert the seq *)
      match goal with H : ceval (_ ;; _, _) _ |- _ => inversion H; subst end.
      eapply CE_WhileT; eassumption.
    + (* guard false: invert ⟨skip, σ⟩ ⇓ τ, so τ = σ *)
      match goal with H : ceval (CSkip, _) _ |- _ => inversion H; subst end.
      apply CE_WhileF. assumption.
Qed.

(** *** →* implies ⇓: rule induction on →*

    The theorem fixes the end configuration to ⟨skip, τ⟩, but (step)
    has an arbitrary end configuration.  State the motive with it
    general. *)

Lemma multi_ceval : forall k k'', k -->* k'' -> forall t, k'' = (CSkip, t) -> ceval k t.
Proof.
  intros k k'' H. induction H; intros t E.
  - (* refl: κ = ⟨skip, τ⟩ *)
    subst. apply CE_Skip.
  - (* step: κ → κ' →* ⟨skip, τ⟩; IH then anti-reduction *)
    eapply cstep_antired; eauto.
Qed.

Theorem big_small : forall c s t, ceval (c, s) t <-> (c, s) -->* (CSkip, t).
Proof.
  intros c s t. split.
  - apply ceval_multi.
  - intros H. eapply multi_ceval; eauto.
Qed.

(** What does the theorem rest on?  Exactly the two bexp lemmas. *)
Print Assumptions big_small.

(** Corollary: small-step never reaches skip from W∞, for free. *)
Corollary Winf_never_skip : forall s t, ~ (Winf, s) -->* (CSkip, t).
Proof.
  intros s t H. apply big_small in H. eapply Winf_no_bigstep. exact H.
Qed.

End FullIMP.
