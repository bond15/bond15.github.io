(* PAGE:ROCQ-GUIDE *)
(** ** Getting started

    This file is written in Rocq (previously named Coq), a proof
    assistant: you state something, prove it, and Rocq checks every step.

    *** Running it in your browser (jsCoq)

    - This page already contains jsCoq.  Nothing to install.
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

    *** Reading a Rocq file

    - [Definition] gives a name to something.

    - [Inductive] defines a relation by its rules.  Each line starting
      with | is one inference rule: premises above the bar, conclusion
      below it.

    - [Example] states a fact, and the proof goes between [Proof.] and
      [Qed.].  The proof is a list of tactics: commands that build the
      proof one step at a time.

    *** Core tactics used in the discussion sections

    - [apply R] uses a theorem or inference rule whose conclusion matches
      the goal; its premises become new goals.  [eapply R] does the same
      while leaving values that Rocq cannot yet infer as temporary holes.

    - [apply R with (n0 := 5)]: the same, but we tell Rocq a value it
      cannot guess on its own.

    - [exact t] supplies the complete proof term [t].  [assumption] uses
      a matching hypothesis; [eassumption] may leave temporary holes.

    - [intros H] assumes the premise of an implication or introduces a
      universally quantified variable.  [intro] introduces one item.

    - [reflexivity]: proves an equation whose two sides compute to the
      same thing.  [symmetry] reverses an equality, and [transitivity y]
      inserts the intermediate expression [y].

    - [rewrite E] replaces one side of equation [E] by the other.
      [unfold e] replaces the name [e] with what it stands for.

    - [simpl] performs routine computation.  [cbn] reduces by call by
      name; [cbv] reduces by call by value; [compute] fully normalizes a
      closed expression.  [change P] replaces the goal by a definitionally
      equal proposition [P].

    - [constructor] applies the constructor that builds the goal.
      [split] handles conjunction or if-and-only-if; [left] and [right]
      choose a disjunct; [exists x] supplies an existential witness.

    *** Cases, induction, and impossible evidence

    - [destruct x] performs case analysis on data or evidence.
      [induction H] performs induction and supplies an induction
      hypothesis for every recursive premise.  An [as] clause names the
      values and hypotheses created in each case.

    - [inversion H]: asks how [H] could have been built, eliminates rules
      that cannot fit, and exposes the premises of the remaining rules.

    - [subst]: uses equations between variables to replace one with the
      other everywhere.  [injection H] extracts equalities between the
      arguments of equal constructors.

    - [discriminate H] closes a goal when [H] equates different
      constructors.  [congruence] combines constructor discrimination,
      injectivity, and equalities automatically.

    - [contradiction] closes a contradictory context.  [exfalso] changes
      the goal to [False].

    *** Controlling hypotheses and proof shape

    - [revert x] moves [x] and dependent hypotheses back into the goal.
      [generalize t] replaces [t] by a fresh variable before induction.

    - [remember t as x eqn:E] gives [t] a name while retaining the
      equation [E].  This is useful when ordinary induction forgets the
      exact indexed expression.

    - [assert (H : P)] creates a new goal for [P] and then adds [H : P]
      to the original goal.  [clear H] removes an unused hypothesis.

    - The modifiers [as] and [eqn:] name generated variables and
      equations.  [in H] applies a tactic to hypothesis [H] instead of
      the goal.  [with] supplies an argument that inference cannot find.

    - [-], [+], [*], and [{ }] separate sibling goals.  The semicolon in
      [t1; t2] runs [t2] on every goal produced by [t1].

    *** Automation and custom tactics

    - [eauto] searches the available rules; [eauto with imp] also uses
      the named hint database [imp].  It may be convenient, but hides
      which rules were chosen.

    - [try t] runs [t] if it works, [repeat t] runs it until it stops
      making progress, and [do n t] runs it exactly [n] times.

    - [first], [solve], [now], and [progress] control tactic search and
      failure.  [fail] deliberately rejects the current branch.
      [match goal with ... end] selects a tactic by the current goal or
      hypotheses.

    - [Ltac name := ...] defines a custom tactic.  The discussion sources
      define helpers such as [step], [run], [lift], and [big]; read their
      definitions before treating them as primitive commands.

    *** Commands outside proofs

    - [From Coq Require Import M] loads a library.  [Import M] opens an
      already loaded module.  [Open Scope s] enables a notation scope.
      [Set ...] changes a Rocq option.

    - [Definition] names a value or function.  [Fixpoint] defines a
      structurally recursive function.  [Inductive] declares data or an
      inference system by its constructors.

    - [Example], [Lemma], [Theorem], and [Corollary] state propositions
      to prove.  They differ mainly in the intended role of the result.

    - [Module] and [End] create a namespace.  [Section], [Context],
      [Variable] or [Variables], and [Hypothesis] share parameters across
      declarations.  [Let] makes a local definition.

    - [Notation], [Reserved Notation], and [Infix] define concrete
      syntax; a [where] clause attaches notation to the preceding
      declaration.  [Coercion] inserts a conversion automatically, while
      [Arguments] controls which parameters are implicit.

    - [Hint] adds rules to an automation database; [Local] and [Global]
      control how far such declarations reach.  [Check] displays a
      type, [Compute] evaluates a term, [Print] displays a declaration,
      and [Print Assumptions] exposes a theorem's trust dependencies.

    - [Axiom] introduces an unproved assumption.  [Admitted] ends the
      current proof without checking it.  Both become visible through
      [Print Assumptions] and mark a deliberate trust boundary.

    - [Abort] discards the current unfinished proof without creating a
      theorem.  Unlike [Admitted], it adds no assumption.

    *** A small file to step through

    Run the definitions first.  Then step through each proof and watch
    the goal change on the right. *)

From Coq Require Import ZArith.
Open Scope Z_scope.

Definition double (n : Z) : Z := n + n.

Inductive color : Type := Red | Blue.

Definition flip (c : color) : color :=
  match c with
  | Red => Blue
  | Blue => Red
  end.

Inductive even : Z -> Prop :=
| Even_0 : even 0
| Even_plus_2 n : even n -> even (n + 2).

Example double_two : double 2 = 4.
Proof.
  unfold double.
  reflexivity.
Qed.

Example flip_twice c : flip (flip c) = c.
Proof.
  destruct c; simpl; reflexivity.
Qed.

Example even_four : even 4.
Proof.
  change (even (2 + 2)).
  apply Even_plus_2.
  change (even (0 + 2)).
  apply Even_plus_2.
  apply Even_0.
Qed.

Example an_even_number_exists : exists n, even n.
Proof.
  exists 0.
  constructor.
Qed.

Example reuse_even_four : even 4.
Proof.
  exact even_four.
Qed.
(* PAGE:ROCQ-GUIDE-END *)
