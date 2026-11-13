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

    *** Tactics used in the discussion sections

    - [apply R]: "use rule R".  If R's conclusion matches the goal, the
      goal is replaced by R's premises.  This builds a derivation tree
      from the bottom up.

    - [apply R with (n0 := 5)]: the same, but we tell Rocq a value it
      cannot guess on its own.

    - [reflexivity]: proves an equation whose two sides compute to the
      same thing.

    - [unfold e]: replaces the name [e] with what it stands for.

    - [-], [+], [*], and [{ }]: bullets separate the premises left by a
      rule.

    - [intros H]: assumes the premise of an implication, names it [H],
      and leaves the conclusion to prove.

    - [induction H as [...]]: performs rule induction on [H].  There is
      one case for each rule that could have built the derivation.

    - [inversion H]: asks how [H] could have been built, eliminates rules
      that cannot fit, and exposes the premises of the remaining rules.

    - [subst]: uses equations between variables to replace one with the
      other everywhere.

    - [rewrite E]: uses an equation to replace one side by the other.

    - [split]: turns an if-and-only-if goal into its two directions.

    *** A small file to step through

    Run the definitions first.  Then step through each proof and watch
    the goal change on the right. *)

From Coq Require Import ZArith.
Open Scope Z_scope.

Definition double (n : Z) : Z := n + n.

Inductive even : Z -> Prop :=
| Even_0 : even 0
| Even_plus_2 n : even n -> even (n + 2).

Example double_two : double 2 = 4.
Proof.
  unfold double.
  reflexivity.
Qed.

Example even_four : even 4.
Proof.
  change (even (2 + 2)).
  apply Even_plus_2.
  change (even (0 + 2)).
  apply Even_plus_2.
  apply Even_0.
Qed.
(* PAGE:ROCQ-GUIDE-END *)
