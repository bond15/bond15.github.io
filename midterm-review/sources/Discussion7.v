(** * Products, sums, and what they mean

    CSE 590, Fall 2026.  Products and sums.

    - Part 1  Products and sums as data
    - Part 2  Isomorphisms
    - Part 3  The Curry-Howard correspondence *)

(* ================================================================= *)
(** * Part 1: Products and sums as data *)

(** Rocq already has the lecture's type formers.  These notations
    let us write them, and their programs, in the lecture's syntax:

        lecture                               Rocq
        τ₁ → τ₂                               τ₁ -> τ₂
        λx:τ. e                               fun x => e
        τ₁ × τ₂                               τ₁ * τ₂
        τ₁ + τ₂                               τ₁ + τ₂
        1                                     unit
        0                                     Empty_set
        ()                                    tt
        in₁ e,  in₂ e                         inl e,  inr e
        e.1,  e.2                             fst e,  snd e
        case₀ e {}                            match e with end
        case₊ e {in₁ x₁ → e₁ | in₂ x₂ → e₂}   match e with
                                              | inl x₁ => e₁
                                              | inr x₂ => e₂ end

    We write λx. e, with a comma for the dot, and give the type of x in
    the type of the whole definition.  In types, 1 and 0 now mean unit
    and Empty_set; in programs they are still the numbers 1 and 0. *)
Notation "τ₁ × τ₂" := (prod τ₁ τ₂) (at level 40, left associativity) : type_scope.
Notation "1" := unit : type_scope.
Notation "0" := Empty_set : type_scope.
Notation "()" := tt.
Notation in₁ := (@inl _ _).
Notation in₂ := (@inr _ _).
Notation "e .1" := (fst e) (at level 2, left associativity, format "e .1").
Notation "e .2" := (snd e) (at level 2, left associativity, format "e .2").
Notation "'case₀' e '{' '}'" := (match e with end) (at level 200, e at level 9).
Notation "'case₊' e '{' 'in₁' x₁ → e₁ | 'in₂' x₂ → e₂ '}'" :=
  (match e with inl x₁ => e₁ | inr x₂ => e₂ end)
  (at level 200, e at level 9, x₁ name, x₂ name,
   format "'case₊'  e  '{' 'in₁'  x₁  →  e₁  |  'in₂'  x₂  →  e₂ '}'").
Notation "τ₁ → τ₂" := (τ₁ -> τ₂) (at level 99, τ₂ at level 200, right associativity) : type_scope.
Notation "'λ' x .. y , e" := (fun x => .. (fun y => e) ..)
  (at level 200, x binder, y binder, right associativity).

Check (3, true) : nat × bool.
Check (3, true).1.
Check (in₁ 3 : nat + bool).
Check (in₂ true : nat + bool).
Check () : 1.

(** case₊ e {in₁ x₁ → e₁ | in₂ x₂ → e₂}, in Rocq: *)
Definition describe (s : nat + bool) : nat :=
  case₊ s {in₁ n → n | in₂ b → if b then 1 else 0}.

Example describe_ex : describe (in₂ true) = 1.
Proof. reflexivity. Qed.

(** 0 has no introduction form, so it has no values, and a case on it
    has no branches.  This is the lecture's case₀ e {}: from an
    impossible value, anything. *)
Definition absurd {τ : Type} (z : 0) : τ :=
  case₀ z {}.

(* ================================================================= *)
(** * Part 2: Isomorphisms *)

(** τ₁ and τ₂ are ISOMORPHIC, τ₁ ≅ τ₂, when there are programs
    f : τ₁ → τ₂ and g : τ₂ → τ₁ that undo each other, in both orders.
    g is a RETRACTION of f when g undoes f, and a SECTION of f when f
    undoes g.  Then τ₁ and τ₂ have "the same values, with different
    names". *)
Definition retraction {τ₁ τ₂ : Type} (f : τ₁ → τ₂) (g : τ₂ → τ₁) : Prop :=
  forall a : τ₁, g (f a) = a.
Definition section {τ₁ τ₂ : Type} (f : τ₁ → τ₂) (g : τ₂ → τ₁) : Prop :=
  forall b : τ₂, f (g b) = b.
Definition iso {τ₁ τ₂ : Type} (f : τ₁ → τ₂) (g : τ₂ → τ₁) : Prop :=
  retraction f g /\ section f g.

(** Each isomorphism below is a pair of programs, f and g, in a module
    of its own, so every module can use the names f and g.  Outside the
    module they are, for example, ProdUnit.f and ProdUnit.g.  The
    Section inside fixes the types the programs work on.

    The proofs that f and g undo each other follow the same pattern:
    unfold iso into its two laws and [split] them; in each, [cbv delta
    [f g]] unfolds f and g, putting in their programs, and [cbv beta]
    substitutes the argument (the β step); take the value apart with
    [destruct], one case per way it can be built; then [simpl] runs the
    rest, and [reflexivity] sees that both sides are the same.  The
    exceptions: for τ × 0 ≅ 0 nothing computes, since no value can be
    built, and for curry the values are functions, so the proof first
    uses funext. *)

(** ** τ × 1 ≅ τ *)

Module ProdUnit.
Section ProdUnit.
Context {τ : Type}.

Definition f : τ × 1 → τ := λ p, p.1.
Definition g : τ → τ × 1 := λ a, (a, ()).

Lemma prod_unit : iso f g.
Proof.
  unfold iso, retraction, section.  (* the two laws *)
  split.
  - (* g (f p) = p *)
    intros p.
    cbv delta [f g].  (* unfold f and g: put in their programs *)
    cbv beta.         (* substitute the argument: the β step *)
    (* (p.1, ()) = p computes no further until p is a pair (a, u),
       and u can only be () *)
    destruct p as [a u]. destruct u.
    simpl.        (* run the rest *)
    reflexivity.
  - (* f (g a) = a *)
    intros a.
    cbv delta [f g].
    cbv beta.
    simpl.
    reflexivity.
Qed.

End ProdUnit.
End ProdUnit.

(** ** τ + 0 ≅ τ *)

Module SumEmpty.
Section SumEmpty.
Context {τ : Type}.

(** The in₂ side holds a value of 0, which can't exist, so it never
    happens: case₀ handles it. *)
Definition f : τ + 0 → τ := λ s, case₊ s {in₁ a → a | in₂ z → case₀ z {}}.
Definition g : τ → τ + 0 := λ a, in₁ a.

Lemma sum_empty : iso f g.
Proof.
  unfold iso, retraction, section.
  split.
  - intros s.
    cbv delta [f g].
    cbv beta.
    (* a sum is in₁ a or in₂ z *)
    destruct s as [a | z].
    + simpl.
      reflexivity.
    + (* z : 0 has no cases *)
      destruct z.
  - intros a.
    cbv delta [f g].
    cbv beta.
    simpl.
    reflexivity.
Qed.

End SumEmpty.
End SumEmpty.

(** ** τ × 0 ≅ 0 *)

Module ProdEmpty.
Section ProdEmpty.
Context {τ : Type}.

(** τ pair needs a value of 0, so there are no such pairs, just as
    there are no values of 0.  Both proofs have no cases. *)
Definition f : τ × 0 → 0 := λ p, p.2.
Definition g : 0 → τ × 0 := λ z, case₀ z {}.

Lemma prod_empty : iso f g.
Proof.
  unfold iso, retraction, section.
  split.
  - intros p.
    cbv delta [f g].
    cbv beta.
    (* a pair (a, z) with z : 0: no cases *)
    destruct p as [a z]. destruct z.
  - intros z.
    cbv delta [f g].
    cbv beta.
    (* z : 0: no cases *)
    destruct z.
Qed.

End ProdEmpty.
End ProdEmpty.

(** ** τ₁ × τ₂ ≅ τ₂ × τ₁ *)

Module ProdComm.
Section ProdComm.
Context {τ₁ τ₂ : Type}.

(** Both directions swap the pair. *)
Definition f : τ₁ × τ₂ → τ₂ × τ₁ := λ p, (p.2, p.1).
Definition g : τ₂ × τ₁ → τ₁ × τ₂ := λ p, (p.2, p.1).

Lemma prod_comm : iso f g.
Proof.
  unfold iso, retraction, section.
  split.
  - intros p.
    cbv delta [f g].
    cbv beta.
    destruct p as [a b].
    simpl.
    reflexivity.
  - intros p.
    cbv delta [f g].
    cbv beta.
    destruct p as [b a].
    simpl.
    reflexivity.
Qed.

End ProdComm.
End ProdComm.

(** ** τ₁ × (τ₂ + τ₃) ≅ τ₁ × τ₂ + τ₁ × τ₃ *)

Module Dist.
Section Dist.
Context {τ₁ τ₂ τ₃ : Type}.

(** Distributivity: a pair whose second part is "a τ₂ or a τ₃" is the
    same as "a pair with a τ₂, or a pair with a τ₃". *)
Definition f : τ₁ × (τ₂ + τ₃) → τ₁ × τ₂ + τ₁ × τ₃ :=
  λ p, case₊ p.2 {in₁ b → in₁ (p.1, b) | in₂ c → in₂ (p.1, c)}.
Definition g : τ₁ × τ₂ + τ₁ × τ₃ → τ₁ × (τ₂ + τ₃) :=
  λ s, case₊ s {in₁ p → (p.1, in₁ p.2) | in₂ p → (p.1, in₂ p.2)}.

Lemma dist : iso f g.
Proof.
  unfold iso, retraction, section.
  split.
  - intros p.
    cbv delta [f g].
    cbv beta.
    (* a pair (a, s), and s is in₁ b or in₂ c *)
    destruct p as [a [b | c]].
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - intros s.
    cbv delta [f g].
    cbv beta.
    (* in₁ (a, b) or in₂ (a, c) *)
    destruct s as [[a b] | [a c]].
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

End Dist.
End Dist.

(** ** (τ₁ × τ₂ → τ₃) ≅ (τ₁ → τ₂ → τ₃) *)

Module Curry.
Section Curry.
Context {τ₁ τ₂ τ₃ : Type}.

(** τ₁ function of a pair is the same as a function that takes its two
    arguments one at a time.  f is usually called curry, and g uncurry. *)
Definition f : (τ₁ × τ₂ → τ₃) → (τ₁ → τ₂ → τ₃) := λ h, λ a, λ b, h (a, b).
Definition g : (τ₁ → τ₂ → τ₃) → (τ₁ × τ₂ → τ₃) := λ k, λ p, k p.1 p.2.

(** Here the values are functions.  Two functions are equal when they
    agree on every input.  Rocq can't prove this, so we assume it. *)
Axiom funext : forall {X Y : Type} (h k : X → Y),
  (forall x, h x = k x) → h = k.

Lemma curry : iso f g.
Proof.
  unfold iso, retraction, section.
  split.
  - (* g (f h) = h: they agree on every pair (a, b) *)
    intros h.
    cbv delta [f g].
    cbv beta.
    apply funext. intros [a b].
    simpl.
    reflexivity.
  - (* f (g k) = k: computes to λ a, λ b, k a b, which is k *)
    intros k.
    cbv delta [f g].
    cbv beta.
    simpl.
    reflexivity.
Qed.

End Curry.
End Curry.

(** ** bool ≅ 1 + 1 *)

Module BoolSum.

(** true is in₁ (), false is in₂ (), and if is a case.  This is why
    bool is also written 2. *)
Definition f : bool → 1 + 1 := λ b, if b then in₁ () else in₂ ().
Definition g : 1 + 1 → bool := λ s, case₊ s {in₁ u → true | in₂ u → false}.

Lemma bool_sum : iso f g.
Proof.
  unfold iso, retraction, section.
  split.
  - intros b.
    cbv delta [f g].
    cbv beta.
    destruct b.
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - intros s.
    cbv delta [f g].
    cbv beta.
    (* in₁ u or in₂ u, and u can only be () *)
    destruct s as [[] | []].
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

End BoolSum.

(** ** option τ ≅ 1 + τ *)

Module OptionSum.
Section OptionSum.
Context {τ : Type}.

(** None is in₁ (), Some a is in₂ a. *)
Definition f : option τ → 1 + τ :=
  λ o, match o with
       | None => in₁ ()
       | Some a => in₂ a
       end.
Definition g : 1 + τ → option τ := λ s, case₊ s {in₁ u → None | in₂ a → Some a}.

Lemma option_sum : iso f g.
Proof.
  unfold iso, retraction, section.
  split.
  - intros o.
    cbv delta [f g].
    cbv beta.
    destruct o as [a |].
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
  - intros s.
    cbv delta [f g].
    cbv beta.
    destruct s as [[] | a].
    + simpl.
      reflexivity.
    + simpl.
      reflexivity.
Qed.

End OptionSum.
End OptionSum.

(* ================================================================= *)
(** * Part 3: The Curry-Howard correspondence *)

(** Read a type as a proposition, and a program of that type as a proof
    of it (the Curry-Howard correspondence):

        type            proposition     Rocq
        1               true            True
        0               false           False
        τ₁ × τ₂         φ ∧ ψ           φ /\ ψ
        τ₁ + τ₂         φ ∨ ψ           φ \/ ψ
        τ₁ → τ₂         φ ⇒ ψ           φ -> ψ

    Look back at Part 2: every program there was a proof.  For example,
    ProdComm.f : τ₁ × τ₂ → τ₂ × τ₁ proves φ ∧ ψ ⇒ ψ ∧ φ, and
    Curry.f : (τ₁ × τ₂ → τ₃) → (τ₁ → τ₂ → τ₃) proves (φ ∧ ψ ⇒ ξ) ⇒ (φ ⇒ ψ ⇒ ξ).

    Rocq has both columns: [τ₁ × τ₂] at Type, [φ /\ ψ] at Prop.  The
    programs are the same. *)

(** ProdComm.f, at Type: a program. *)
Check ProdComm.f : nat × bool → bool × nat.

(** The same function at Prop: a proof that ∧ is commutative.  conj is
    the pair for /\, and match takes the pair apart. *)
Definition and_swap {φ ψ : Prop} (h : φ /\ ψ) : ψ /\ φ :=
  match h with
  | conj p q => conj q p
  end.

(** The same proof, written with tactics.  [Print] shows the program
    the tactics built. *)
Lemma and_swap' (φ ψ : Prop) : φ /\ ψ -> ψ /\ φ.
Proof.
  intros [p q].
  split.
  - exact q.
  - exact p.
Qed.

Print and_swap'.

(** case, at Prop: a proof by cases.  or_introl and or_intror are in₁
    and in₂ for \/. *)
Definition or_swap {φ ψ : Prop} (h : φ \/ ψ) : ψ \/ φ :=
  match h with
  | or_introl p => or_intror p
  | or_intror q => or_introl q
  end.

(** case₀ e {}, at Prop: from False, anything (ex falso). *)
Definition ex_falso {φ : Prop} (h : False) : φ :=
  match h with end.

(** Distributivity, at Prop: it does what Dist.f does, with a match on
    conj in place of projections. *)
Definition and_or_dist {φ ψ ξ : Prop} (h : φ /\ (ψ \/ ξ))
  : (φ /\ ψ) \/ (φ /\ ξ) :=
  match h with
  | conj p (or_introl q) => or_introl (conj p q)
  | conj p (or_intror r) => or_intror (conj p r)
  end.

(** Currying, at Prop: the same program as Curry.f. *)
Definition and_curry {φ ψ ξ : Prop} : (φ /\ ψ → ξ) → (φ → ψ → ξ) :=
  λ f, λ p, λ q, f (conj p q).

(** ** ∀ and ∃ *)

(** forall x : τ, φ x is a dependent function type: a program that,
    given any x, returns a proof of φ x.  Here the result type n = n
    mentions the argument n. *)
Definition refl_all : forall n : nat, n = n := λ n, eq_refl.

(** When the result type doesn't mention the argument, forall is just →. *)
Check (forall _ : nat, bool).

(** {x : τ | φ x} is a dependent pair: a witness x, with a proof of φ x.
    The type of the second part, Nat.even 4 = true, mentions the first. *)
Definition even_four : {n : nat | Nat.even n = true} := exist _ 4 eq_refl.

(** ** Excluded middle *)

(** φ ∨ ¬φ, where ¬φ is φ → False.  As a type, it is φ + (φ → 0): a
    program would have to choose in₁ or in₂, without knowing anything
    about φ.  There is no such program, so φ ∨ ¬φ can't be proved this
    way: the logic is intuitionistic.  Try it: neither [left] nor
    [right] gets anywhere. *)
Lemma excluded_middle (φ : Prop) : φ \/ ~ φ.
Proof.
  (* left: we would need a proof of φ.  right: we would need φ -> False. *)
Abort.

(** But it can't be refuted either: its double negation has a proof.
    Given h : ¬(φ ∨ ¬φ), choose right; to show ¬φ, assume p : φ, and
    then left p contradicts h. *)
Lemma not_not_excluded_middle (φ : Prop) : ~ ~ (φ \/ ~ φ).
Proof.
  intros h.
  apply h.
  right.
  intros p.
  apply h.
  left.
  exact p.
Qed.
