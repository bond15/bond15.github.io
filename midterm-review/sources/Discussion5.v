(** * Denotational semantics of IMP

    CSE 590, Fall 2026.  IMP and its big-step semantics, written the
    same way as in Discussion 4, then the denotational semantics from
    §3 of Kozen's Lecture 18 notes.

    - Part 1  𝒜⟦a⟧ and ℬ⟦b⟧: functions instead of relations.
    - Part 2  Partiality with option.
    - Part 3  𝒞⟦c⟧ : Env → option Env, and the base cases skip, :=, if.
    - Part 4  Sequencing: putting partial maps together.
    - Part 5  Equational reasoning: expressions, commands, loops.
    - Denotations forget running time: two programs, one meaning. *)

From Coq Require Import ZArith Bool String List.
Import ListNotations.
Open Scope Z_scope.
Open Scope string_scope.

(* ================================================================= *)
(** ** Syntax *)

Definition name := string.

(** AExp : a ::= n | x | a0 + a1 | a0 ∗ a1 | a0 − a1 *)
Inductive aexp : Type :=
| ANum (n : Z)
| AId (x : name)
| APlus (a0 a1 : aexp)
| AMult (a0 a1 : aexp)
| AMinus (a0 a1 : aexp).

(** BExp : b ::= true | false | a0 = a1 | a0 ≤ a1 | b0 ∨ b1 | b0 ∧ b1 | ¬b *)
Inductive bexp : Type :=
| BTrue
| BFalse
| BEq (a0 a1 : aexp)
| BLe (a0 a1 : aexp)
| BOr (b0 b1 : bexp)
| BAnd (b0 b1 : bexp)
| BNot (b : bexp).

(** Com : c ::= skip | x := a | c0 ; c1 | if b then c0 else c1
                | while b do c *)
Inductive com : Type :=
| CSkip
| CAsgn (x : name) (a : aexp)
| CSeq (c0 c1 : com)
| CIf (b : bexp) (c0 c1 : com)
| CWhile (b : bexp) (c : com).

(** Concrete syntax.  [const n] is the number n and [var x] is the
    variable x, as expressions.  ⊕, ⊗ and ⊖ are +, ∗ and − in the
    language, so they can't be confused with +, * and - on integers.
    In the same way, TRUE and FALSE are the Boolean expressions, and
    true and false are Rocq's Boolean values. *)
Notation "'const' n" := (ANum n) (at level 1, n at level 0).
Notation "'var' x" := (AId x) (at level 1, x at level 0).
Notation "a0 ⊕ a1" := (APlus a0 a1) (at level 50, no associativity).
Notation "a0 ⊗ a1" := (AMult a0 a1) (at level 50, no associativity).
Notation "a0 ⊖ a1" := (AMinus a0 a1) (at level 50, no associativity).

Notation "'TRUE'" := BTrue.
Notation "'FALSE'" := BFalse.
Notation "a0 == a1" := (BEq a0 a1) (at level 55, no associativity).
Notation "a0 ≤ a1" := (BLe a0 a1) (at level 55, no associativity).
Notation "¬ b" := (BNot b) (at level 56, right associativity).
Notation "b0 ∧ b1" := (BAnd b0 b1) (at level 57, left associativity).
Notation "b0 ∨ b1" := (BOr b0 b1) (at level 58, left associativity).

Notation "'skip'" := CSkip.
Notation "x ::= a" := (CAsgn x a) (at level 60).
Notation "c0 ;; c1" := (CSeq c0 c1) (at level 80, right associativity).
Notation "'IF' b 'THEN' c0 'ELSE' c1 'FI'" := (CIf b c0 c1) (at level 80).
Notation "'WHILE' b 'DO' c 'END'" := (CWhile b c) (at level 80).

Reserved Notation "⟨ a , σ ⟩ '⇓a' n"
  (at level 70, a at level 99, σ at level 99, n at level 69).
Reserved Notation "⟨ b , σ ⟩ '⇓b' t"
  (at level 70, b at level 99, σ at level 99, t at level 69).
Reserved Notation "⟨ c , σ ⟩ '⇓' τ"
  (at level 70, c at level 99, σ at level 99, τ at level 69).

(* ================================================================= *)
(** ** Environments *)

(** σ : Var → Z, total. *)
Definition Env := name -> Z.

(** σ[x ↦ n] is σ, except that x now holds n:
      σ[x ↦ n](y) = n      if y = x
      σ[x ↦ n](y) = σ(y)   otherwise *)
Definition upd (σ : Env) (x : name) (n : Z) : Env :=
  fun y => if String.eqb y x then n else σ y.


(* ================================================================= *)
(** * Part 1: 𝒜⟦a⟧ and ℬ⟦b⟧ *)


Reserved Notation "𝒜⟦ a ⟧" (at level 0, a at level 200).
Reserved Notation "ℬ⟦ b ⟧" (at level 0, b at level 200).
Reserved Notation "𝒞⟦ c ⟧" (at level 0, c at level 200).

(** In the ⊕ line, ⊕ on the left is + in the language, and + on the
    right is addition of integers.  The notes write + for both. *)
Fixpoint Asem (a : aexp) : Env -> Z :=
  fun σ =>
    match a with
    | const n => n
    | var x => σ x
    | a0 ⊕ a1 => 𝒜⟦a0⟧ σ + 𝒜⟦a1⟧ σ
    | a0 ⊗ a1 => 𝒜⟦a0⟧ σ * 𝒜⟦a1⟧ σ
    | a0 ⊖ a1 => 𝒜⟦a0⟧ σ - 𝒜⟦a1⟧ σ
    end
where "𝒜⟦ a ⟧" := (Asem a).


Fixpoint Bsem (b : bexp) : Env -> bool :=
  fun σ =>
    match b with
    | TRUE => true
    | FALSE => false
    | a0 == a1 => Z.eqb (𝒜⟦a0⟧ σ) (𝒜⟦a1⟧ σ)
    | a0 ≤ a1 => Z.leb (𝒜⟦a0⟧ σ) (𝒜⟦a1⟧ σ)
    | b0 ∨ b1 => ℬ⟦b0⟧ σ || ℬ⟦b1⟧ σ
    | b0 ∧ b1 => ℬ⟦b0⟧ σ && ℬ⟦b1⟧ σ
    | ¬ b0 => if ℬ⟦b0⟧ σ then false else true
    end
where "ℬ⟦ b ⟧" := (Bsem b).

(** *** Examples *)

Definition X : name := "X".
Definition Y : name := "Y".

(** X = 3, Y = 2 *)
Definition σ0 : Env :=
  fun x => if String.eqb x X then 3 else if String.eqb x Y then 2 else 0.

Example Asem_ex : 𝒜⟦(var X ⊕ var Y) ⊗ var X⟧ σ0 = 15.
Proof. reflexivity. Qed.

Example Bsem_ex : ℬ⟦¬ (var X == const 0)⟧ σ0 = true.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** * Part 2: Partiality with option *)

(** A PARTIAL function from D to E has no answer for some inputs.  A
    Rocq function must always return an answer, so we make "no answer"
    one of the possible answers.  The type [option E] has two kinds of
    values:

        Some e    an answer, e : E
        None      no answer

    A partial function from D to E is then a total function

        D → option E.

    (The notes write E⊥ for option E, and ⊥ for None.)

    For example, dividing by 0 has no answer: *)
Definition div (n m : Z) : option Z :=
  if Z.eqb m 0 then None else Some (n / m).

Example div_7_2 : div 7 2 = Some 3.
Proof. reflexivity. Qed.

Example div_7_0 : div 7 0 = None.
Proof. reflexivity. Qed.

(* ================================================================= *)
(** * Part 3: 𝒞⟦c⟧ and the base cases *)

(** Run a command c from σ.  Either it stops, in some environment σ',
    or it runs forever (like WHILE TRUE DO skip END).  So the meaning
    of c is a partial map from Env to Env:

        𝒞⟦c⟧ : Env → option Env

        𝒞⟦c⟧ σ = Some σ'    c, run from σ, stops in σ'
        𝒞⟦c⟧ σ = None       c, run from σ, runs forever

    The base cases:

        𝒞⟦skip⟧ σ                     = Some σ
        𝒞⟦x ::= a⟧ σ                  = Some σ[x ↦ 𝒜⟦a⟧ σ]
        𝒞⟦IF b THEN c0 ELSE c1 FI⟧ σ  = if ℬ⟦b⟧ σ then 𝒞⟦c0⟧ σ
                                                   else 𝒞⟦c1⟧ σ

    skip and := always stop, so they always give Some.  IF picks a
    branch and then does whatever that branch does: if the branch runs
    forever, so does the IF.

    So none of these ever gives None.  Only loops can run forever.  But
    loops are coming, and sequencing has to be ready for them.

 *)

(* ================================================================= *)
(** * Part 4: Sequencing *)

(** Take c1 ;; c2 ;; c3.  Each piece has a meaning

        𝒞⟦c1⟧ : Env → option Env
        𝒞⟦c2⟧ : Env → option Env
        𝒞⟦c3⟧ : Env → option Env

    and we want to put them together.  For ordinary functions we would
    just compose them: 𝒞⟦c2⟧ (𝒞⟦c1⟧ σ).  But that doesn't type-check:
    𝒞⟦c1⟧ σ is an [option Env], and 𝒞⟦c2⟧ wants an [Env].

    So look at the two cases for 𝒞⟦c1⟧ σ:

    - None: c1 runs forever.  There is no environment to run c2 on, so
      the whole program runs forever.  The answer is None.

    - Some σ1: c1 stopped in σ1, so run c2 from there: 𝒞⟦c2⟧ σ1.

    This case analysis is the Kleisli lift from lecture:

        f† : (D → E⊥) → (D⊥ → E⊥)
        f† None      = None
        f† (Some x)  = f x

    f only accepts an environment; f† also accepts None, and passes it
    on.  Sequencing, as in the notes:

        𝒞⟦c1 ;; c2⟧ σ = 𝒞⟦c2⟧† (𝒞⟦c1⟧ σ) *)
Definition lift {D E : Type} (f : D -> option E) : option D -> option E :=
  fun x =>
    match x with
    | None => None
    | Some y => f y
    end.

Notation "f †" := (lift f) (at level 5, format "f †").

(** For longer programs this nests inside out: c1 ;; c2 ;; c3 is
    𝒞⟦c3⟧† (𝒞⟦c2⟧† (𝒞⟦c1⟧ σ)), where c3 is written first but runs
    last.  So we give the environment in the middle a name.  Writing
    𝒞⟦c2⟧ as λσ'. 𝒞⟦c2⟧ σ' changes nothing:

        𝒞⟦c2⟧† (𝒞⟦c1⟧ σ)  =  (λσ'. 𝒞⟦c2⟧ σ')† (𝒞⟦c1⟧ σ)

    and we abbreviate the right-hand side as

        σ' ← 𝒞⟦c1⟧ σ ; 𝒞⟦c2⟧ σ'

    In general,   σ' ← m ; rest   means   (λσ'. rest)† m.

    Read it as: "run m.  If it stops, call the result σ' and go on with
    rest.  If it doesn't, neither does the whole thing."  The two
    equations for † become the two rules for computing with it:

        (σ' ← Some τ ; rest)  =  rest, with τ in place of σ'
        (σ' ← None ; rest)    =  None                                  *)
Notation "x ← m ; rest" := ((fun x => rest)† m)
  (at level 100, m at level 99, right associativity).

(** Here is all of 𝒞⟦·⟧.  The ;; line is the notes' 𝒞⟦c1⟧† (𝒞⟦c0⟧ σ),
    written with the arrow.  The WHILE line is a placeholder: for now
    every loop means None, which is the notes' first approximation
    W₀ = λσ. ⊥.  It gets replaced when we do while. *)
Fixpoint Csem (c : com) : Env -> option Env :=
  fun σ =>
    match c with
    | skip => Some σ
    | x ::= a => Some (upd σ x (𝒜⟦a⟧ σ))
    | IF b THEN c0 ELSE c1 FI => if ℬ⟦b⟧ σ then 𝒞⟦c0⟧ σ else 𝒞⟦c1⟧ σ
    | c0 ;; c1 => σ' ← 𝒞⟦c0⟧ σ ; 𝒞⟦c1⟧ σ'
    | WHILE b DO c0 END => None
    end
where "𝒞⟦ c ⟧" := (Csem c).

(** *** A three-command program *)

(** Max x y r compares x and y, and stores the larger one in r. *)
Definition Max (x y r : name) : com :=
  IF var x ≤ var y THEN r ::= var y ELSE r ::= var x FI.

(** Its denotation, by the IF and := lines of 𝒞⟦·⟧:

        𝒞⟦Max x y r⟧ σ = if σ(x) ≤ σ(y) then Some σ[r ↦ σ(y)]
                                         else Some σ[r ↦ σ(x)]         *)
Example Max_den x y r σ :
  𝒞⟦Max x y r⟧ σ
  = if Z.leb (σ x) (σ y) then Some (upd σ r (σ y)) else Some (upd σ r (σ x)).
Proof. reflexivity. Qed.

Definition R : name := "R".

Definition c1 : com := X ::= const 3.
Definition c2 : com := Y ::= const 4.
Definition c3 : com := Max X Y R.

(** We start with every variable at 0. *)
Definition σ_start : Env := fun _ => 0.

(** Using the sequencing line twice, the meaning of c1 ;; c2 ;; c3 is

        σ1 ← 𝒞⟦c1⟧ σ_start ;
        σ2 ← 𝒞⟦c2⟧ σ1 ;
        σ3 ← 𝒞⟦c3⟧ σ2 ;
        Some σ3

    (The last two lines could just be 𝒞⟦c3⟧ σ2: running c3 and then
    stopping where it stopped is the same as running c3.)

    To compute it, we only need the two rules for the arrow:

        (σ' ← Some τ ; rest)  =  rest, with τ in place of σ'
        (σ' ← None ; rest)    =  None

    Write τ1 = σ_start[X ↦ 3],  τ2 = τ1[Y ↦ 4],  τ3 = τ2[R ↦ 4].

        𝒞⟦c1 ;; c2 ;; c3⟧ σ_start

      = σ1 ← 𝒞⟦X ::= const 3⟧ σ_start ;        sequencing line twice,
        σ2 ← 𝒞⟦Y ::= const 4⟧ σ1 ;             then c1, c2, c3
        σ3 ← 𝒞⟦Max X Y R⟧ σ2 ;                 filled in
        Some σ3

      = σ1 ← Some τ1 ;                         := line
        σ2 ← 𝒞⟦Y ::= const 4⟧ σ1 ;
        σ3 ← 𝒞⟦Max X Y R⟧ σ2 ;
        Some σ3

      = σ2 ← 𝒞⟦Y ::= const 4⟧ τ1 ;             arrow on Some τ1
        σ3 ← 𝒞⟦Max X Y R⟧ σ2 ;
        Some σ3

      = σ2 ← Some τ2 ;                         := line
        σ3 ← 𝒞⟦Max X Y R⟧ σ2 ;
        Some σ3

      = σ3 ← 𝒞⟦Max X Y R⟧ τ2 ;                 arrow on Some τ2
        Some σ3

      = σ3 ← Some τ3 ;                         Max_den: τ2(X) = 3 ≤ 4 = τ2(Y)
        Some σ3

      = Some τ3                                arrow on Some τ3

    The environments:
                                                        X   Y   R
        σ_start                                         0   0   0
        τ1 = σ_start[X ↦ 3]                             3   0   0
        τ2 = τ1[Y ↦ 4]                                  3   4   0
        τ3 = τ2[R ↦ 4]        (3 ≤ 4, so R gets Y)      3   4   4   *)
Example seq3 :
  𝒞⟦c1 ;; c2 ;; c3⟧ σ_start
  = (σ1 ← 𝒞⟦c1⟧ σ_start ;
     σ2 ← 𝒞⟦c2⟧ σ1 ;
     σ3 ← 𝒞⟦c3⟧ σ2 ;
     Some σ3).
Proof. reflexivity. Qed.

Example seq3_value :
  𝒞⟦c1 ;; c2 ;; c3⟧ σ_start
  = Some (upd (upd (upd σ_start X 3) Y 4) R 4).
Proof. reflexivity. Qed.

(** Now make c2 a loop that never stops.  𝒞⟦c2_loop⟧ σ1 is None, so
    the arrow stops right there, and Max never runs:

        σ1 ← 𝒞⟦c1⟧ σ_start ;      Some σ1
        σ2 ← 𝒞⟦c2_loop⟧ σ1 ;      None: stop
        σ3 ← 𝒞⟦c3⟧ σ2 ;           (never reached)
        Some σ3

    (𝒞⟦c2_loop⟧ is None for every σ.  That stays true once while has
    its real meaning.) *)
Definition c2_loop : com := WHILE TRUE DO Y ::= const 4 END.

Example seq3_loop : 𝒞⟦c1 ;; c2_loop ;; c3⟧ σ_start = None.
Proof. reflexivity. Qed.

(** *** while: the approximations 𝒲ₙ

    For a loop WHILE b DO c END, the notes define approximations
    𝒲ₙ(b, c, σ):

        𝒲₀(b, c, σ)    = None
        𝒲ₙ₊₁(b, c, σ)  = if ℬ⟦b⟧ σ then (σ' ← 𝒞⟦c⟧ σ ; 𝒲ₙ(b, c, σ'))
                                     else Some σ

    Think of 𝒲ₙ as the loop with a timeout.  It gives the loop's answer
    if the loop stops within n tests of b (so at most n − 1 trips
    through the body), and None otherwise.  (The notes write
    𝒲ₙ₊₁ = F 𝒲ₙ.)

    The meaning of the loop is the limit of 𝒲₀, 𝒲₁, 𝒲₂, ...  For each
    starting σ, exactly one of two things happens:

      - ∃n. 𝒲ₙ(b, c, σ) = Some τ.  Then 𝒲ₘ(b, c, σ) = Some τ for every
        m ≥ n (a longer timeout replays the same run), and

            𝒞⟦WHILE b DO c END⟧ σ = Some τ.

      - ∀n. 𝒲ₙ(b, c, σ) = None.  No timeout is long enough: the loop
        runs forever, and

            𝒞⟦WHILE b DO c END⟧ σ = None.

    Since an answer never changes once it appears, this limit is well
    defined; the notes call it the least upper bound of the 𝒲ₙ.

    The ordering behind this.  On answers, Env⊥ = option Env, the notes
    use the flat order ("knows at most as much as"):

        None ⊑ v                  for every v
        Some τ ⊑ Some τ'   ⟺   τ = τ'

    so None is below everything, and two different answers are
    unrelated.  On meanings, Env → option Env, the order is pointwise:

        f ⊑ g   :⟺   ∀σ. f σ ⊑ g σ
                 ⟺   ∀σ τ. f σ = Some τ  ⟹  g σ = Some τ

    i.e. g answers wherever f does, with the same answer.  (Seen as sets
    of pairs (σ, τ), this is just ⊆; compare §4 of the notes.)  Then:

      - 𝒲₀ = λσ. None is the least element:  𝒲₀ ⊑ f  for every f.

      - With  F w = λσ. if ℬ⟦b⟧ σ then (σ' ← 𝒞⟦c⟧ σ ; w σ') else Some σ,
        we have 𝒲ₙ₊₁ = F 𝒲ₙ, and F is monotone (f ⊑ g ⟹ F f ⊑ F g), so

            𝒲₀ ⊑ 𝒲₁ ⊑ 𝒲₂ ⊑ ⋯         (a chain).

      - Least upper bounds of chains are taken pointwise:

            (⊔ₙ 𝒲ₙ) σ  =  Some τ   if ∃n. 𝒲ₙ σ = Some τ
                           None     if ∀n. 𝒲ₙ σ = None

        which is exactly the two cases above.

      - Every chain in Env → option Env has a least upper bound (it is a
        chain-complete partial order, a CPO), and F is continuous:
        F (⊔ₙ wₙ) = ⊔ₙ F wₙ.  These are the two facts the notes need to
        extend their fixed-point theorem from ⊆ to CPOs.  It gives

            𝒞⟦WHILE b DO c END⟧  =  ⊔ₙ 𝒲ₙ  =  fix F,

        the LEAST solution of W = F W.

    In Rocq, W takes the MEANINGS bb = ℬ⟦b⟧ and cc = 𝒞⟦c⟧ instead of b
    and c, so that the WHILE line of 𝒞⟦·⟧ can use it later.  We write
    𝒲 n (b, c, σ) for W ℬ⟦b⟧ 𝒞⟦c⟧ n σ. *)
Fixpoint W (bb : Env -> bool) (cc : Env -> option Env) (n : nat)
  : Env -> option Env :=
  match n with
  | O => fun σ => None
  | S n' => fun σ => if bb σ then (σ' ← cc σ ; W bb cc n' σ') else Some σ
  end.

Notation "'𝒲' n ( b , c , σ )" := (W (ℬ⟦b⟧) (𝒞⟦c⟧) n σ)
  (at level 10, n at level 0, b at level 99, c at level 99, σ at level 99).

(** *** 𝒲ₙ on an example

    The loop

        WHILE ¬ (var X == const 2) DO X ::= var X ⊕ const 1 END

    counts X up until it hits 2.

    Write ρₖ for σ_X0 with X set to k, so the body takes ρₖ to ρₖ₊₁:
    𝒞⟦X ::= var X ⊕ const 1⟧ ρₖ = Some ρₖ₊₁.  Unfolding 𝒲₃ from ρ₀:

        𝒲₃(b, c, ρ₀)
      = if ℬ⟦b⟧ ρ₀ then (σ' ← 𝒞⟦c⟧ ρ₀ ; 𝒲₂(b, c, σ')) else Some ρ₀
      = σ' ← Some ρ₁ ; 𝒲₂(b, c, σ')         X = 0 ≠ 2: test true, run c
      = 𝒲₂(b, c, ρ₁)                        arrow on Some ρ₁
      = 𝒲₁(b, c, ρ₂)                        X = 1 ≠ 2: the same two steps
      = Some ρ₂                             X = 2: test false, stop

    One step less runs out of time just before the last test:

        𝒲₂(b, c, ρ₀) = 𝒲₁(b, c, ρ₁) = 𝒲₀(b, c, ρ₂) = None

    Started with X = 0, it tests X = 2 three times (X = 0, 1, 2) and
    goes through the body twice.  So the answer first appears at 𝒲₃,
    and after that it never changes:

        n                 0     1     2     3        4        5        6
        final X (𝒲ₙ σ)   None  None  None  Some 2   Some 2   Some 2   Some 2

    Started with X = 5, it counts 5, 6, 7, ... and never hits 2.  Every
    𝒲ₙ gives None: no timeout is long enough. *)
Definition loop_b : bexp := ¬ (var X == const 2).
Definition loop_c : com := X ::= var X ⊕ const 1.

Definition σ_X0 : Env := fun _ => 0.
Definition σ_X5 : Env := fun x => if String.eqb x X then 5 else 0.

(** The value of x at the end, or None if there is no end. *)
Definition final (x : name) (r : option Env) : option Z :=
  match r with
  | None => None
  | Some σ => Some (σ x)
  end.

(** The unfolding, checked: *)
Example W3_step :
  𝒲 3 (loop_b, loop_c, σ_X0) = 𝒲 2 (loop_b, loop_c, upd σ_X0 X 1).
Proof. reflexivity. Qed.

Example W2_none : 𝒲 2 (loop_b, loop_c, σ_X0) = None.
Proof. reflexivity. Qed.

Example from_0 :
  map (fun n => final X (𝒲 n (loop_b, loop_c, σ_X0))) [0; 1; 2; 3; 4; 5; 6]%nat
  = [None; None; None; Some 2; Some 2; Some 2; Some 2].
Proof. reflexivity. Qed.

Example from_5 :
  map (fun n => final X (𝒲 n (loop_b, loop_c, σ_X5))) [0; 1; 2; 3; 4; 5; 6]%nat
  = [None; None; None; None; None; None; None].
Proof. reflexivity. Qed.

(* ================================================================= *)
(** * Part 5: Equational reasoning *)

(** Meanings are functions, so "same meaning" is an equation, and we
    can reason about programs by calculation, as in algebra.  There are
    three layers: expressions, commands without loops, and loops. *)

(** *** Expressions: plain algebra *)

(**     a ≡_a a'  :⟺  ∀σ. 𝒜⟦a⟧ σ = 𝒜⟦a'⟧ σ
        b ≡_b b'  :⟺  ∀σ. ℬ⟦b⟧ σ = ℬ⟦b'⟧ σ
    𝒜 and ℬ are total, so we get the usual laws of ℤ and of booleans:
        a ⊕ const 0 ≡_a a          a0 ⊕ a1 ≡_a a1 ⊕ a0          a ⊗ const 1 ≡_a a
        ¬ ¬ b ≡_b b                ¬ (b0 ∧ b1) ≡_b ¬ b0 ∨ ¬ b1    a == a ≡_b TRUE
    Constant folding lives here:  cfold : AExp → AExp,
    cfold(Y ⊕ (const 2 ⊗ const 3)) = Y ⊕ const 6,  and  ∀a. cfold a ≡_a a
    (induction on a). *)

(** *** Commands without loops: algebra with partiality *)

(**     c ≡ c'  :⟺  ∀σ. 𝒞⟦c⟧ σ = 𝒞⟦c'⟧ σ    (both run forever, or both
                                              stop in the same environment)
    Expression laws carry over:
        a ≡_a a'  ⟹  x ::= a ≡ x ::= a'          (e.g. x ::= a ≡ x ::= cfold a)
        b ≡_b b'  ⟹  IF b THEN c0 ELSE c1 FI ≡ IF b' THEN c0 ELSE c1 FI
    Laws (unfold 𝒞⟦·⟧, case on ℬ⟦b⟧ σ or on 𝒞⟦c0⟧ σ = Some _ / None):
        IF TRUE THEN c0 ELSE c1 FI                ≡  c0
        skip ;; c                                 ≡  c
        c ;; skip                                 ≡  c
        (c0 ;; c1) ;; c2                          ≡  c0 ;; (c1 ;; c2)
        IF b THEN c ELSE c FI                     ≡  c
        IF ¬ b THEN c0 ELSE c1 FI                 ≡  IF b THEN c1 ELSE c0 FI
        IF b THEN (c0 ;; c) ELSE (c1 ;; c) FI     ≡  (IF b THEN c0 ELSE c1 FI) ;; c
    Congruence (𝒞⟦c0 ;; c1⟧ and 𝒞⟦IF b THEN c0 ELSE c1 FI⟧ only use
    ℬ⟦b⟧, 𝒞⟦c0⟧, 𝒞⟦c1⟧):
        c0 ≡ c0'             ⟹   c0 ;; c1 ≡ c0' ;; c1
        c1 ≡ c1'             ⟹   c0 ;; c1 ≡ c0 ;; c1'
        c0 ≡ c0', c1 ≡ c1'   ⟹   IF b THEN c0 ELSE c1 FI ≡ IF b THEN c0' ELSE c1' FI
    So we can calculate, and each step is a rewrite a compiler may use:
          X ::= 3 ;; IF TRUE THEN (skip ;; Y ::= 4) ELSE skip FI
        ≡ X ::= 3 ;; (skip ;; Y ::= 4)          IF TRUE law, inside ;;
        ≡ X ::= 3 ;; Y ::= 4                    skip ;; c ≡ c, inside ;; *)

(** *** Loops: equations plus induction *)

(** With 𝒞⟦WHILE b DO c END⟧ σ = the limit of 𝒲ₙ(b, c, σ), some
    equations still hold:
        WHILE b DO c END  ≡  IF b THEN (c ;; WHILE b DO c END) ELSE skip FI
                                                   (the limit is a fixed point)
        WHILE FALSE DO c END  ≡  skip
        c ≡ c'  ⟹  WHILE b DO c END ≡ WHILE b DO c' END
                                                   (𝒲ₙ only uses 𝒞⟦c⟧)
    But equations alone cannot pin a loop down.  For WHILE TRUE DO skip
    END the unrolling equation says  W σ = W σ,  which every W
    satisfies.  To show what a loop does, we need induction: on n (the
    𝒲ₙ), or on the data (P1 ≡ P2 below needs induction on σ(X)). *)

(** *** What ≡ does not tell us *)

(** (1) Too strict:  R ::= (X ⊕ Y) ⊗ (X ⊕ Y)  ≢  T ::= X ⊕ Y ;; R ::= T ⊗ T,
        although both give the same R; they differ at T.
    (2) A fact about the model: it says something about runs only if
        ⟨c, σ⟩ ⇓ τ ⟺ 𝒞⟦c⟧ σ = Some τ (Theorem 1 in the notes; not proved
        here), and cfold is correct in ℤ, not in 64-bit arithmetic.
    (3) Language-specific: IF b THEN c ELSE c ≡ c needs ℬ⟦b⟧ σ to always
        finish and to leave σ alone.
    (4) No running time: see below. *)

(* ================================================================= *)
(** * Denotations forget running time *)

(**     P1 = IF 1 ≤ X THEN X ::= 0 ELSE skip FI
        P2 = WHILE 1 ≤ X DO X ::= X ⊖ 1 END
        𝒞⟦P1⟧ = 𝒞⟦P2⟧ = λσ. if 1 ≤ σ(X) then Some σ[X ↦ 0] else Some σ
    So P1 ≡ P2, but P1 takes one step and P2 takes σ(X) trips through
    its loop. *)
