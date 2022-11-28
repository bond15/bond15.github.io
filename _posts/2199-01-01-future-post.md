---
title: 'Deriving Function Extensionality in Cubical Agda'
date: 2022-11-27
permalink: /posts/2022/11/27/FunExtCubicalAgda/
tags:
---

<script type="text/javascript" id="MathJax-script" async
  src="https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-mml-chtml.js">
</script>

<script type="text/javascript" id="MathJax-script" async
  src="https://cdnjs.cloudflare.com/ajax/libs/mathjax/3.0.0/es5/latest?tex-mml-chtml.js">
</script>

Function extensionality is not derivable in Agda or Coq. It can be postulated as an axiom that is consistent with the theory, but you cannot construct a term for the type representing function extensionality.

In Cubical Agda it is derivable and it has a tauntingly concise definition. (removing Level for a moment since that is tangental)
```
funext : {A B : Set}{f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g
funext p i a = p a i
```
That said, there is a fair amount to unpack to understand what is going on here.

Cubical Agda adds an abstract Interval Type `I` which has two endpoints `i0` and `i1`.   (see footnote [1])

Equality in Cubical Agda is represented by Path Types. 
```
_≡_ : {A : Set} -> A -> A -> Set 
_≡_ {A} x y = Path A x y
```
read as ... `x` and `y` are equal elements of `A` when there is a `Path` in `A` from `x` to `y`.
A Path is constructed by abstracting over an abstract interval `I` and saying where each endpoint (`i0` and `i1`) maps to.  (subject to some constraints)
Here is a concrete example.
```
data Bool : Set where 
      true : Bool 
      false : Bool

true-eq-true : Path Bool true true
true-eq-true =  λ i -> true
```
This says we have a `Path` in `Bool` between elements `true` and `true` (Aka `true ≡ true`).

We construct this path by abstracting over an interval `i` and setting both endpoints `i0` and `i1` to `true`.

Paths can be sampled at their endpoints using a syntax similar to function application.

for instance given `p : a ≡ b`. 

I can sample the left endpoint by applying `p` to `i0`  so `p i0 := a`

I can sample the right endpoint by applying `p` to `i1` so `p i1 := b`

Now back to funext
```
funext : {A B : Set}{f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g
funext = ?
```
First take in the argument `p` of type `(∀ (a : A) → f a ≡ g a) ` from the hypothesis.
```
funext : {A B : Set}{f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g
funext p = ?
```
then the goal is `f ≡ g`. 

We have to construct a Path (in `A -> B`)from `f` to `g`, so we have to abstract over an inverval `i : I`
```
funext : {A B : Set}{f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g
funext p i = ?
```
Since we are defining a path in the function space `A -> B`,  the endpoints `i0` and `i1` each need to map to something of type `A -> B`. 
So we can start by abstracting over `a : A`
```
funext : {A B : Set}{f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g
funext p i a = ?
```
Our goal is now to construct an element of `B`.

Using `p : ∀ (a : A) → f a ≡ g a) ` and `a : A` we can get a path `f a ≡ g a`.

`p a : f a ≡ g a` is a path from `f a` to `g a` both of which have type `B`.  

Paths can be sampled at their endpoints so we apply `p a` to `i` and get an element of `B`
```
funext : {A B : Set}{f g : A → B} → (∀ (a : A) → f a ≡ g a) → f ≡ g
funext p i a = p a i
```
To see what is happening here let's consider what happens at each endpoint of the interval.

When `i := i0`, `p a i0 := f a` 

when `i := i1`, `p a i1 := g a`

Foot notes:
[1]

Cubical agda internalizes the higher inductive type `I` into the type theory.
```
data I : Set where 
       i0 : I 
       i1 : I 
       eq : i0 ≡ i1
```
So the `eq` condition must be obeyed when constructing paths that is to say that the endpoints must be definitionally equal.

more details can be found here: https://agda.readthedocs.io/en/v2.6.2.1/language/cubical.html