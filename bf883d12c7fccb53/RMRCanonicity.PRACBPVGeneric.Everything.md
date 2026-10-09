---
title: "PRACBPVGeneric"
layout: agda
permalink: /bf883d12c7fccb53/RMRCanonicity.PRACBPVGeneric.Everything.html
sitemap: false
---
{% raw %}
<link rel="stylesheet" href="Agda.css">

# PRACBPVGeneric: world-indexed CBPV over a mode theory of locks

This is an Agda formalization of call-by-push-value over a category of worlds `W`, with lock telescopes and lock modalities `[ κ ]` given by a lock signature, algebraic operations given by an operation signature, and a theory of equations over them. It has a denotational semantics in presheaves on `W`, tree reduction (sound, deterministic, strongly normalizing), an equational theory with its soundness and canonical forms, and a configuration machine that is generic in any right module of the free-model monad, with soundness, and strong and weak normalization when the module is affine. It has no postulates, holes or termination pragmas. It is checked with the flags of the library file `proto.agda-lib` (`--cubical --guarded --guardedness --rewriting --postfix-projections`), not with `--safe`: `--rewriting` is on in the library file, although no module declares a rewrite rule.

The guiding standard is the POPL'27 formalization (the separate clone `cbpv-popl-formalization`, `agda/src/POPL`), which is the special case `W = 1` with no locks. [POPL formalization → PRACBPVGeneric](#popl-formalization--pracbpvgeneric) gives, for each of its results, the counterpart here or says that there is none. [Beyond the POPL formalization](#beyond-the-popl-formalization) lists what has no counterpart there, and [Deviations and limits](#deviations-and-limits) lists every difference and every open problem.

This page is the literate Agda module `RMRCanonicity.PRACBPVGeneric.Everything`. It imports every module of the development, and every name in the tables links to its definition.

<pre class="Agda"><a id="1705" class="Keyword">module</a> <a id="1712" href="RMRCanonicity.PRACBPVGeneric.Everything.html" class="Module">RMRCanonicity.PRACBPVGeneric.Everything</a> <a id="1752" class="Keyword">where</a>

<a id="1759" class="Keyword">import</a> <a id="1766" href="RMRCanonicity.PRACBPVGeneric.Closing.html" class="Module">RMRCanonicity.PRACBPVGeneric.Closing</a>
<a id="1803" class="Keyword">import</a> <a id="1810" href="RMRCanonicity.PRACBPVGeneric.Fam.html" class="Module">RMRCanonicity.PRACBPVGeneric.Fam</a>
<a id="1843" class="Keyword">import</a> <a id="1850" href="RMRCanonicity.PRACBPVGeneric.FinCount.html" class="Module">RMRCanonicity.PRACBPVGeneric.FinCount</a>
<a id="1888" class="Keyword">import</a> <a id="1895" href="RMRCanonicity.PRACBPVGeneric.FinMax.html" class="Module">RMRCanonicity.PRACBPVGeneric.FinMax</a>
<a id="1931" class="Keyword">import</a> <a id="1938" href="RMRCanonicity.PRACBPVGeneric.FinSum.html" class="Module">RMRCanonicity.PRACBPVGeneric.FinSum</a>
<a id="1974" class="Keyword">import</a> <a id="1981" href="RMRCanonicity.PRACBPVGeneric.Instances.Constant.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Constant</a>
<a id="2029" class="Keyword">import</a> <a id="2036" href="RMRCanonicity.PRACBPVGeneric.Instances.Equational.Common.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Equational.Common</a>
<a id="2093" class="Keyword">import</a> <a id="2100" href="RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors</a>
<a id="2157" class="Keyword">import</a> <a id="2164" href="RMRCanonicity.PRACBPVGeneric.Instances.Equational.Everything.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Equational.Everything</a>
<a id="2225" class="Keyword">import</a> <a id="2232" href="RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Equational.State</a>
<a id="2288" class="Keyword">import</a> <a id="2295" href="RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid</a>
<a id="2360" class="Keyword">import</a> <a id="2367" href="RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer</a>
<a id="2424" class="Keyword">import</a> <a id="2431" href="RMRCanonicity.PRACBPVGeneric.Instances.Guarded.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Guarded</a>
<a id="2478" class="Keyword">import</a> <a id="2485" href="RMRCanonicity.PRACBPVGeneric.Instances.LocalState.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.LocalState</a>
<a id="2535" class="Keyword">import</a> <a id="2542" href="RMRCanonicity.PRACBPVGeneric.Instances.Machines.Error.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Machines.Error</a>
<a id="2596" class="Keyword">import</a> <a id="2603" href="RMRCanonicity.PRACBPVGeneric.Instances.Machines.Everything.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Machines.Everything</a>
<a id="2662" class="Keyword">import</a> <a id="2669" href="RMRCanonicity.PRACBPVGeneric.Instances.Machines.GlobalState.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Machines.GlobalState</a>
<a id="2729" class="Keyword">import</a> <a id="2736" href="RMRCanonicity.PRACBPVGeneric.Instances.Machines.Guarded.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Machines.Guarded</a>
<a id="2792" class="Keyword">import</a> <a id="2799" href="RMRCanonicity.PRACBPVGeneric.Instances.Machines.LocalState.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Machines.LocalState</a>
<a id="2858" class="Keyword">import</a> <a id="2865" href="RMRCanonicity.PRACBPVGeneric.Instances.Normalization.Error.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Normalization.Error</a>
<a id="2924" class="Keyword">import</a> <a id="2931" href="RMRCanonicity.PRACBPVGeneric.Instances.Normalization.Everything.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Normalization.Everything</a>
<a id="2995" class="Keyword">import</a> <a id="3002" href="RMRCanonicity.PRACBPVGeneric.Instances.Normalization.GlobalState.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Normalization.GlobalState</a>
<a id="3067" class="Keyword">import</a> <a id="3074" href="RMRCanonicity.PRACBPVGeneric.Instances.Normalization.Guarded.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Normalization.Guarded</a>
<a id="3135" class="Keyword">import</a> <a id="3142" href="RMRCanonicity.PRACBPVGeneric.Instances.Normalization.LocalState.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Normalization.LocalState</a>
<a id="3206" class="Keyword">import</a> <a id="3213" href="RMRCanonicity.PRACBPVGeneric.Instances.Polynomials.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.Polynomials</a>
<a id="3264" class="Keyword">import</a> <a id="3271" href="RMRCanonicity.PRACBPVGeneric.Instances.SelfModule.Error.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.SelfModule.Error</a>
<a id="3327" class="Keyword">import</a> <a id="3334" href="RMRCanonicity.PRACBPVGeneric.Instances.SelfModule.Everything.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.SelfModule.Everything</a>
<a id="3395" class="Keyword">import</a> <a id="3402" href="RMRCanonicity.PRACBPVGeneric.Instances.SelfModule.List.html" class="Module">RMRCanonicity.PRACBPVGeneric.Instances.SelfModule.List</a>
<a id="3457" class="Keyword">import</a> <a id="3464" href="RMRCanonicity.PRACBPVGeneric.Metatheory.Chain.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.Chain</a>
<a id="3510" class="Keyword">import</a> <a id="3517" href="RMRCanonicity.PRACBPVGeneric.Metatheory.ClosedLaws.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.ClosedLaws</a>
<a id="3568" class="Keyword">import</a> <a id="3575" href="RMRCanonicity.PRACBPVGeneric.Metatheory.Determinism.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.Determinism</a>
<a id="3627" class="Keyword">import</a> <a id="3634" href="RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation</a>
<a id="3692" class="Keyword">import</a> <a id="3699" href="RMRCanonicity.PRACBPVGeneric.Metatheory.EqSubstitution.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.EqSubstitution</a>
<a id="3754" class="Keyword">import</a> <a id="3761" href="RMRCanonicity.PRACBPVGeneric.Metatheory.Equational.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.Equational</a>
<a id="3812" class="Keyword">import</a> <a id="3819" href="RMRCanonicity.PRACBPVGeneric.Metatheory.Everything.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.Everything</a>
<a id="3870" class="Keyword">import</a> <a id="3877" href="RMRCanonicity.PRACBPVGeneric.Metatheory.Fundamental.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.Fundamental</a>
<a id="3929" class="Keyword">import</a> <a id="3936" href="RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation</a>
<a id="3992" class="Keyword">import</a> <a id="3999" href="RMRCanonicity.PRACBPVGeneric.Metatheory.Renaming.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.Renaming</a>
<a id="4048" class="Keyword">import</a> <a id="4055" href="RMRCanonicity.PRACBPVGeneric.Metatheory.SubstReduction.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.SubstReduction</a>
<a id="4110" class="Keyword">import</a> <a id="4117" href="RMRCanonicity.PRACBPVGeneric.Metatheory.Substitution.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.Substitution</a>
<a id="4170" class="Keyword">import</a> <a id="4177" href="RMRCanonicity.PRACBPVGeneric.Metatheory.Termination.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.Termination</a>
<a id="4229" class="Keyword">import</a> <a id="4236" href="RMRCanonicity.PRACBPVGeneric.Metatheory.TermsSet.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.TermsSet</a>
<a id="4285" class="Keyword">import</a> <a id="4292" href="RMRCanonicity.PRACBPVGeneric.Metatheory.TreeNormalization.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.TreeNormalization</a>
<a id="4350" class="Keyword">import</a> <a id="4357" href="RMRCanonicity.PRACBPVGeneric.Metatheory.TreeSize.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.TreeSize</a>
<a id="4406" class="Keyword">import</a> <a id="4413" href="RMRCanonicity.PRACBPVGeneric.Metatheory.TypesSet.html" class="Module">RMRCanonicity.PRACBPVGeneric.Metatheory.TypesSet</a>
<a id="4462" class="Keyword">import</a> <a id="4469" href="RMRCanonicity.PRACBPVGeneric.Multiset.html" class="Module">RMRCanonicity.PRACBPVGeneric.Multiset</a>
<a id="4507" class="Keyword">import</a> <a id="4514" href="RMRCanonicity.PRACBPVGeneric.Polynomial.html" class="Module">RMRCanonicity.PRACBPVGeneric.Polynomial</a>
<a id="4554" class="Keyword">import</a> <a id="4561" href="RMRCanonicity.PRACBPVGeneric.Properties.html" class="Module">RMRCanonicity.PRACBPVGeneric.Properties</a>
<a id="4601" class="Keyword">import</a> <a id="4608" href="RMRCanonicity.PRACBPVGeneric.Reduction.html" class="Module">RMRCanonicity.PRACBPVGeneric.Reduction</a>
<a id="4647" class="Keyword">import</a> <a id="4654" href="RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Affinity</a>
<a id="4702" class="Keyword">import</a> <a id="4709" href="RMRCanonicity.PRACBPVGeneric.Semantics.Algebra.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Algebra</a>
<a id="4756" class="Keyword">import</a> <a id="4763" href="RMRCanonicity.PRACBPVGeneric.Semantics.Branching.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Branching</a>
<a id="4812" class="Keyword">import</a> <a id="4819" href="RMRCanonicity.PRACBPVGeneric.Semantics.Closed.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Closed</a>
<a id="4865" class="Keyword">import</a> <a id="4872" href="RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity</a>
<a id="4928" class="Keyword">import</a> <a id="4935" href="RMRCanonicity.PRACBPVGeneric.Semantics.Denotation.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Denotation</a>
<a id="4985" class="Keyword">import</a> <a id="4992" href="RMRCanonicity.PRACBPVGeneric.Semantics.EqCanonicity.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.EqCanonicity</a>
<a id="5044" class="Keyword">import</a> <a id="5051" href="RMRCanonicity.PRACBPVGeneric.Semantics.EquationalSoundness.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.EquationalSoundness</a>
<a id="5110" class="Keyword">import</a> <a id="5117" href="RMRCanonicity.PRACBPVGeneric.Semantics.Everything.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Everything</a>
<a id="5167" class="Keyword">import</a> <a id="5174" href="RMRCanonicity.PRACBPVGeneric.Semantics.Free.Closed.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Free.Closed</a>
<a id="5225" class="Keyword">import</a> <a id="5232" href="RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison</a>
<a id="5287" class="Keyword">import</a> <a id="5294" href="RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation</a>
<a id="5349" class="Keyword">import</a> <a id="5356" href="RMRCanonicity.PRACBPVGeneric.Semantics.Free.Renaming.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Free.Renaming</a>
<a id="5409" class="Keyword">import</a> <a id="5416" href="RMRCanonicity.PRACBPVGeneric.Semantics.Free.Soundness.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Free.Soundness</a>
<a id="5470" class="Keyword">import</a> <a id="5477" href="RMRCanonicity.PRACBPVGeneric.Semantics.Free.Substitution.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Free.Substitution</a>
<a id="5534" class="Keyword">import</a> <a id="5541" href="RMRCanonicity.PRACBPVGeneric.Semantics.FreeModel.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.FreeModel</a>
<a id="5590" class="Keyword">import</a> <a id="5597" href="RMRCanonicity.PRACBPVGeneric.Semantics.Ground.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Ground</a>
<a id="5643" class="Keyword">import</a> <a id="5650" href="RMRCanonicity.PRACBPVGeneric.Semantics.GuardedLock.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.GuardedLock</a>
<a id="5701" class="Keyword">import</a> <a id="5708" href="RMRCanonicity.PRACBPVGeneric.Semantics.Lock.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Lock</a>
<a id="5752" class="Keyword">import</a> <a id="5759" href="RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Machine</a>
<a id="5806" class="Keyword">import</a> <a id="5813" href="RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Normalization</a>
<a id="5866" class="Keyword">import</a> <a id="5873" href="RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine</a>
<a id="5924" class="Keyword">import</a> <a id="5931" href="RMRCanonicity.PRACBPVGeneric.Semantics.PolySelfModule.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.PolySelfModule</a>
<a id="5985" class="Keyword">import</a> <a id="5992" href="RMRCanonicity.PRACBPVGeneric.Semantics.Presheaf.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Presheaf</a>
<a id="6040" class="Keyword">import</a> <a id="6047" href="RMRCanonicity.PRACBPVGeneric.Semantics.Renaming.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Renaming</a>
<a id="6095" class="Keyword">import</a> <a id="6102" href="RMRCanonicity.PRACBPVGeneric.Semantics.RunMachine.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.RunMachine</a>
<a id="6152" class="Keyword">import</a> <a id="6159" href="RMRCanonicity.PRACBPVGeneric.Semantics.RunNormalization.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.RunNormalization</a>
<a id="6215" class="Keyword">import</a> <a id="6222" href="RMRCanonicity.PRACBPVGeneric.Semantics.Runner.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Runner</a>
<a id="6268" class="Keyword">import</a> <a id="6275" href="RMRCanonicity.PRACBPVGeneric.Semantics.RunnerAffine.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.RunnerAffine</a>
<a id="6327" class="Keyword">import</a> <a id="6334" href="RMRCanonicity.PRACBPVGeneric.Semantics.SelfCanonicity.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.SelfCanonicity</a>
<a id="6388" class="Keyword">import</a> <a id="6395" href="RMRCanonicity.PRACBPVGeneric.Semantics.SelfMachine.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.SelfMachine</a>
<a id="6446" class="Keyword">import</a> <a id="6453" href="RMRCanonicity.PRACBPVGeneric.Semantics.SelfModule.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.SelfModule</a>
<a id="6503" class="Keyword">import</a> <a id="6510" href="RMRCanonicity.PRACBPVGeneric.Semantics.Soundness.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Soundness</a>
<a id="6559" class="Keyword">import</a> <a id="6566" href="RMRCanonicity.PRACBPVGeneric.Semantics.StrongTheory.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.StrongTheory</a>
<a id="6618" class="Keyword">import</a> <a id="6625" href="RMRCanonicity.PRACBPVGeneric.Semantics.Substitution.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.Substitution</a>
<a id="6677" class="Keyword">import</a> <a id="6684" href="RMRCanonicity.PRACBPVGeneric.Semantics.TreeCanonicity.html" class="Module">RMRCanonicity.PRACBPVGeneric.Semantics.TreeCanonicity</a>
<a id="6738" class="Keyword">import</a> <a id="6745" href="RMRCanonicity.PRACBPVGeneric.Signature.html" class="Module">RMRCanonicity.PRACBPVGeneric.Signature</a>
<a id="6784" class="Keyword">import</a> <a id="6791" href="RMRCanonicity.PRACBPVGeneric.Syntax.html" class="Module">RMRCanonicity.PRACBPVGeneric.Syntax</a>
<a id="6827" class="Keyword">import</a> <a id="6834" href="RMRCanonicity.PRACBPVGeneric.Types.html" class="Module">RMRCanonicity.PRACBPVGeneric.Types</a>
</pre>
## Build

The development depends on the libraries `cubical`, `cubical-categorical-logic`, `polynomial` (modules `Polynomial.*`) and `right-module-reduction` (modules `RightModuleReduction.*`, abbreviated RMR below). It imports nothing else from the `RMRCanonicity` tree. The file `libraries`, in the library root (the directory that holds `RMRCanonicity/`), lists the paths to their `.agda-lib` files. From the library root:

```bash
timeout 600 agda --library-file=libraries RMRCanonicity/PRACBPVGeneric/Everything.lagda.md +RTS -M6G -RTS
```

On 2026-10-08, after the POPL instances were added (parity stage H), a fully clean check (no `_build`, 89 modules) took 408 s with a maximum resident size of 4.22 GB; the weighted monoid alone takes about 170 s.

`Everything.lagda.md` is this README as literate Agda: it imports every module. To get the browsable HTML, in which every name links to its definition, run

```bash
agda --library-file=libraries --html --html-highlight=auto --html-dir=html RMRCanonicity/PRACBPVGeneric/Everything.lagda.md
```

This writes one `.html` page per module (including the library modules), plus `html/RMRCanonicity.PRACBPVGeneric.Everything.md`: this page as Markdown with highlighted, hyperlinked code, for a Markdown renderer such as Jekyll. In that page the tables link into the HTML (module page and position of the definition); in `README.md` the same tables link to the `.agda` sources by line.

## Design choices

- **Worlds and lock telescopes.** Types and terms are indexed by telescopes `Θ` that compute their world: `∅ w` is the representable `y w`, `Θ , A` adds a variable, and `Θ ⧀⟨ κ , p ⟩` is the `p`-summand of the lock `L_κ`, the left adjoint of the right adjoint `R_κ` of the lock kind's strong familial arity. The modal type `[ κ ] A` denotes `R_κ ⟦A⟧`. POPL's setting is `W = 1` with no lock kinds.
- **One calculus.** CBPV(𝒯) with `𝟘`, `𝟙`, `⊕`, `×`, `U`, `F`, `⇒`, base types with constants, and `[ κ ]`. There is no CBPV⁺ (complex values and complex stacks; user decision) and no `&` or `⊤`.
- **Syntax.** Terms are intrinsically typed, with de Bruijn variables and neutrals (`up`, `opn`, `nm` reach across locks). Renamings and substitutions are data whose world map is computed. Operations `op o vs k` take parameter values `vs` and continuations behind the lock word of each slot.
- **Equations.** As in POPL (its D4), terms are plain inductive data and the equational theory is an inductive relation `≈`, not a quotient.
- **Two denotations.** `F A` is interpreted once by the term algebra of the signature (tree soundness, closing and the machine are about it) and once by a free model of the theory (the equational theory is about it). A binary logical relation relates them.
- **Relations by hand.** The logical relations are defined by recursion on types, with `𝒞⟦ F A ⟧` inductive, and their fundamental theorems are proved by induction on terms (POPL's D6). Their Kripke quantifiers range over chains of substitutions into lock telescopes (a root followed by locks), which are the closed contexts here.
- **The machine.** It is RMR's effect reduction for any configuration container `Q′` with any right module `ρ : Q ∘ T ⇒ Q` of the free-model monad `T`. POPL's operational model `Q = T`, `ρ = μ` is one instance. The effect step is RMR's derivative form `ρ((∂η C)⟪⟦op⟧(η(args))⟫)`, and it closes the operation's locks (closing) in the same step.
- **Normalization.** Affinity is a property of the right module, read off its generic redex (`Semantics/Affinity.agda`). The measure is the multiset of the heights of the holes' derivations, in counting form.

## POPL formalization → PRACBPVGeneric

One row for each row of the POPL formalization's "Paper → Agda" table, in its order. The left column names the POPL result and its Agda names; the right column gives the counterpart here, each name linked to its definition. **Not done** marks a result with no counterpart.

### Algebraic theories, free model monads, and the syntax (§2)

| POPL formalization | PRACBPVGeneric |
|---|---|
| §2.1 signatures, terms, equations, algebras, models (`Signature`, `Term`, `Theory`, `Model`, `IsHom`) | RMR's `Signature`, `Term`, `Theory`, `Algebra`, `Satisfies`, `Hom` (`RightModuleReduction.Theory`, `.TermAlgebra`), at the signature [`polynomial`](RMRCanonicity.PRACBPVGeneric.Polynomial.html#9750) with its [`strength`](RMRCanonicity.PRACBPVGeneric.Polynomial.html#9951), built from a lock signature [`LockSig`](RMRCanonicity.PRACBPVGeneric.Signature.html#2347) and an operation signature [`OpSig`](RMRCanonicity.PRACBPVGeneric.Signature.html#2519). A theory over it: [`Equations`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#3840), [`theory`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#4046), [`noEquations`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#4411) |
| §2.1 free model monad (`FreeModel`, `ext-uniq`, `μ`, `map`) | RMR's `FreeModel` (`RightModuleReduction.FreeAdjunction`: a left adjoint to the forgetful functor from models, with its monad). Its universal property as POPL states it: [`T`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html#4183), [`η`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html#4421), [`ext`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html#4562), [`ext-η`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html#4687), [`ext-unique`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html#4928). POPL's record itself, at `W = 1`: [`PolyFree`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Common.html#6730). The free model of an equation-free theory (terms): [`freeModel`](RMRCanonicity.PRACBPVGeneric.Semantics.FreeModel.html#3842), [`term-unique`](RMRCanonicity.PRACBPVGeneric.Semantics.FreeModel.html#1722) |
| §2.3 Fig. 1 syntax of CBPV(𝒯) and CBPV⁺(𝒯) (`VTy`, `CTy`, `Mode`, `Val`, `Comp`, `Stack`) | CBPV(𝒯) only; **CBPV⁺ not done (excluded by user decision)**, so there is no `Mode`. [`ValTy`](RMRCanonicity.PRACBPVGeneric.Types.html#476), [`CompTy`](RMRCanonicity.PRACBPVGeneric.Types.html#494) (with [`𝟘`](RMRCanonicity.PRACBPVGeneric.Types.html#582), [`_⊕_`](RMRCanonicity.PRACBPVGeneric.Types.html#606) and the modality [`[_]_`](RMRCanonicity.PRACBPVGeneric.Types.html#687)); [`Tele`](RMRCanonicity.PRACBPVGeneric.Syntax.html#4457), [`Ne`](RMRCanonicity.PRACBPVGeneric.Syntax.html#5506), [`Val`](RMRCanonicity.PRACBPVGeneric.Syntax.html#6029), [`Comp`](RMRCanonicity.PRACBPVGeneric.Syntax.html#6104), [`Stack`](RMRCanonicity.PRACBPVGeneric.Syntax.html#6141) |
| §2.3 Fig. 2 operations `V[γ]`, `M[γ]`, `S[γ]`, `δ[γ]`, `S[M]`, `S'[S]` (`renC`, `subV`, `subC`, `subS`, `_⊚_`, `plug`, `_∘ˢ_`, `plug-sub`) | [`Ren`](RMRCanonicity.PRACBPVGeneric.Syntax.html#8366), [`Sub`](RMRCanonicity.PRACBPVGeneric.Syntax.html#11908), [`renC`](RMRCanonicity.PRACBPVGeneric.Syntax.html#9927), [`subV`](RMRCanonicity.PRACBPVGeneric.Syntax.html#13689), [`subC`](RMRCanonicity.PRACBPVGeneric.Syntax.html#13795), [`subS`](RMRCanonicity.PRACBPVGeneric.Syntax.html#13847), [`plug`](RMRCanonicity.PRACBPVGeneric.Syntax.html#7775); fusion [`sub-fuseC`](RMRCanonicity.PRACBPVGeneric.Metatheory.Substitution.html#34631); [`sub-plug`](RMRCanonicity.PRACBPVGeneric.Metatheory.SubstReduction.html#1280). Composites of substitutions are formal: [`Chain`](RMRCanonicity.PRACBPVGeneric.Metatheory.Chain.html#2952), [`chC`](RMRCanonicity.PRACBPVGeneric.Metatheory.Chain.html#3402) (under a lock, one substitution over the composite world map would read a body at a position equal only propositionally). No stack composition `S'[S]` (nothing uses it) |
| §2.3 Fig. 2 equational theory (`_≈v_`, `_≈c_`) | [`_≈v_`](RMRCanonicity.PRACBPVGeneric.Metatheory.Equational.html#5373), [`_≈vs_`](RMRCanonicity.PRACBPVGeneric.Metatheory.Equational.html#5420), [`_≈c_`](RMRCanonicity.PRACBPVGeneric.Metatheory.Equational.html#5473) (with η for `[ κ ]` and algebraicity for every stack across the slot's locks); closed under substitution: [`sub≈c`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqSubstitution.html#7563) |

### Denotational semantics and equational canonicity (§3)

| POPL formalization | PRACBPVGeneric |
|---|---|
| §3.2 Fig. 3 denotational semantics (`⟦_⟧v`, `⟦_⟧c`, `⟦_⟧V`, `⟦_⟧C`, `⟦_⟧S`, `powModel`, `prodModel`) | In the term algebra: [`⟦_⟧v`](RMRCanonicity.PRACBPVGeneric.Semantics.Denotation.html#4842), [`⟦_⟧c`](RMRCanonicity.PRACBPVGeneric.Semantics.Denotation.html#4859), [`⟦_⟧V`](RMRCanonicity.PRACBPVGeneric.Semantics.Denotation.html#8528), [`⟦_⟧C`](RMRCanonicity.PRACBPVGeneric.Semantics.Denotation.html#8630), [`⟦_⟧S`](RMRCanonicity.PRACBPVGeneric.Semantics.Denotation.html#10310). In a free model of the theory (POPL's): [`⟦_⟧m`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html#12102), [`⟦_⟧C`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html#14547). `powModel` is [`expModel`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Denotation.html#5867), which needs [`ExpClosed`](RMRCanonicity.PRACBPVGeneric.Semantics.StrongTheory.html#3009); `prodModel` has no counterpart (no `&`) |
| §3.2 the denotation preserves substitution, plugging and operations (`den-subC`, `den-plug`, `den-stack-hom`) | [`den-subC`](RMRCanonicity.PRACBPVGeneric.Semantics.Substitution.html#7141), [`den-plug`](RMRCanonicity.PRACBPVGeneric.Semantics.Soundness.html#6880); for the free-model denotation [`den-subC`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Substitution.html#6711), [`den-plug`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Soundness.html#6753), [`den-stack-op`](RMRCanonicity.PRACBPVGeneric.Semantics.EquationalSoundness.html#5738) |
| §3.2 soundness of `⟦-⟧` for the equations (`sound-c`) | [`sound-v`](RMRCanonicity.PRACBPVGeneric.Semantics.EquationalSoundness.html#8642), [`sound-c`](RMRCanonicity.PRACBPVGeneric.Semantics.EquationalSoundness.html#8875), [`sound-c≡`](RMRCanonicity.PRACBPVGeneric.Semantics.EquationalSoundness.html#13198), for the free-model denotation, given a free model `fm` and `ec : ExpClosed eqs` |
| §3.3 Fig. 6 equational logical relation (`𝒱⟦_⟧`, `𝒞⟦_⟧`, `FPred`) | [`𝒱⟦_⟧`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#4938), [`𝒞⟦_⟧`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#4985), [`FPred`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#4487), closed under `≈`: [`𝒱-conv`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#5839), [`𝒞-conv`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#5910) |
| §3.4 Fundamental Theorem (`fundV`, `fundC`) | [`fundV`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#17971), [`fundC`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#18081) |
| §3.4 Corollary (equational canonicity) (`equational-canonicity`) | [`related`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#18341), [`equational-canonicity`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#18910), for every computation of type `F A` on a lock telescope |
| §3.4 Corollary (uniqueness; corrected, C3) (`canonical-form-unique`) | [`⌊_⌋`](RMRCanonicity.PRACBPVGeneric.Semantics.EqCanonicity.html#3389), [`den-reify`](RMRCanonicity.PRACBPVGeneric.Semantics.EqCanonicity.html#3758), [`canonical-form-denotes`](RMRCanonicity.PRACBPVGeneric.Semantics.EqCanonicity.html#4199), [`canonical-form-unique`](RMRCanonicity.PRACBPVGeneric.Semantics.EqCanonicity.html#4677), [`canonicity`](RMRCanonicity.PRACBPVGeneric.Semantics.EqCanonicity.html#4981) |

### Tree reduction (§4)

| POPL formalization | PRACBPVGeneric |
|---|---|
| §4.1 Fig. 5 tree reduction (`_↦red_`, `_↦h_`, `_↦_`, `det`) | [`_⇝_`](RMRCanonicity.PRACBPVGeneric.Reduction.html#1704) (redexes, including the one-frame operation steps `op-to`, `op-app`), [`_↦_`](RMRCanonicity.PRACBPVGeneric.Reduction.html#2892) (a head step under a stack), [`_↦*_`](RMRCanonicity.PRACBPVGeneric.Reduction.html#3117) (with congruence under `op`); determinism by a step function: [`next`](RMRCanonicity.PRACBPVGeneric.Metatheory.Determinism.html#1867), [`↦-det`](RMRCanonicity.PRACBPVGeneric.Metatheory.Determinism.html#5522) |
| §4.1 Theorem (soundness of `↦tree`) (`sound↦`) | [`sound⇝`](RMRCanonicity.PRACBPVGeneric.Semantics.Soundness.html#4488), [`sound↦`](RMRCanonicity.PRACBPVGeneric.Semantics.Soundness.html#7297), [`sound↦*`](RMRCanonicity.PRACBPVGeneric.Semantics.Soundness.html#7535); for the free-model denotation [`sound↦`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Soundness.html#7170) |
| §4.2 Fig. 7 operational logical relation (`𝒱⟦_⟧`, `𝒞⟦_⟧`, `FPred`) | [`Tree`](RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html#4602), [`𝒱⟦_⟧`](RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html#5047), [`𝒞⟦_⟧`](RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html#5094), Kripke over chains into lock telescopes ([`IsLT`](RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html#3736)); [`mono𝒞`](RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html#7333) |
| §4.2 Lemma (anti-reduction; corrected, C5) (`hjoin`, `AR`, `FW`) | Holds for every step at every type, so C5's restriction and `hjoin` are not needed: [`back𝒞`](RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html#7685). An operation moves one frame per step (`op-to`, `op-app`) and `↦` never reduces under `op`, so `M ↦ M'` gives `app M V ↦ app M' V` ([`↦-app`](RMRCanonicity.PRACBPVGeneric.Metatheory.Determinism.html#1648)); `𝒞⟦ F A ⟧` is closed under anti-reduction by its constructor `back` |
| §4.2 Lemma (congruence) (`𝒞-op`) | [`op𝒞`](RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html#7852) (at `A ⇒ B` by one `op-app` step, the argument moved across the slot's locks); equational: [`𝒞-op`](RMRCanonicity.PRACBPVGeneric.Metatheory.EqLogicalRelation.html#8323) |
| §4.3 Fundamental Lemma (`fundV`, `fundC`, `related`) | [`fundV`](RMRCanonicity.PRACBPVGeneric.Metatheory.Fundamental.html#8465), [`fundC`](RMRCanonicity.PRACBPVGeneric.Metatheory.Fundamental.html#8575), [`related`](RMRCanonicity.PRACBPVGeneric.Metatheory.Termination.html#3046) |
| §4.3 Corollary (termination) (`termination`) | [`termination`](RMRCanonicity.PRACBPVGeneric.Metatheory.Termination.html#3150), into operation trees [`OpTree`](RMRCanonicity.PRACBPVGeneric.Metatheory.Termination.html#2189) read back by [`reify`](RMRCanonicity.PRACBPVGeneric.Metatheory.Termination.html#2411) |
| §4.3 Corollary (strong normalization) (`strong-normalization`) | [`strong-normalization`](RMRCanonicity.PRACBPVGeneric.Metatheory.TreeNormalization.html#2563): accessibility for the converse [`_↤_`](RMRCanonicity.PRACBPVGeneric.Metatheory.TreeNormalization.html#2066), from determinism, with no metric |
| §4.3 Corollary (canonicity; corrected, C8) (`tree-canonicity`) | [`tree-canonicity`](RMRCanonicity.PRACBPVGeneric.Semantics.TreeCanonicity.html#2462), [`tree-canonicity₀`](RMRCanonicity.PRACBPVGeneric.Semantics.TreeCanonicity.html#2765) (at a root) |

### Configuration reduction (§5)

| POPL formalization | PRACBPVGeneric |
|---|---|
| §5.2 polynomials, `∂p`, plugging (`Poly`, `⟦_⟧`, `∂`, `plug`, `plug-map`) | The operations form an RMR signature, a polynomial whose positions and scopes depend on the world: [`polynomial`](RMRCanonicity.PRACBPVGeneric.Polynomial.html#9750), [`strength`](RMRCanonicity.PRACBPVGeneric.Polynomial.html#9951), read back by [`shape-is`](RMRCanonicity.PRACBPVGeneric.Polynomial.html#10235), [`position-is`](RMRCanonicity.PRACBPVGeneric.Polynomial.html#10375), [`scope-is`](RMRCanonicity.PRACBPVGeneric.Polynomial.html#10573), [`strength-is`](RMRCanonicity.PRACBPVGeneric.Polynomial.html#10825). Configurations are RMR indexed containers, with RMR's derivative `∂Q`, `plug` and `plug-map` (`RightModuleReduction.IndexedContainer`, `.EffectReduction`) |
| §5.2 Def. (Operational Model) (`OperationalModel`, `map-poly`) | Generalized: any configuration container `Q′` with any right module `R` of the free-model monad, the parameters of [`Run`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#6820). POPL's `Q = T`, `ρ = μ`: for a free model presented by a container, [`Presentation`](RMRCanonicity.PRACBPVGeneric.Semantics.PolySelfModule.html#3793) (its naturality `to-nat` is `map-poly`), [`ρ-is-μ`](RMRCanonicity.PRACBPVGeneric.Semantics.PolySelfModule.html#4687), [`polyModule`](RMRCanonicity.PRACBPVGeneric.Semantics.PolySelfModule.html#5114); for the term model of an equation-free theory, [`TermQ′`](RMRCanonicity.PRACBPVGeneric.Semantics.SelfModule.html#5132), [`selfModule`](RMRCanonicity.PRACBPVGeneric.Semantics.SelfModule.html#10044) |
| §5.3 Fig. "Configuration Reduction" (derivative form) (`_↦T_`) | [`_⟶_`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#8880) on [`Config`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#7764), with one-hole contexts [`Ctxt`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#7823): `pure` (a tree step in a hole) and `effect`, whose target is RMR's `step`, `ρ((∂η C)⟪⟦op⟧(η(args))⟫)`, after the operation is closed ([`closeK`](RMRCanonicity.PRACBPVGeneric.Closing.html#3247)); [`_⟶*_`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#9719) |
| §5.3 Theorem (soundness of the initial configuration) (`sound-init`) | [`denote-η`](RMRCanonicity.PRACBPVGeneric.Semantics.PolySelfModule.html#5930), [`denote-ηC`](RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html#5339) (and [`denote-ηC`](RMRCanonicity.PRACBPVGeneric.Semantics.SelfCanonicity.html#4856), by `refl`): `η M` denotes the term-algebra denotation of `M` mapped into the free model; at a first-order type that is the free-model denotation: [`denote-ηC-free`](RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html#9410), [`denote-ηC-free`](RMRCanonicity.PRACBPVGeneric.Semantics.SelfCanonicity.html#5473) |
| §5.3 Theorem (soundness of `↦T`) (`sound-T`) | [`sound⟶`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#9986), [`sound⟶*`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#10507), in any right module |
| §5.4 Def. (Affinity), and appendix "Simplification" (`step`, `ρ`, `Affine`, `simplification`, `effect-via-step`) | [`ModuleAffine`](RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html#7184): the generic redex [`Gen`](RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html#6175), its step [`generic`](RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html#6720) (POPL's `step`), [`origin`](RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html#6940) (POPL's `ρ`); every actual step is the generic one renamed, [`represent`](RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html#7882) (the role of `simplification` / `effect-via-step`); [`affine-subsingleton`](RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html#8622). At `Q = T`: [`Affine`](RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html#10684), [`genSpliced`](RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html#11825), [`origin-is`](RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html#12113) |
| §5.4 Lemma (Progress) (`progress-T`) | [`progress`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#12788), [`Terminal`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#10523) |
| §5.4 Def. (Termination Metric; corrected, C7) (`size`, `‖_‖`, `‖_‖T`) | The height of a derivation of the logical relation, not POPL's metric: [`size`](RMRCanonicity.PRACBPVGeneric.Metatheory.TreeSize.html#4324), [`size-unique`](RMRCanonicity.PRACBPVGeneric.Metatheory.TreeSize.html#4988), [`sz`](RMRCanonicity.PRACBPVGeneric.Metatheory.TreeSize.html#12321), [`sz-step`](RMRCanonicity.PRACBPVGeneric.Metatheory.TreeSize.html#12414); a configuration is measured by the multiset of its holes' heights in counting form, [`measure`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#6795), ordered by [`_⊏_`](RMRCanonicity.PRACBPVGeneric.FinCount.html#4044), well founded by [`⊏-vanishing-acc`](RMRCanonicity.PRACBPVGeneric.FinCount.html#10035) |
| §5.4 Theorem (strong normalization for `↦T`) (`strong-normalization-T`, `normalize-T`, `canonicity-T`) | [`decrease`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#7488), [`strongNormalization`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#10125), [`weakNormalization`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#13758), [`wn-sound`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#13925), [`normalize`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#5976), in any affine right module with finitely many holes and continuations; at `Q = T`: [`canonicity-T`](RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html#13517), [`canonicity-T`](RMRCanonicity.PRACBPVGeneric.Semantics.SelfCanonicity.html#4401) |
| §5.4 Lemma (uniqueness of the result) (`final-unique`, `ground-canonicity`) | [`Final`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#3937), [`retF`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#4058), [`den-final`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#4325), [`final-unique`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#4542) (a left inverse suffices, D12), [`ground-canonicity`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#6269); [`Ground`](RMRCanonicity.PRACBPVGeneric.Semantics.Ground.html#1569), [`reflect`](RMRCanonicity.PRACBPVGeneric.Semantics.Ground.html#1808), [`reflect-den`](RMRCanonicity.PRACBPVGeneric.Semantics.Ground.html#2139); at `Q = T`: [`ground-canonicity-T`](RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html#13663) |
| §5.2 monad containers (Uustalu), and the equivalence of their two sets of laws, D15 (`MCOps`, `MonadLaws`, `UustaluLaws`, `M→U`, `U→M`, `MonadContainer`) | **Not done.** Configurations are RMR indexed containers with a right module; monad containers are not developed |
| §5.2 Def. (Operational Model) as a monad container, D15 (`OperationalModel`, `gen`, `μₘ≡μ`, `map-poly`) | **Not done** |
| the two definitions of operational model are equivalent, D15 (`toPoly`, `fromPoly`, …) | **Not done** |
| §5.3–5.4 for monad-container operational models, D15 (`_↦T_`, `sound-T`, `step-shape`, `step-pos`, `Affine`, …) | **Not done** |

### Instances (§2.2, §5.3)

All four are at `W = 1` with no locks, each with its equations, as `Q = T` with `ρ = μ` (`Instances/Equational/`).

| POPL formalization | PRACBPVGeneric |
|---|---|
| Writer: theory, free model, affinity, derived rule (`writerTheory`, `writerFree`, `writerOM`, `writer-affine`, `writer-effect`) | [`writerEqs`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#3741), [`writerFree`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#5041), [`writer-module`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#6229), [`writer-affine`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#6357), [`writer-effect`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#6653); also [`writer-sn`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#7141), [`writer-wn`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#7218), [`writer-ground-canonicity`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#7309), and a run [`writer-run`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Writer.html#7869) |
| Errors (`errTheory`, `errFree`, `errOM`, `err-affine`, `err-effect`) | [`errEqs`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#3268), [`errFree`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#4329), [`err-module`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#5402), [`err-affine`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#5492), [`err-effect`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#6091); also [`err-sn`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#6375), [`err-wn`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#6446), [`err-ground-canonicity`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#6531), [`err-run`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.Errors.html#7198) |
| Boolean state, and the get and set rules (`stateTheory`, `stateFree`, `stateOM`, `state-affine`, `state-get`, `state-set`) | [`stateEqs`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#4618) (the four lens laws, D13), [`stateFree`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#7257), [`state-module`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#9715), [`state-affine`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#10483), [`state-get`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#11394), [`state-set`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#12590); also [`state-sn`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#13691), [`state-wn`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#13766), [`state-ground-canonicity`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#13855), [`toggle-run`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.State.html#14560) |
| Weighted monoid (`wmTheory`, `wmFree`, `wmOM`, `wm-affine`, `wm-act`, `wm-unit`, `wm-mul`) | [`wmEqs`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html#5801), [`wmFree`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html#15633), [`wm-module`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html#18730), [`wm-act`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html#21502), [`wm-unit`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html#22235), [`wm-mul`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html#22709), a run [`wm-run`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html#24154) with [`wm-run-unique`](RMRCanonicity.PRACBPVGeneric.Instances.Equational.WeightedMonoid.html#24575). **`wm-affine` not done (deferred by user decision)**, so no SN, WN or ground canonicity for it |

### Future work: combining effects

| POPL formalization | PRACBPVGeneric |
|---|---|
| combining effects with a distributive law of monadic containers, writer + errors (`γ`, `μWE`, `mc`, `theory`, `OM`, `affine`, `rule-tell`, `rule-raise`, …) | **Not done** |

## Beyond the POPL formalization

| Topic | What is proved | Agda |
|---|---|---|
| Worlds and presheaf semantics | every type denotes a presheaf on `W` (`𝒱 = [W, Set]`), every telescope a presheaf over `y (world Θ)`; renamings and substitutions carry world maps (`WMap`: `W` with a strict identity) and denote context morphisms over them | [`𝒱`](RMRCanonicity.PRACBPVGeneric.Semantics.Presheaf.html#1542), [`world`](RMRCanonicity.PRACBPVGeneric.Syntax.html#4469), [`WMap`](RMRCanonicity.PRACBPVGeneric.Syntax.html#2667), [`den-renC`](RMRCanonicity.PRACBPVGeneric.Semantics.Renaming.html#6169), [`den-subC`](RMRCanonicity.PRACBPVGeneric.Semantics.Substitution.html#7141) |
| Lock telescopes and the `[ κ ]` modality | a lock kind is a strong familial arity; its lock is the coend `L_κ Γ = ∫^w Γ w × E w` (a set quotient), left adjoint to `R_κ`, with the adjunction a hom-set bijection natural in `Γ`; `[ κ ] A` denotes `R_κ ⟦A⟧`, with `shut` and `openV`, β by definition and η as an axiom of `≈` | [`LockKind`](RMRCanonicity.PRACBPVGeneric.Signature.html#2086), [`_⧀⟨_,_⟩`](RMRCanonicity.PRACBPVGeneric.Syntax.html#4556), [`[_]_`](RMRCanonicity.PRACBPVGeneric.Types.html#687), [`L`](RMRCanonicity.PRACBPVGeneric.Semantics.Lock.html#5511), [`R`](RMRCanonicity.PRACBPVGeneric.Semantics.Lock.html#3989), [`unlock`](RMRCanonicity.PRACBPVGeneric.Semantics.Lock.html#6308), [`transpose`](RMRCanonicity.PRACBPVGeneric.Semantics.Lock.html#6690), [`unlock-transpose`](RMRCanonicity.PRACBPVGeneric.Semantics.Lock.html#7082), [`transpose-unlock`](RMRCanonicity.PRACBPVGeneric.Semantics.Lock.html#7387), [`shut-open`](RMRCanonicity.PRACBPVGeneric.Semantics.Lock.html#13024) |
| Local state | `W = Inj`, `new` behind a `fresh` lock that binds the new location; a runner machine with a concrete allocation run, strongly and weakly normalizing | [`newℓ`](RMRCanonicity.PRACBPVGeneric.Instances.LocalState.html#5977), [`read`](RMRCanonicity.PRACBPVGeneric.Instances.LocalState.html#5619), [`write`](RMRCanonicity.PRACBPVGeneric.Instances.LocalState.html#5757), [`alloc-write`](RMRCanonicity.PRACBPVGeneric.Instances.Machines.LocalState.html#3901), [`local-sn`](RMRCanonicity.PRACBPVGeneric.Instances.Normalization.LocalState.html#2264) |
| Guarded recursion | `W = ω^op`, `step` behind a `tick` lock, `▸ A = [ tick ] A`, `delay`, `next`, `later`; the tick lock is the earlier modality; a machine with timeout, strongly and weakly normalizing, with ground canonicity | [`delay`](RMRCanonicity.PRACBPVGeneric.Instances.Guarded.html#4595), [`next`](RMRCanonicity.PRACBPVGeneric.Instances.Guarded.html#4494), [`later`](RMRCanonicity.PRACBPVGeneric.Instances.Guarded.html#4718), [`earlierIso`](RMRCanonicity.PRACBPVGeneric.Semantics.GuardedLock.html#1636), [`delay-delay`](RMRCanonicity.PRACBPVGeneric.Instances.Machines.Guarded.html#2288), [`guarded-ground-canonicity`](RMRCanonicity.PRACBPVGeneric.Instances.Normalization.Guarded.html#2335) |
| Closing and the fused effect step | a closed operation's continuations live behind its slots' locks; closing turns them into closed terms at the scopes (any lock word) and preserves the denotation; the machine closes and runs an operation in one step, which keeps it strongly normalizing | [`opNodeC`](RMRCanonicity.PRACBPVGeneric.Closing.html#2675), [`closeK`](RMRCanonicity.PRACBPVGeneric.Closing.html#3247), [`closeOp`](RMRCanonicity.PRACBPVGeneric.Closing.html#3630), [`close-den`](RMRCanonicity.PRACBPVGeneric.Semantics.Closed.html#6619), [`_⟶_`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#8880) |
| Syntactic laws | terms form sets; renaming and substitution identity, fusion and extensionality over arbitrary paths of telescopes; closed computations form a presheaf and an algebra | [`isSetComp`](RMRCanonicity.PRACBPVGeneric.Metatheory.TermsSet.html#13171), [`ren-fuseC`](RMRCanonicity.PRACBPVGeneric.Metatheory.Renaming.html#18136), [`sub-fuseC`](RMRCanonicity.PRACBPVGeneric.Metatheory.Substitution.html#34631), [`closedLaws`](RMRCanonicity.PRACBPVGeneric.Metatheory.ClosedLaws.html#4349) |
| The machine generic in any right module | soundness, strong and weak normalization, progress, den-final, final-unique and ground canonicity hold for every configuration container and right module (affine, with finitely many holes and continuations, where needed) | [`Run`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#6820), [`sound⟶`](RMRCanonicity.PRACBPVGeneric.Semantics.Machine.html#9986), [`strongNormalization`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#10125), [`final-unique`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#4542), [`ground-canonicity`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#6269) |
| Runners (one-store state) | a deterministic runner (states at each world, halting outcomes, a transition) gives a right module of the term monad; the machine at error, global state, local state and guarded recursion, with concrete runs and their agreement with the runner on the denotation | [`run`](RMRCanonicity.PRACBPVGeneric.Semantics.Runner.html#4949), [`runnerModule`](RMRCanonicity.PRACBPVGeneric.Semantics.Runner.html#7116), [`op-step`](RMRCanonicity.PRACBPVGeneric.Semantics.RunMachine.html#5436), [`run-return`](RMRCanonicity.PRACBPVGeneric.Semantics.RunMachine.html#7196), [`runner-affine`](RMRCanonicity.PRACBPVGeneric.Semantics.RunnerAffine.html#2417), [`toggle-run`](RMRCanonicity.PRACBPVGeneric.Instances.Machines.GlobalState.html#2360) |
| Module-level affinity and the counting-form multiset measure | affinity is stated on the right module (injective origins at the generic redex), not per instance; the measure is a multiset of heights in counting form, compared top-down, well founded on vanishing counting functions; neither needs the module to keep the number of holes | [`ModuleAffine`](RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html#7184), [`represent`](RMRCanonicity.PRACBPVGeneric.Semantics.Affinity.html#7882), [`count`](RMRCanonicity.PRACBPVGeneric.FinCount.html#3828), [`count-replace`](RMRCanonicity.PRACBPVGeneric.FinCount.html#6648), [`⊏-vanishing-acc`](RMRCanonicity.PRACBPVGeneric.FinCount.html#10035), [`decrease`](RMRCanonicity.PRACBPVGeneric.Semantics.Normalization.html#7488) |
| Equation-free `Q = T` at any `W` (whose objects form a set) | the terms of an equation-free theory form a configuration container whose action is substitution (`ρ = μ`), affine; the machine there, with runs for error and for list nondeterminism without the monoid equations | [`selfModule`](RMRCanonicity.PRACBPVGeneric.Semantics.SelfModule.html#10044), [`self-affine`](RMRCanonicity.PRACBPVGeneric.Semantics.SelfModule.html#15059), [`op-root`](RMRCanonicity.PRACBPVGeneric.Semantics.SelfMachine.html#5889), [`orFail-run`](RMRCanonicity.PRACBPVGeneric.Instances.SelfModule.List.html#6657) |
| The denotation comparison | a binary Kripke logical relation between the term-algebra and the free-model denotations, with its fundamental lemma; at first-order types the canonical algebra map carries one denotation of a closed computation to the other, and likewise the machine's map | [`Rv`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison.html#5884), [`Rc`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison.html#5927), [`fundC`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison.html#16092), [`comparison`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison.html#20618), [`machine-comparison`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison.html#22537), [`final-comparison`](RMRCanonicity.PRACBPVGeneric.Semantics.PolyMachine.html#9925) |
| Models closed under exponentials | the free-model denotation needs the theory's models closed under exponentials; proved for every equation-free theory and for every theory over a chaotic `W` (e.g. `W = 1`) | [`ExpClosed`](RMRCanonicity.PRACBPVGeneric.Semantics.StrongTheory.html#3009), [`expClosed-noEquations`](RMRCanonicity.PRACBPVGeneric.Semantics.StrongTheory.html#3264), [`expClosed-chaotic`](RMRCanonicity.PRACBPVGeneric.Semantics.StrongTheory.html#5836) |

## Deviations and limits

Each item is also recorded, with its reason, in `BUILD-NOTES.md` under the stage that introduced it.

### Deviations from the POPL formalization

| Topic | POPL formalization | PRACBPVGeneric |
|---|---|---|
| Setting | `W = 1`, no locks | any category of worlds, lock telescopes and `[ κ ]` (see Design choices) |
| CBPV⁺ | mode `cbpv⁺`: complex values and complex stacks | not done, by user decision. So there are no value eliminators: the η laws of `𝟘`, `+` and `×` are stated for computations only (POPL's `η𝟘c`, `η+c`, `η×c`), and POPL's value laws `η𝟘v`, `η+v`, `η×v`, `vcase+-β`, `vcase×-β` have no counterpart |
| `&` and `⊤` | computation types `&`, `⊤` | absent, so `&-β`, `η&`, `η⊤` and `prodModel` have no counterpart |
| `absurd` | a value, `absurd : Val Γ 𝟘 → Val Γ A` | a computation, `absurd V : Comp Θ B` (Levy's `case V of {}`); values stay introduction forms and neutrals |
| Two denotations | one, in the free model of the theory | the term-algebra denotation (`Semantics/Denotation.agda`, for tree soundness, closing and the machine) and the free-model denotation (`Semantics/Free/`, for the equational theory). `Free/Renaming`, `Free/Substitution`, `Free/Soundness` and `Free/Closed` repeat the text of `Renaming`, `Substitution`, `Soundness` and `Closed` (only `return` and `to` differ): making the old modules generic in the interpretation of `F` would have changed the existing denotation |
| Comparing the denotations | not needed | [`comparison`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison.html#20618) is a function only at first-order result types (no `U`: at `A ⇒ B` the denotations are contravariant, so there is no map); at other types only the relation [`related-closed`](RMRCanonicity.PRACBPVGeneric.Semantics.Free.Comparison.html#17932). It is stated at roots `∅ w`, not at lock telescopes (the relation at a lock asks for representatives of a quotient's points) |
| `ExpClosed` | not needed (`W = 1`) | the free-model denotation, `sound-c` and the canonical-form theorems take `ec : ExpClosed eqs`. Proved for every equation-free theory and for every theory over a chaotic `W`; at a general `W` it can fail (an equation between operations whose continuations are reached along different maps; the counterexample is not built) |
| Instances of the theory's equations | open computations `γ : Fin n → Comp Γ B` | closed computations ([`ClosedEnv`](RMRCanonicity.PRACBPVGeneric.Metatheory.Equational.html#4367), [`inst`](RMRCanonicity.PRACBPVGeneric.Metatheory.Equational.html#4642)) moved into any telescope along a world map; an open instance is not natural in the world, so not sound from `Satisfies` at a general `W`. Instances open in variables that can be λ-abstracted are derivable (`theory` at the function type, `op-app≈`, `⇒-β`); instances whose leaves use a lock's names (`nm`) are not |
| Closed contexts | the empty context | lock telescopes (a root followed by locks; no variables, but names). The canonical forms [`OpTree`](RMRCanonicity.PRACBPVGeneric.Metatheory.Termination.html#2189) have values of lock telescopes at their leaves, and [`⌊_⌋`](RMRCanonicity.PRACBPVGeneric.Semantics.EqCanonicity.html#3389) is a map out of `⟦ Θ ⟧` |
| Anti-reduction (C5) | restricted to head steps, with `hjoin` and determinism of head steps | not needed: `↦` is one head step under a stack and never reduces under `op`, so anti-reduction holds for every step ([`back𝒞`](RMRCanonicity.PRACBPVGeneric.Metatheory.LogicalRelation.html#7685)) |
| Tree SN (C7) | from a decreasing metric | from determinism ([`strong-normalization`](RMRCanonicity.PRACBPVGeneric.Metatheory.TreeNormalization.html#2563)): a derivation is a chain of `back` steps ending in `return` or `op`. The machine's measure uses the height of a derivation, not POPL's metric, and a multiset rather than a sum |
| Termination's tree | — | the tree that [`termination`](RMRCanonicity.PRACBPVGeneric.Metatheory.Termination.html#3150) extracts does not reduce to a normal form by `refl` (the derivation passes through a transport on the indexed `Tree`); no statement needs it to |
| Operational model | `T(X)` the free model, polynomial; `ρ = μ` | any right module of any configuration container. `Q = T` with equations needs a free model presented by a container ([`Presentation`](RMRCanonicity.PRACBPVGeneric.Semantics.PolySelfModule.html#3793)): there is one more generic layer (`PolySelfModule`, `PolyMachine`), and `Instances/Equational/Common.agda` builds the free models at `W = 1` from POPL's universal property |
| Machine results | for `Q = T` | for every right module ([`den-final`](RMRCanonicity.PRACBPVGeneric.Semantics.ConfigCanonicity.html#4325) by the module's unit law); `canonicity-T` is the instance at `η M` |
| Ground types | built from `0`, `1`, `+`, `×` | also base types (a closed value of base type is a constant); not `[ κ ] A` (a closed `shut V` has its body behind a lock, where names may occur) |
| Derived rules of the instances | equations about `μ (C ⟪ … ⟫)` | machine steps `x ⟶ y` that include closing the operation; state's rules at any hole (POPL: at `s₀`); the weighted monoid's on configurations `((suc n , cons r ws) , cons M γ)` |
| Monoids | `MonoidOn`, not necessarily a set | cubical `Monoid ℓ-zero` (a set): RMR's container shapes are sets |
| Variables of equations | `Fin n` | constant presheaves; get-get uses `Bool × Bool` variables, so its satisfaction in the free model is `refl` |
| Errors | `X + 1` | `X + 1` as a presented free model (`Instances/Equational/Errors.agda`), and also the term model of the same equation-free theory (`Instances/SelfModule/Error.agda`); the two machines agree on reachable configurations (`raise` is `raised`), which is stated, not proved |
| Weighted monoid | `WeightedMonoidAffine`: affinity, hence SN, WN, ground canonicity | affinity deferred by user decision; the instance has its theory, free model, `ρ = μ`, the derived rules, soundness, `final-unique` and a run, but no SN, WN or ground canonicity |
| Monad containers (D15), future work | `MonadContainer/*`, `FutureWork/WriterWithErrors` | not done |

### Limits and open problems

- **No adequacy of the machine.** Its steps preserve the denotation and, under the hypotheses, it is strongly and weakly normalizing. Nothing shows that a program whose denotation runs to a configuration reaches that configuration on the machine.
- **Normalization is under hypotheses.** `Semantics/Normalization.agda` assumes `finOp`, `finQ` and `ModuleAffine`. They are discharged for runners (any equation-free theory), for `Q = T` over an equation-free theory with finitely many, numbered continuations and a set of worlds, and for writer, errors and Boolean state with their equations. A non-affine module (one that copies a thread) is not covered.
- **`Q = T` with equations only at `W = 1`.** `PolyMachine` is generic in `W` and in the presented free model, but the four presented free models are at `W = 1`. The equation-free `Q = T` (`SelfModule`, the term model) works at any `W` whose objects form a set. No generic free model of a theory with equations (a quotient of terms) is built.
- **List nondeterminism with the monoid equations** (`Q = T = List`, `ρ = concat`) is not built. Its free model is lists, which would fit `PolySelfModule` like the weighted monoid. Without the equations the free model is binary trees, which is what `Instances/SelfModule/List.agda` runs.
- **Runners only for equation-free theories.** `Runner` builds right modules only for equation-free theories; a runner for a theory with equations must respect them.
- **`isSet Lk` and `isSet Base` are hypotheses** of the syntactic laws, and so of the machine instances; `LockSig` does not assume them, and every instance proves them.
- **Layering.** The three equational metatheory modules import `Semantics.Machine` (for the record `Equations`) and `Semantics.Presheaf`. There is no cycle; moving `Equations` would change `Machine.agda`, whose names every instance uses.
- **Maps out of a lock are into sets.** They are built by the quotient's `rec` and `elimProp`. A `Type`-valued construction on locked telescopes, such as the comparison's relation, is stated on representatives instead (`LRel`).
- **No exchange.** Renamings and substitutions are order-preserving on names. Max New's `Γ − ℓ`, which keeps later names, needs a 2-cell `fresh·fresh ⇒ fresh·fresh`.
- **`earlierIso` is pointwise.** It is an `Iso` at each world, with `earlier-nat` for naturality, not an isomorphism of presheaves. Local state's lock (a Day convolution with `y 1`) is not computed.
- **The calculus.** Positions, scopes and the strength follow the operation, not its parameter values. Names are uniform over the positions of one lock kind. Every lock kind is a type former, and a world-changing slot needs a lock kind. `ι` is data (a polynomial does not determine its strength). On morphisms the polynomial agrees with `pos` / `smap` only propositionally (`GP-canonical`).
- **Presentation.** Word bracketing is repeated: `wordE`, `wordStr`, `wposW`, `_⧀*⟨_,_⟩`, `world-⧀*`, `keepW`, `liftWS`, `dropW`, `wsW`, `closeK` and `shutW` each have three clauses (`[]`, `[ κ ]`, `κ ∷ μ`), the price of read-back by `refl`. Used raw, `op` gives an unlocked slot an ignored binder.
- **Check time.** A clean check takes about 410 s of the 600 s cap; the weighted monoid alone takes about 170 s. A further large instance would need the index split.
- **Not here yet.** Adequacy; weighted-monoid affinity (deferred by user decision); list nondeterminism with the monoid equations and a generic free model with equations; presented free models at a non-trivial `W`; comodels and branching monads (`Semantics/Branching.agda` defines branching monads, no machine uses them); Max New's stack-homomorphism property of `newx`; exchange of fresh names; runners for theories with equations; `earlierIso` as a presheaf isomorphism and local state's lock as a Day convolution; `ExpClosed` at a general `W` (a sufficient condition on equations, or the counterexample); monad containers (POPL's D15) and the combination of effects by distributive laws.

## The development in detail

The rest of this page describes the development module by module, with the names of the main definitions and the paper-style numbering (Prop 1.1, Thm 5.1, …) used in the comments of the code.

### Summary

The table lists what is proved.

| Part | What is proved | Files |
|---|---|---|
| Syntax | telescopes with locks, structural renaming and substitution, the RMR polynomial with its strength | `Syntax.agda`, `Polynomial.agda` |
| Semantics | a denotation in presheaves in which a lock is a summand of the left adjoint `L_κ ⊣ R_κ`, and the adjunction is a proved hom-set bijection, natural in `Γ` | `Semantics/Lock.agda`, `Semantics/Denotation.agda` |
| Substitution lemmas | every renaming and substitution denotes a context morphism over its world map, and the denotation commutes with both | `Semantics/Renaming.agda`, `Semantics/Substitution.agda` |
| Tree reduction | β-steps and frame steps preserve the denotation | `Reduction.agda`, `Semantics/Soundness.agda` |
| Closing | closing the locks of a closed operation, for any lock word, preserves the denotation | `Closing.agda`, `Semantics/Closed.agda` |
| The machine | tree steps and effect steps (an operation is closed and run by the module in one step) preserve the denotation. The theorem is parametric: it assumes the syntactic laws `ClosedLaws`, a theory over the polynomial, a free model of that theory, a configuration container and a right module. `Metatheory/` proves `ClosedLaws` whenever `Lk` and `Base` are sets. `RunMachine` and `SelfMachine` supply the rest for equation-free theories, `PolyMachine` for free models presented by a container (the POPL instances, with their equations). | `Semantics/Machine.agda`, `Semantics/FreeModel.agda` |
| Syntactic laws | terms form sets; renaming and substitution identity, fusion and extensionality; closed computations form a presheaf and an algebra | `Metatheory/` |
| Termination | tree reduction is deterministic; a Kripke logical relation over chains of substitutions, with its fundamental lemma; every computation of type `F A` on a lock telescope, in particular every closed one, reduces to an operation tree | `Metatheory/Determinism.agda`, `Metatheory/Chain.agda`, `Metatheory/LogicalRelation.agda`, `Metatheory/Fundamental.agda`, `Metatheory/Termination.agda` |
| Equational theory | an inductive equational theory `≈` over a theory (equivalence, congruence, β and η for every connective including stack-form F-η and the lock modality, algebraicity of operations for every stack, the theory's equations), closed under substitution; a second denotation, in a free model of the theory (`F A` denotes the free model on `⟦ A ⟧`), is sound for it for every theory whose models are closed under exponentials (every theory when `W` is chaotic, e.g. `W = 1` as in POPL; every equation-free theory at any `W`); an equational logical relation with its fundamental theorem, so every computation of type `F A` on a lock telescope is `≈` to an operation tree; canonical forms denote, and are unique in the free model | `Metatheory/Equational.agda`, `Metatheory/EqSubstitution.agda`, `Metatheory/EqLogicalRelation.agda`, `Semantics/StrongTheory.agda`, `Semantics/Free/*.agda`, `Semantics/EquationalSoundness.agda`, `Semantics/EqCanonicity.agda` |
| Relating the denotations | a binary Kripke logical relation between the term-algebra and the free-model denotations, with its fundamental lemma; at a first-order result type (no `U`) the canonical algebra map from the term algebra to the free model (evaluation) carries the first denotation of every closed computation to the second, and likewise the machine's map into the free model | `Semantics/Free/Comparison.agda` |
| Tree normalization and canonicity | tree reduction is strongly normalizing on computations of type `F A` of lock telescopes (accessibility for its converse); every such computation reduces to an operation tree whose image in the free model is its free-model denotation (POPL's C8) | `Metatheory/TreeNormalization.agda`, `Semantics/TreeCanonicity.agda` |
| Canonicity of the machine | in any right module: a final configuration (a value at every hole) denotes its values; two final configurations reached from one configuration are equal when the closed denotation has a left inverse (POPL's D12); ground types (`𝟘`, `𝟙`, `⊕`, `×`, base types) have one. Under the normalization hypotheses every configuration reaches a final one, unique at a ground type. At Q = T, for `η M`, and the machine's denotation of `η M` agrees with the free-model denotation of `M` | `Semantics/Ground.agda`, `Semantics/ConfigCanonicity.agda`, `Semantics/SelfCanonicity.agda` |
| Runners | a deterministic runner gives a right module; the machine at error, global state, local state and guarded recursion, with concrete runs | `Semantics/Runner.agda`, `Semantics/RunMachine.agda`, `Instances/Machines/` |
| Normalization | if every operation has finitely many continuations, every configuration finitely many holes, and the right module is affine, then the machine is strongly normalizing, every configuration is terminal or steps, and every configuration reaches a terminal one with the same denotation | `Metatheory/TreeSize.agda`, `Semantics/Affinity.agda`, `Semantics/Normalization.agda`, `FinCount.agda`, `FinSum.agda`, `FinMax.agda` |
| Q = T with equations (parity stage H) | a free model presented by a configuration container is a right module over itself (`ρ = μ`), for any theory; the machine there: the unit configuration's denotation, final configurations and their comparison with the free-model denotation, and SN / WN / canonicity under affinity. The POPL instances at `W = 1`, each with its equations, a concrete free model, its container, `ρ = μ`, POPL's derived rules as machine steps and a run with its unique final configuration: writer (`M × X`), errors (`X + 1`), Boolean state with the four lens laws (`(Bool × X)^Bool`), all three affine, finite and so strongly and weakly normalizing with ground canonicity; the weighted monoid (weighted lists), whose affinity is deferred by user decision, so it has soundness and `final-unique` but no SN / WN / ground canonicity | `Semantics/PolySelfModule.agda`, `Semantics/PolyMachine.agda`, `Instances/Equational/` |
| Normalization at the instances | a runner's module is affine, so the machine is strongly and weakly normalizing at error, global state, local state and guarded recursion, at every result type, with ground canonicity at global state and guarded recursion; terms over an equation-free theory are a configuration container with `ρ = μ` (Q = T), affine, and the machine there is strongly and weakly normalizing, with runs for error and for list nondeterminism without the monoid equations | `Semantics/RunnerAffine.agda`, `Semantics/RunNormalization.agda`, `Instances/Normalization/`, `Semantics/SelfModule.agda`, `Semantics/SelfMachine.agda`, `Instances/SelfModule/` |

The syntactic laws take `isSet Lk` and `isSet Base` as hypotheses; `LockSig` does not assume them, and every instance proves them.

### The problem it fixes

In the old core (module `RMRCanonicity.Syntax`), judgements are `w | Γ ⊢ M` and an operation is `op o k` with `o : Shape w`. The shape is external, so in `read_i` the cell `i ∈ Fin w` is meta-level data, not a value. Two things follow:

- **A location can't be a value.** You cannot write `read x` for a variable `x : Loc`, or pass a location to a function.
- **Contexts are flat.** The syntax cannot say "x was bound before ℓ was allocated" (Max's `Γ # ℓ`), or "x is usable only after a tick" (guarded type theory).

### The idea

The RMR signature functor

```text
Ext X = Σ_o  Par_o × R_o X          Par_o = Π_{b ∈ params o} Const b
```

is a parametric right adjoint: `Ext 1 = Σ_o Par_o` is the parameter part, and over each shape the arity `R_o X (w) = Π_p X (scope w p)` is a right adjoint whose left adjoint is a **lock**. The syntax gives each part a syntactic counterpart:

| Part of `Ext` | In the syntax |
|---|---|
| the parameter part `Ext 1 = Σ_o Par_o` | base types, and `op o vs` with `vs` values |
| the locks (left adjoints) | telescopes `Θ ⧀⟨ κ , p ⟩` |
| the right adjoints of the lock kinds | modal types `[ κ ] A` |

Which right adjoints become types is a parameter, the **mode theory**. Operation arities are built from the lock kinds by composites and sums. A slot with the empty word (lookup's branches, global state) has no lock and no modal type.

The two choices are tied in one direction. The empty word has scope `w`, so a slot that changes the world needs a lock kind, and every lock kind `κ` gives a type `[ κ ] A`. So a world-changing operation always brings a modal type with it. This is standard in MTT, where every modality of the mode theory is a type former.

### The parameter (`Fam.agda`, `Signature.agda`)

**Fam W.** The free coproduct completion of `W^op`: objects are formal sums `Σ_{i∈I} y (X i)` of representables, and a map `(I , X) → (J , Y)` is `φ : I → J` with `W [ Y (φ i) , X i ]` for each `i`. `Yo : W^op → Fam W` is `w ↦ (1 , w)`.

**Strong familial arities.** A functor `E : W^op → Fam W` with a strength `str : E ⇒ Yo`, i.e. an object of the slice `[W^op , Fam W] / Yo`.

- `E w = Σ_{p ∈ Pos w} y (scope w p)` and `E f = (pos f , smap f)`, so the scope depends on the position.
- `ι w p : w → scope w p` are the strength's components (`ιOf`).
- `R_E X (w) = Π_{p ∈ Pos w} X (scope w p)` (`Arity.R`) is the right adjoint of the lock `L_E Γ = ∫^w Γ w × E w`, and `L_E (y u) = E u` (familial representability). Both are proved in `Semantics/Lock.agda`: the adjunction as a hom-set bijection natural in `Γ` (Prop 1.1), and familial representability summand by summand (Prop 1.4).

The slice has the structure the syntax and the polynomial use:

| Structure | Definition | On locks |
|---|---|---|
| unit `Yo` | `w ↦ y w` | the identity |
| composite `E ⊙ E'`, `_⊙ˢ_` | `(E ⊙ E') w = Σ_{p ∈ E w} E' (scope w p)`, `ι (p , q) = ι p ⋆ ι' q` | `L_{E⊙E'} = L_{E'} ∘ L_E` |
| sum `Σᴬ A E`, `Σˢ` | `(Σᴬ E) w = Σ_a E_a w`, `ι` by cases | coproduct |

**Layer 1: `LockSig W`, the mode theory.** Base types `b` with constants `Const b : W → Set`, and a type `Lk` of lock kinds (only the syntactic laws need it to be a set, and take that as a hypothesis). Each `κ : Lk` is a `LockKind`:

| Field | Meaning |
|---|---|
| `E : W^op → Fam W` | the arity: positions `Pos κ w`, scope `scope κ w p` |
| `str : E ⇒ Yo` | the strength `ι κ w p : w → scope κ w p` (Kripke access across the lock) |
| `names : List Base` | the types of the names the lock binds |
| `gen : Global (R_E (Π Const names))` | their generic elements, i.e. a map `L_κ 1 → Π Const` |

All laws are fields of these `Functor`, `NatTrans` and `Global` records.

**Layer 2: `OpSig L`, the operations.** These are lawless. Each operation `o` has:

| Field | Meaning |
|---|---|
| `params o : List Base` | the values it takes |
| `Ar o` (a set) | its slots (continuations) |
| `slot o a : List Lk` | the lock word slot `a` sits behind (`[]` = no lock) |

So `(Ar o , slot o)` is an object of `Fam (Lk*)`. Its meaning is the extension of `κ ↦ E κ` that preserves the unit, `⊙` and sums. It is defined on objects only, and is unique only up to isomorphism: `⊙` is associative only up to iso, and `wordE` fixes one bracketing.

- `wordE [] = Yo`, `wordE [κ] = E κ`, `wordE (κ ∷ μ) = E κ ⊙ wordE μ` (no trailing unit, so a one-lock word is `E κ` itself); `wordStr` likewise.
- `WPos μ`, `wscope μ` and `wι μ` are read off `wordE μ` and `wordStr μ`.
- `opE o = Σᴬ_{a ∈ Ar o} wordE (slot o a)` and `opStr o = Σˢ_a wordStr (slot o a)` (in `Polynomial.agda`).

Special cases:
- **Flat contexts:** no lock kinds (`Lk = ⊥`). Every slot then has the empty word, so its scope is `w` and its strength is the identity. This gives the old core's flat `w | Γ` for world-preserving (constant-arity) signatures, such as error and global state (`Instances/Constant.agda`). It is not the whole old core. There an operation may come from any RMR `Signature`: it may change the world (as local state's `new` does there), and its positions may depend on the parameter values (see Deviations and limits). A world-changing slot needs a lock kind.
- **One modality per operation:** `Lk = Op`, `Ar o = 1`, `slot o _ = [ o ]`.

### The polynomial (`Polynomial.agda`)

**Step 1 (generic, `Groth`).** A functor `G : ∫Shapes → Fam W` is the positions-and-scopes part of an RMR `Signature`, by the Grothendieck construction (`Groth.poly`). A natural transformation `G ⇒ Yo ∘ π` is a strength (`Groth.strG`).

**Step 2 (this signature).**
- `Shapes w = Σ_o Csts w (params o)` (`ShapesP`).
- `G (w , (o , cs)) = opE o w` (`GP`): forget the parameters (base change along the typing `Σ_o Par_o → Op`), then apply the arity.
- `σP` assembles the `opStr o`; `strength` is `Groth.strG ShapesP GP σP`, defined by copatterns.

Read-back, all by `refl`:

```text
Shape w                = Σ o. Csts w (params o)               shape-is
Position w (o , cs)    = Σ (a : Ar o). WPos (slot o a) w      position-is
scope w (o,cs) (a,ps)  = wscope (slot o a) w ps               scope-is     (depends on the position)
strength component     = wι (slot o a) w ps                   strength-is  (composite of the ι's)
```

On morphisms the polynomial's reindexing agrees with `pos`/`smap` of `opE o` up to the transport along the `refl` operation path (`GP-canonical`, `pos-is`, `smap-is`).

The polynomial is always written `PM.polynomial L O` (with `import …Polynomial as PM`), never under a second name. A module copy or an abbreviation is not syntactically the same term, and comparing the two unfolds the Grothendieck construction: one such equation took more than 60 s against 5 s.

### The syntax (`Types.agda`, `Syntax.agda`)

**Types.** `A ::= 0 | 1 | A + A | A × A | U B | [ κ ] A | base b` (in Agda `𝟘`, `𝟙`, `_⊕_`, `_×_`, …) and `B ::= F A | A ⇒ B`, with `⟦[ κ ] A⟧ = R_κ ⟦A⟧` and `⟦base b⟧ = Const b`. Only lock kinds give modal types.

**Telescopes.** Judgements are `Θ ⊢ M`, and a telescope computes its world (induction-recursion). `⟦Θ⟧` lives over `y (world Θ)`.

| Telescope | `world` | Meaning |
|---|---|---|
| `∅ w` | `w` | the representable context `y w` |
| `Θ , A` | `world Θ` | `⟦Θ⟧ × ⟦A⟧` |
| `Θ ⧀⟨ κ , p ⟩` | `scope κ (world Θ) p` | the `p`-summand of `L_κ ⟦Θ⟧` |

`Θ ⧀*⟨ μ , ps ⟩` iterates over a word (the word is explicit), and `world-⧀*` says its world is `wscope μ`. With no lock kinds every telescope is `∅ w , A₁ , … , Aₙ`.

**Neutrals.**

| Neutral | Meaning |
|---|---|
| `here`, `wkv` | projections |
| `up n : Ne (Δ ⧀⟨ κ , p ⟩) A` | `ε_κ ; ⟦n⟧`: reach across a lock along `ι` |
| `opn n : Ne (Δ ⧀⟨ κ , p ⟩) A`, for `n : Ne Δ ([ κ ] A)` | the counit of `L_κ ⊣ R_κ` at `p` |
| `nm k : Ne (Δ ⧀⟨ κ , p ⟩) (base b)`, for `k : names κ ∋ b` | `L_κ ! ; gen κ`: a name bound by the lock |

**Values.** `ne`, `tt`, `inl`, `inr`, `pair`, `thunk`, `const c` (a constant at the world), and `shut (λ p → V_p)` with `V_p : Val (Θ ⧀⟨ κ , p ⟩) A`.

**Computations.** `return`, `to`, `force`, `case` (on a pair), `case₊ V M N` (on a sum, `M : Comp (Θ , A) B`, `N : Comp (Θ , A') B`), `absurd V` (for `V : Val Θ 𝟘`), `lam`, `app`, and

```text
op o vs (λ a ps → M)      vs : Vals Θ (params o)
                          M  : Comp (Θ ⧀*⟨ slot o a , ps ⟩) B   for ps : WPos (slot o a) (world Θ)
```

In a closed `op o (consts cs) k`, the shape `(o , cs)` and the positions `(a , ps)` are literally those of the RMR operation. Each continuation `k a ps`, however, still lives behind its locks, in `∅ w ⧀*⟨ slot o a , ps ⟩`. It becomes a closed term at the scope `wscope (slot o a) w ps` through `Closing.closeK`, which closes any lock word, outermost lock first. `Closing.opNodeC` goes the other way: it builds an `op` from closed terms at the scopes (see Closed computations below). Stacks and `plug` are as in the old core.

**World maps.** `WMap` is `W` with a strict identity `idW` adjoined. `toW : WMap w w' → W [ w , w' ]` is its identity-on-objects interpretation; `toW-⋆`, `posW-toW` and `cmapW-toW` check that composition, `posW` and `cmapW` agree with `W`'s. The strict identity keeps weakening and same-world substitution definitionally off constants and positions. Users meet `WMap` in `root f` and in `close p f` (for example `close tt idW` in `afterNew-ℓ`).

**Renamings** `Ren Θ Θ'` are data, with the world map `wm` computed. Each constructor denotes one structure map of the semantics, a map `⟦Θ'⟧ → ⟦Θ⟧` over `y (wm ρ)`. The last column is the definition of `⟦_⟧r`, and the substitution lemma for it is proved (`Semantics/Renaming.agda`, below):

| Constructor | Type / world map | Semantics |
|---|---|---|
| `idR` | `wm = idW` | identity |
| `root f` | `Ren (∅ w) Θ'`, `wm = f` | `⟦Θ'⟧ → y (world Θ') → y w` |
| `keep`, `drop` | | `⟦ρ⟧ × id`, `π₁ ; ⟦ρ⟧` |
| `keepL ρ p` | `Ren (Δ ⧀⟨ κ , posW κ (wm ρ) p ⟩) (Δ' ⧀⟨ κ , p ⟩)`, `wm = smapW κ (wm ρ) p` | `L_κ ⟦ρ⟧` on the `p`-summand (`Lsum`) |
| `dropL ρ p` | `Ren Θ (Δ' ⧀⟨ κ , p ⟩)`, `wm = wm ρ ⋆ ι κ (world Δ') p` | `inc_p ; ε_κ ; ⟦ρ⟧` |

**Substitutions** `Sub Θ Θ'` are data, with `wmS` computed; `⟦_⟧s` is proved sound in `Semantics/Substitution.agda`:

| Constructor | Type | Semantics and action on neutrals |
|---|---|---|
| `⌜ ρ ⌝` | | `⟦ρ⟧`, a renaming |
| `σ ,ₛ V` | `Sub (Θ , A) Θ'` | `⟨⟦σ⟧ , ⟦V⟧⟩`, a value for a variable |
| `lockₛ σ p τ` | `Sub (Δ ⧀⟨ κ , posW κ (wmS σ) p ⟩) Θ'`, for `τ : Ren (Δ' ⧀⟨ κ , p ⟩) Θ'` | `⟦τ⟧ ; L_κ ⟦σ⟧` on the `p`-summand: `up n ↦ τ (↑ (σ n))`, `opn n ↦ τ (openV (σ n) p)`, `nm k ↦ τ (nm k)` |
| `close p f` | `Sub (∅ u ⧀⟨ κ , p ⟩) Θ'` | `⟦Θ'⟧ → y (world Θ') → y (scope κ u p) ≅ L_{κ,p} (y u)` (familial representability, `ν`): `nm k ↦ const (Const f (gen κ u p)_k)` |

On values these are cartesian, as Max's are. On names they are affine and order-preserving. So they match Max's substitutions restricted to order-preserving names, with no exchange. His `(ρ , ℓ' ↦ ℓ)` lets `ρ` use names after `ℓ` (`Γ − ℓ` keeps later names), which needs exchange. `lockₛ σ p τ` covers `ℓ' ↦ ℓ` when the names after `ℓ` are not used by `σ`.

**Helpers.**
- `wkV`/`wkC = ren (drop idR)`; `↑V`/`↑C p = ren (dropL idR p)` cross a lock.
- `box κ : A → [ κ ] A` is the unit coming from `ι`; `openV` is open on any value, resolving `open (shut V)`.
- `keepW` and `liftWS` lift under a word; `wkS`, `liftS`, `idS`.
- `sub₁`, `sub₂` substitute one or two variables.
- `reindexC f = renC (root (mapW f))`: closed computations form a presheaf (`Metatheory/ClosedLaws.agda`).
- `closeC p = subC (close p idW)`: closing one lock, the one-lock case of `Closing.closeK`.
- The syntactic operation node on closed computations is `Closing.opNodeC` (it supersedes the old `algC`).

### Properties (`Properties.agda`)

**Injectivity.** Every renaming has a left inverse on neutrals (`unren`, `unren-ren`, `renNe-inj`). Consequence, **freshness** (`apart`): `renNe ρ (up n) ≢ renNe ρ (nm k)`. A variable bound before a lock is never renamed to that lock's name. When renamings were arbitrary functions on neutrals (the first version), a renaming could send `x` to `ℓ`.

**Locks are never deleted.** `locks Θ` counts the locks of `Θ`, and `inner Θ` counts those not directly after the root.
- `locks-mono : Ren Θ Θ' → locks Θ ≤ locks Θ'`: no renaming deletes a lock.
- `subInner : Sub Θ Θ' → inner Θ ≤ locks Θ'`: a counting bound, so a substitution can lose at most the locks directly after the root. Only `close` removes a lock, and only one directly after the root. At the instances' telescopes (`noUnlockSub`, `noUntickSub`) the count gives exactly that statement.
- `noUndo : Ren (∅ w ⧀⟨ κ , p ⟩) (∅ w') → ⊥` is `locks-mono`. The semantic map exists, but it sends the names to constants: it is `close`, a substitution.

The instances' `noUnlock`, `noUntick`, `noUnlockSub` and `noUntickSub` are these two lemmas at particular telescopes: no renaming or substitution deletes the lock that `opn` needs.

### Instances

#### Local state (`Instances/LocalState.agda`)

`W = Inj`, and `Loc` has the constants `Fin n`. One lock kind, `fresh`:
- arity `E n = y (n + 1)` (`Efresh`);
- strength the prefix inclusion (`strFresh`);
- one name of type `Loc`, the last cell (`genFresh`).

| Operation | Parameters | Slots |
|---|---|---|
| `lookup` | `[Loc]` | `Bool`, unlocked |
| `update b` | `[Loc]` | one, unlocked |
| `new b` | none | one, behind `[fresh]` |

Two test operations beyond Max's calculus, `newIf b` (slots at `n+1` and `n`) and `new₂ b` (one slot behind `[fresh , fresh]`), are commented out in `Instances/LocalState.agda`, together with their examples, machine cases and read-backs. So no instance currently exercises per-position scope across slots or a lock word of length 2. The generic results (`Closing.closeK` for any word, `close-den`) still cover them.

| Max | Here |
|---|---|
| `read V {M_tt ∣ M_ff}`, `V := b ; M` | `read V M N`, `write V b M`: no locks in the branches |
| `Γ # ℓ` | `Θ #ℓ = Θ ⧀⟨ fresh , tt ⟩` (independent of the initial value) |
| `cell ℓ` | `ℓ = ne (nm ∋z)` |
| `new ℓ := b in M` | `newℓ b M` |
| Cartesian `new x := b in M` | `newx b M = newℓ b (subC (⌜ dropL idR tt ⌝ ,ₛ ℓ) M)` |
| `𝕃 ⊸ A` | `𝕃⊸ A = [ fresh ] A`, one modality for `new true` and `new false` |

Examples:
- Max's constructs: `passLoc` (passes `ℓ` to a function, so a later-bound `y` may be `ℓ`), `passLocx`, `before` (`x` bound before the allocation is reached with `up`), `after` (`y` bound after it is a plain variable), `generic` (`ν ℓ. ℓ : 𝕃 ⊸ 𝕃`), and `useAbs b` for every `b`. None of these examples is in Max's note; they exercise its constructs.
- `resolve`: substituting `cell i` for `x` turns `read x` into `lookup` at `cell i`.
- Closing under one lock (part of the machine's effect step): `afterNew-ℓ` (`closeC tt (return ℓ) ≡ return (cell last)`, by `refl`) and `closeRead`.
- `freshness` (via `apart`), and `noUnlock` / `noUnlockSub`: no renaming or substitution deletes the fresh lock that `opn` needs to open `x : 𝕃 ⊸ 𝕃`.
- (Commented out with `newIf` / `new₂`: `readNew`, `readNewEx`, `new₂ℓ`, `twoCells`, `afterNew₂`, `afterNew₂-cells`.)

#### Guarded (`Instances/Guarded.agda`)

`W = ω^op` (`Omega`: a map `n → m` is `m ≤ n`). One lock kind, `tick`:
- no position at 0; at `n + 1` one position, with scope `n` (`Etick`);
- strength `n + 1 → n` (`strTick`);
- no names.

Positions and maps between them are propositions, so its laws are free (`isPropTickHom`). One operation, `step`, with one slot behind `[tick]`. The terms:
- `▸ A = [ tick ] A` and `next = box tick`;
- `delay M = op step []ᵥ (λ _ p → ↑C p M)`;
- `later V = op step []ᵥ (λ _ p → force (openV V p))`, and `_⊛_`.

Checks:
- `openLater`: `x : ▸ A` opens behind a tick.
- `noOpenWithoutTick`: in `∅ n , x : ▸ A` every neutral has type `▸ A`, for every `A`, so without a tick nothing of the opened type is reachable from `x`.
- `tick-world` (`refl`): behind a tick at `n + 1` the world is `n`.
- `delay₀`: at world 0, `delay M ≡ op step []ᵥ (λ _ ())` (no tick, so `M` is dropped); `next₀`: `next tt` is trivial at 0.
- `next-open` (`refl`): opening `next V` is `V` moved across the tick.
- `noUntick` / `noUntickSub`: no renaming or substitution deletes the tick that `opn` needs.
- `noTimeTravel`: no renaming moves a variable from before a tick to after it.

`fix` is deliberately absent.

#### Constant signatures (`Instances/Constant.agda`)

`noLocks W` has no base types and no lock kinds; `constOps` makes every slot unlocked. So there are no modal types and no locks, and every telescope is flat (`GlobalState.flat`): the old core's flat `w | Γ`, which suffices because these signatures keep the world. Examples: error (`Error.raiseC`) and Boolean global state (`GlobalState.toggle`, and `getThen`, which uses `ne here` under `get` without `up`).

#### Polynomials (`Instances/Polynomials.agda`)

The polynomials with strength for local state, guarded and global state, stated at `Strength L O (polynomial L O)`. Read-back by `refl`:
- `newScope` (`n + 1`) and `newStrength` (the prefix inclusion, i.e. `ι fresh`);
- `lookupScope` (`n`);
- (commented out with the test operations: `newIfScope`, `new₂Scope`, `new₂Strength`);
- `noStepAt0`.

### The semantics (`Semantics/`)

**Setting** (`Semantics/Presheaf.agda`). `𝒱 = [W, Set]` (`𝒱`, elements `El X w`), with `y w = W(w, −)` (`Y`; `Ymap f` is precomposition), `fromFun`, `yoneda`, and the exponential `Exp G Q w = 𝒱(y w × G, Q)` with `λExp` and `appExp`. `Env w G = y w × G` and `reWorld` move an environment along a world map.

#### The lock of a strong familial arity (`Semantics/Lock.agda`)

The module is parametrised by an arity `E` and its strength. From the arity: `ι`, `pos-id`, `smap-id`, `pos-seq`, `smap-seq` and `ι-nat` (the strength's naturality: `ι (pos f p) ; smap f p = f ; ι p`).

| Object | Definition | Agda |
|---|---|---|
| right adjoint | `R X w = Π_{q ∈ Pos w} X (scope w q)` | `R`, `Rmap` |
| the lock | the coend `L Γ = ∫^v Γ v × E v`. At `t` it is the set quotient of the points `⟪ v , q , g , e ⟫` (`q ∈ Pos v`, `g : scope v q → t`, `e ∈ Γ v`) by `⟪ v , q , g , Γ f e ⟫ = ⟪ v' , pos f q , smap f q ⋆ g , e ⟫` for `f : v' → v` | `Raw`, `Shift` (constructor `shift`), `LEl`, `pt`, `L`, `Lmap` |
| the two transposes | `unlock φ ⟪ v , q , g , e ⟫ = X g (φ e q)` for `φ : Γ → R X`; `transpose ψ e q = ψ ⟪ v , q , id , e ⟫` for `ψ : L Γ → X` | `unlock`, `transpose` |
| the strength as a map out of the lock | `box e q = Γ (ι v q) e`, and `ε = unlock box`, so `ε ⟪ v , q , g , e ⟫ = Γ (ι v q ; g) e` | `box`, `ε` |
| the lock of `y w` | `Ey w = Σ_p y (scope w p)`; `genE w : y w → R (Ey w)`, `h ↦ λ q. (pos h q , smap h q)` | `Ey`, `genE`, `Epull` |

**Over a world** (`module Over π`, for `π : Γ → y w`):

| Object | Definition | Agda |
|---|---|---|
| where a point lies | `Lπ = unlock (π ; genE w) : L Γ → Ey w` | `Lπ` |
| the `p`-summand | `Summand p t = { (x , k) ∈ L Γ t × W(scope w p , t) ∣ Lπ x = (p , k) }`, the pullback of `Lπ` along the `p`-th injection (the condition is a proposition). It lies over `y (scope w p)` by `πS (x , k) = k`, and `inc (x , k) = x` | `SumEl`, `summand≡`, `Summand`, `inc`, `πS` |
| copairing | `copair φ x = φ_{fst (Lπ x)} (x , snd (Lπ x) , refl)` | `copair-ob`, `copair` |
| R's introduction | `shut φ e q = φ_{pos (π e) q} (inj e q)`, with `inj e q = (⟪ v , q , id , e ⟫ , smap (π e) q)` | `inj`, `shut` |
| familial representability | `ν_p : y (scope u p) → Summand_p (y u)`, `k ↦ (⟪ u , p , k , id ⟫ , k)` | `ν` |
| `L` on a map over `f : w → w'` | `Lsum : Summand_p Γ → Summand_{pos f p} Δ`, `(x , k) ↦ (L α x , smap f p ; k)` | `Lsum` |

What is proved:

| | Statement | Agda |
|---|---|---|
| Prop 1.1 (adjunction) | `unlock` and `transpose` are mutually inverse, and `unlock (α ; φ) = L α ; unlock φ` (naturality in `Γ`). Naturality in `X`, `unlock (φ ; R g) = unlock φ ; g`, follows from `g`'s naturality but is not stated as a lemma | `unlock-transpose`, `transpose-unlock`, `unlock-Lmap` |
| Prop 1.2 (`L Γ` is the sum of its summands) | `inc_p ; copair φ = φ_p`; and `copair φ x = φ_p (x , k , r)` for ANY witness `r : Lπ x = (p , k)` | `copair-β`, `copair-at` |
| Prop 1.3 (R's introduction) | `shut φ = transpose (copair φ)`; β: `inc_p ; unlock (shut φ) = φ_p`; η: `shut (λ p. inc_p ; unlock ψ) = ψ` | `shut-is`, `open-shut`, `shut-open` |
| Prop 1.4 (familial representability on summands) | `ν_p` and `πS_p` are inverse | `πS-ν` (`refl`), `ν-πS` |
| Prop 1.5 (the structure maps) | `unlock (φ ; box) = ε ; φ`; `π (ε x) = ι w p ; k` on `Summand_p`; `ε` is natural; `Lsum` lies over `E f`; Prop 1.1's naturality pointwise; β pointwise | `unlock-box`, `ε-over`, `ε-Lmap`, `Lπ-Lmap`, `unlock-Lmap-at`, `open-shut-at` |

Every map out of a lock that the syntax uses is an `unlock`: `ε = unlock box` for `up`, `unlock ⟦n⟧` for `opn`, `unlock names` for `nm`. So every substitution-lemma case for a lock is one of the facts above.

#### Algebras (`Semantics/Algebra.agda`)

For an RMR signature `P` with a strength (here always `PM.polynomial L O` and `PM.strength L O`):

- `Ext X = Poly.Extension P X`, `ι w o p` the strength at a position, and `strength : Ext X × A → Ext (X × A)`, `((o , k) , a) ↦ (o , λ p. (k p , A (ι p) a))`: an argument is carried into every continuation's world.
- The exponential algebra `expAlg A B`. Its carrier is `Exp A |B|`, and its structure is the curry (`expMap`) of

  ```text
  Ext(Q^A) × A --strength--> Ext(Q^A × A) --Ext ev--> Ext Q --α_B--> Q
  ```

  It is opaque (`expAlgebra`), with its unfolding `expAlgebra-ob`; `expAlgebra-id` is the case of the identity world map.
- `η X = var : X → T X`, and `bind G A B N : T A × G → |B|`, the Kleisli extension of `N : G × A → |B|`. It evaluates the term into the power algebra `B^G` with variables sent to the curry of `N` (`bindEnv`), and applies the result at `(id , γ)`. `bind` is opaque and used only through `bind-η` (`bind (var a , x) = N (x , a)`), `bind-op` (an operation node passes through, the environment moved along `ι`) and `bind-pre` (changing the environment along a map; proved with `evalPre`).
- `tpos`, `smapP`: the extension's positions and scope maps at a canonical lift.

#### Types, telescopes and terms (`Semantics/Denotation.agda`)

`K κ` is the lock module at `E κ`, and `KW μ` the one at `wordE μ`. Each syntactic construct denotes:

| Syntax | Meaning | Agda |
|---|---|---|
| `1`, `A × A'`, `base b` | terminal, product, `Const b` | `⟦_⟧v`, `Cst`, `Par` (parameter lists), `pick-cmaps` |
| `0`, `A + A'` | the initial presheaf, the coproduct (both pointwise) | `EmptyPsh`, `_⊎Psh_` (`Semantics/Presheaf.agda`) |
| `[ κ ] A` | `R_κ ⟦A⟧`, the right adjoint | `K.R` |
| `U B` | the carrier of `⟦B⟧` | `⟦_⟧u` |
| `F A` | the term algebra `T_P ⟦A⟧`, free with no equations | `⟦_⟧c` |
| `A ⇒ B` | the exponential algebra, built from `P`'s strength | `expAlg` |
| a telescope `Θ` | a presheaf over `y (world Θ)`: `π_Θ : ⟦Θ⟧ → y (world Θ)` | `⟦_⟧t`, `πt` |
| `∅ w`, `Θ , A` | `y w`; `⟦Θ⟧ × ⟦A⟧` | |
| a lock `Θ ⧀⟨ κ , p ⟩` | the `p`-summand of the coend `L_κ ⟦Θ⟧` | `K.Over.Summand`, `incl` (its inclusion) |
| `here`, `wkv` | projections | `⟦_⟧ne` |
| `up n` | `inc_p ; unlock (⟦n⟧ ; box)`, which is `inc_p ; ε ; ⟦n⟧` | |
| `opn n` | `inc_p ; unlock ⟦n⟧`, the counit | |
| `nm k` | `inc_p ; unlock (names κ k)`, the generic elements `gen κ` | `namesR` |
| `const c` | `π_Θ ; ŷ c` (Yoneda) | `⟦_⟧V` |
| `shut V` | `shut (λ p. ⟦V p⟧) = transpose ∘ copair` | `K.Over.shut` |
| `tt`, `pair`, `thunk M` | the evident ones; `⟦thunk M⟧ = ⟦M⟧` | `⟦_⟧Vs` for lists |
| `return V`, `M to N` | `⟦V⟧ ; η`; `⟨⟦M⟧ , id⟩ ; bind ⟦N⟧` | `⟦_⟧C` |
| `force`, `case`, `lam`, `app` | identity, reassociation, curry, evaluation | |
| `inl V`, `inr V` | `⟦V⟧` followed by the injection | `inlPsh`, `inrPsh` |
| `case₊ V M N` | `⟨ id , ⟦V⟧ ⟩ ; [⟦M⟧ , ⟦N⟧]`, the copairing in context (presheaves are distributive) | `casePsh` |
| `absurd V` | `⟦V⟧` followed by the map out of the initial presheaf | `EmptyPsh-rec` |
| `op o vs k` | the algebra of `⟦B⟧` at the shape `(o , ⟦vs⟧)`, on the continuations transposed through their lock words: `opNode o ⟦vs⟧ (λ a. shutW (slot o a) (λ ps. ⟦k a ps⟧)) ; α_⟦B⟧` | `opNode`, `opDen` |
| stacks | maps `⟦B⟧ × ⟦Θ⟧ → ⟦B'⟧`: `hole = π₁`, `S to• N` by `bind`, `app• S V` by evaluation | `⟦_⟧S` |

`shutW μ` is R's introduction iterated along a word. For `[]` it is `k tt ; unitR`, for `[κ]` it is `shut κ k`, and for `κ ∷ μ` it is `shut κ (λ p. shutW μ (k (p , −))) ; uncurryR`. Here `R_κ R_μ = R_{κ ⊙ μ}` and `R_[] X = X` are identities on elements (`unitR`, `uncurryR`). `opNode`'s naturality is `pos-is` / `smap-is`.

### Renamings and substitutions are context morphisms (`Semantics/Renaming.agda`, `Semantics/Substitution.agda`)

`⟦ρ⟧r : ⟦Θ'⟧ → ⟦Θ⟧` lies over the world map: `π_Θ (⟦ρ⟧ e) = toW (wm ρ) ; π_Θ' e` (`ren-over`). The two are defined mutually, because `keepL`'s map must land in the right summand. Likewise `⟦σ⟧s` and `sub-over`. The clauses are the Semantics columns of the two tables in The syntax. `keepL` uses `pos-smapW`, the bridge between `E κ` at `toW f` and the syntax's `posW` / `smapW` (`refl` at `mapW`, `pos-id` / `smap-id` at `idW`). `⟦ idS ⟧s` is the identity by definition, so there is no identity lemma.

The substitution lemma's lock cases are each one fact about the lock:

| Case | Lock fact |
|---|---|
| `up`, `opn`, `nm` under `keepL` | `unlock-Lmap-at` |
| `up` under `dropL` | `unlock-box` |
| `up` under `lockₛ` | `ε-Lmap`, `unlock-box` |
| `opn` under `lockₛ` | `openV-counit` (at `shut` it is `open-shut-at`) |
| `nm` under `lockₛ` | `unlock-Lmap-at` |
| `nm` under `close` | `Const` is a functor |
| `shut`, `op` | `copair-at` twice (`shutW-ren`, `shutW-sub`) |

What is proved, pointwise (`PshHom` has no η):

| | Statement | Agda |
|---|---|---|
| Thm 5.1 (renaming) | `⟦ renX ρ t ⟧ e ≡ ⟦ t ⟧ (⟦ ρ ⟧ e)` for neutrals, values, value lists and computations | `den-renNe`, `den-renV`, `den-renVs`, `den-renC` |
| Thm 5.2 (substitution) | `⟦ subX σ t ⟧ e ≡ ⟦ t ⟧ (⟦ σ ⟧ e)`; so `⟦ sub₁ M V ⟧ e ≡ ⟦ M ⟧ (e , ⟦ V ⟧ e)`, and likewise for `sub₂` | `den-subNe`, `den-subV`, `den-subVs`, `den-subC` (with `sub-wk`, `sub-lift`); `den-sub₁`, `den-sub₂` |
| Lemma 5.3 (β of the modality) | `⟦ openV V q ⟧ = inc_q ; unlock ⟦V⟧` | `openV-counit` |
| Lemma 5.4 | `shutW` commutes with renaming and substitution | `shutW-ren`, `shutW-sub` |

Lemma 5.4 needs no path over positions. Two summand elements with the same underlying point of the lock have the same image under a copairing, whatever their positions (`copair-at`).

### Tree reduction (`Reduction.agda`, `Semantics/Soundness.agda`)

`dropW ρ μ ps : Ren Θ (Δ ⧀*⟨ μ , ps ⟩)` crosses the locks of a word: it is iterated `dropL`, Kripke access along the word's composite strength. The head steps `_⇝_`:

```text
return V to N        ⇝  sub₁ N V                                                     β-to
force (thunk M)      ⇝  M                                                            β-force
case (pair V V') M   ⇝  sub₂ M V V'                                                  β-case
case₊ (inl V) M N    ⇝  sub₁ M V                                                     β-case₊-inl
case₊ (inr V) M N    ⇝  sub₁ N V                                                     β-case₊-inr
app (lam M) V        ⇝  sub₁ M V                                                     β-app
(op o vs k) to N     ⇝  op o vs (λ a ps → k a ps to renC (keep (dropW idR (slot o a) ps)) N)   op-to
app (op o vs k) V    ⇝  op o vs (λ a ps → app (k a ps) (renV (dropW idR (slot o a) ps) V))     op-app
```

`M ↦ M'` (`step S r`) is a head step inside a stack: `plug S M ↦ plug S M'`. `M ↦* M'` is its reflexive-transitive closure (`refl*`, `step*`) plus congruence under `op`, continuation by continuation (`op*`). Tree reduction has no close rule: it never removes the locks in front of a continuation. Closing them is a machine step.

**Crossing the locks is the strength.** Lemma 6.1 (`shutW-strength`): suppose each continuation `h' ps` uses the environment only through `dropW idR μ ps`, that is `h' ps x = g (h ps x , ⟦ dropW idR μ ps ⟧ x)`. Then

```text
shutW μ h' e ps = g (shutW μ h e ps , ⟦Θ⟧ (wι μ v ps) e)
```

So the environment arrives in the continuation moved along the word's composite strength `wι μ`. That is the polynomial's strength at the position (`strength-is`), and it is exactly what `bind` (`bind-op`) and the exponential algebra (`expAlgebra-id`) do with the environment. Hence the frame steps are sound. `dropW-split` splits `dropW ρ` into `dropW idR` followed by `ρ`.

Thm 6.2:

| Statement | Agda |
|---|---|
| `M ⇝ M'` implies `⟦M⟧ e ≡ ⟦M'⟧ e` | `sound⇝` (β: `bind-η` and `den-sub₁` / `den-sub₂`; op-to: `bind-op`, `bind-pre` and `shutW-strength`; op-app: `expAlgebra-id` and `shutW-strength`) |
| `⟦ plug S M ⟧ e ≡ ⟦S⟧ (⟦M⟧ e , e)` | `den-plug` |
| `M ↦ M'` implies `⟦M⟧ ≡ ⟦M'⟧` | `sound↦` |
| `M ↦* M'` implies `⟦M⟧ ≡ ⟦M'⟧` | `sound↦*` (`op*` is congruence of `opDen`) |

### Closed computations and closing (`Closing.agda`, `Semantics/Closed.agda`)

A closed computation lives at the root: `M : Comp (∅ w) B`. Since `⟦∅ w⟧ = y w`, by Yoneda it denotes `denClosed M = ⟦M⟧ (id_w)`, an element of `⟦B⟧` at `w`. Reindexing is `reindexC f = renC (root (mapW f))`, and Lemma 7.1 (`denClosed-reindex`) says `denClosed (reindexC f M) = ⟦B⟧ f (denClosed M)`.

An RMR operation node has closed continuations at the scopes of its positions. A closed `op o vs k` instead has its continuations behind the locks of their slots. `Closing.agda` (syntax only) goes between the two:

| Definition | What it does |
|---|---|
| `opNodeC o cs ks` | the syntactic operation node (it supersedes the old `algC`): `op o (consts cs) (λ a ps → renC (root (wsW (slot o a) (∅ w) ps)) (ks a ps))`. Here `ks a ps : Comp (∅ (wscope (slot o a) w ps)) B`, and `wsW` is the strict-identity world map from the scope to the world behind the word's locks |
| `closeVals vs` | a closed list of base values is a list of constants (a closed neutral does not exist) |
| `closeK μ K ps` | closes a continuation family behind any lock word, outermost lock first. `[]`: nothing to do; `[κ]`: `closeC p`; `κ ∷ κ' ∷ μ'`: close `κ` with `close p idW` lifted under the rest of the word (`liftWS`), then recurse. The family is read at `wposW (κ' ∷ μ') idW ps'`, exactly where the lifted substitution expects it. That position equals `ps'` only propositionally, and reading the family there means no term is transported along that equation |
| `closeOp o vs k` | `opNodeC o (closeVals vs) (λ a → closeK (slot o a) (k a))` |
| `wpos`, `wsmap` | the word's arity on maps of `W` |
| `ClosedLaws` | the syntactic facts the machine needs: `isSetComp`, `reindexC-id`, `reindexC-seq`, `reindexC-opNodeC` (proved in `Metatheory/ClosedLaws.agda`) |

What is proved (`Semantics/Closed.agda`), at `B = F A` where it matters:

| | Statement | Agda |
|---|---|---|
| Lemma 7.1 | `denClosed (reindexC f M) ≡ ⟦B⟧ f (denClosed M)` | `denClosed-reindex` |
| Lemma 7.2 | `denClosed (opNodeC o cs ks) ≡ ops (o , cs) (λ (a , ps) → denClosed (ks a ps))`, for every lock word | `opNodeC-den` (with `consts-id`, `shutW-root`) |
| Lemma 7.3 | `⟦ vs ⟧ id ≡ closeVals vs` | `closeVals-den` |
| Lemma 7.4 (familial representability at the root) | `shutW μ (λ ps → ⟦ K ps ⟧) id ps ≡ denClosed (closeK μ K ps)` | `closeK-den` (with `inj-ν`) |
| Cor 7.5 | `denClosed (op o vs k) ≡ denClosed (closeOp o vs k)` | `close-den` |

### The machine (`Semantics/Machine.agda`, `Semantics/FreeModel.agda`)

**Data.** A theory over the derived polynomial: `Equations` (fields `Equation`, `equationWorld`, `Variables`, `lhs`, `rhs`), made into an RMR theory by `theory`, whose signature is `PM.polynomial L O`. The equation-free theory is `noEquations` (`noEquations-empty`). Then a free model of the theory, an RMR indexed container `Q′` with a right module `R` of the free-model monad, and the result type `A`.

**Closed computations as an algebra** (`module WithLaws laws`, given `laws : ClosedLaws`). `CompPsh B` is the presheaf `w ↦ Comp (∅ w) B` under `reindexC`. Its operation is `opC ((o , cs) , ks) = opNodeC o cs ks`, natural by `opC-nat` (`reindexC-opNodeC`, then `pos-is` / `smap-is`). Together they give the P-algebra `CompAlg B`. Thm 8.6 (`hClosed A`): `denClosed : CompAlg (F A) → T_P ⟦A⟧` is a P-homomorphism (Lemmas 7.1 and 7.2).

**The machine** (`module Run eqs freeModel Q′ R A`). `ER` is RMR's `EffectReduction` at these data, and `freeA` is the free model on `⟦A⟧`. Let `h = hClosed A ; evaluate η : CompAlg (F A) → freeA`. Then `denote = ρ ∘ Q h` (`ER.Semantic`). A configuration (`Config`) is `Q (CompPsh (F A))`; a one-hole context (`Ctxt`) has its hole at `hole-world C`. `h-cong` and `hole-step` say that a step in the hole which `h` does not see does not change `denote`. The steps `_⟶_`:

| Step | | Sound by |
|---|---|---|
| `pure C r` | `plug C M ⟶ plug C M'` for a tree step `r : M ↦ M'` | `sound↦` (Thm 6.2) |
| `effect C o vs k` | the hole holds `op o vs k`; it is closed (parameters `closeVals vs`, continuations `closeK`) and RMR's effect step runs the closed node through the module, in one step: `plug C (op o vs k) ⟶ ER.step R (CompAlg (F A)) C ((o , closeVals vs) , closeK …)` | `close-den` (Cor 7.5), then `ER.Semantic.sound↦` (`sound-effect`) |

Closing and running are one step on purpose. As a separate step, close fired on its own output (`closeOp o vs k` is `opNodeC …`, itself an `op`), so the machine was not strongly normalizing. Now every `op` in a hole is consumed in the step that closes it. RMR's redex at the closed node is `plug C (closeOp o vs k)` definitionally.

`_⟶*_` has `done`, `_then_` and `_by-equation_`. Thm 9.1 (`sound⟶`, `sound⟶*`): `x ⟶ y` implies `denote x ≡ denote y`, and so does `x ⟶* y`. The theorem is stated inside `WithLaws laws` and `Run eqs freeModel Q′ R A`, so it is relative to those data. `Semantics/RunMachine.agda` discharges all of them for an equation-free theory and a runner (below).

**The free model of an equation-free theory** (`Semantics/FreeModel.agda`, parameters `𝒯` and a proof that it has no equations). It is the term algebra: `anyModel` (every algebra is a model), `TermModel`, `η`, `free` (extension `evaluateHom`), `unit`, and uniqueness `term-unique` by induction on terms. With `UP = FreeAdjunction.FromUniversalProperty` this gives `freeModel : FreeModel 𝒯`. Its monad is `T X = TermPsh X` with `η = var` (`unit-is-var`, by `refl`) and `μ = evaluate id`. Since `evaluate-var` holds (evaluating at the unit gives the term back), `h` is `denClosed` for an equation-free theory (`h-is-denClosed` below).

### Syntactic laws (`Metatheory/`)

These modules are syntax-only: no `Semantics` module is imported, except that the equational theory (next section) takes a theory over the polynomial, `Semantics/Machine.agda`'s `Equations`, as its parameter. Every module that needs a set of types takes `isSet Lk` and `isSet Base` as hypotheses. They are needed because `to`, `case`, `case₊` and `app` store a `ValTy`, and `nm` stores a `Base`.

**Sets** (Thm 8.1).
- `Metatheory/TypesSet.agda`: `isSetValTy`, `isSetCompTy`. Types are a retract of an indexed W-type over the two sorts (`Sort`, with `vT` and `cT`).
- `Metatheory/TermsSet.agda`: `isSet∋`; `isSetNe`, via a code `NeCode` defined by recursion on the telescope; `isSetVal`, `isSetVals` and `isSetComp`, as one indexed W-type over `Ix = val Θ A | vals Θ bs | comp Θ B`. The index need not be a set, only the labels.

**Renaming** (`Metatheory/Renaming.agda`, Thms 8.2–8.4). The theory is heterogeneous. Under `shut`, `renV ρ` reads the body at the pulled-back position `posW κ (wm ρ) q`. For `ρ = root (mapW W.id)` that is `pos κ W.id q`, which is `q` only propositionally (the arity's `F-id`); likewise `keepW μ idR ps` sits at `wposW μ idW ps`. So the renamed subterms live over different telescopes. Every theorem is therefore stated over an ARBITRARY path of telescopes `e`, with a path of terms over it.

| | Statement | Agda |
|---|---|---|
| agreement | `ρ₁` and `ρ₂` agree on neutrals and on world maps, over `e` | `Agree` (fields `on-ne`, `on-world`) |
| composite | `ρ₁` then `ρ₂` agrees with `ρ₁₂`, over `e` | `Composite` (same fields) |
| Thm 8.3 (identity) | `renX idR t ≡ t` | `ren-idV`, `ren-idVs`, `ren-idC`, from `ren-agree-idV`, `ren-agree-idVs`, `ren-agree-idC` (`Agree e ρ idR` and `t ≡[e] t'` give `renX ρ t ≡ t'`) |
| Thm 8.4 (fusion) | `Composite e ρ₁ ρ₂ ρ₁₂` and `t ≡[e] t'` give `renX ρ₂ (renX ρ₁ t) ≡ renX ρ₁₂ t'` | `ren-fuseV`, `ren-fuseVs`, `ren-fuseC` |
| Thm 8.2 (extensionality) | `Agree e ρ₁ ρ₂` and `t₁ ≡[e] t₂` give `renX ρ₁ t₁ ≡ renX ρ₂ t₂` | `ren-extV`, `ren-extVs`, `ren-extC` (fusion with `idR`, via `Agree→Composite`, then identity) |

Each proof first eliminates the telescope path and the term path together (`J-tele`), then inducts on the term. Transport is never computed on `Ne`, `Val` or `Comp`. Inside the induction the only non-trivial paths are the ones the closure lemmas build:
- `keep`: the same path, one variable further (`AgreeId-keep`, `Composite-keep`);
- `keepL`: a path of positions, built in `Ey κ w x = Σ_p W [ scope p , x ]` (the elements of `E κ w` at `x`) so that the first component moves the telescope and the second is the new world map (`AgreeId-pt`, `AgreeId-keepL`, `Composite-pt`, `Composite-keepL`; from `pt`, `ptW`, `pt-id`, `pt-seq`, `ptW-toW`, `ptW-seq`);
- `keepW`: the same along a lock word, outermost lock first (`AgreeId-pts`, `AgreeId-keepW`, `Composite-pts`, `Composite-keepW`);
- `root`: there are no neutrals out of `∅ u` (`Ne∅`, `ne∅`), so agreement is agreement of world maps (`Agree-root`, `Composite-root`).

Only agreement with the identity needs closure lemmas (`Agree-idR` and the `AgreeId-*`). The action on neutrals under `keep` and `keepL` is `liftNe,` and `liftNe⧀`; constants move by `cmapW-seq` and `cmapW-id`.

**Closed laws** (`Metatheory/ClosedLaws.agda`, Cor 8.5). `closedLaws : ClosedLaws`, with `reindexC-id` from `ren-agree-idC`, `reindexC-seq` from `ren-fuseC`, and `reindexC-opNodeC` from `renVs-consts` (the parameters) and `keepW-wsW` (each continuation; the syntactic word position `wposW μ (mapW f) ps` against the arity's `wpos μ f ps`, together with the world maps). `Metatheory/Everything.agda` instantiates it at local state (`lsClosedLaws`). So closed computations of each type form a presheaf and, with `opNodeC`, a P-algebra.

**Substitution** (`Metatheory/Substitution.agda`, `Metatheory/SubstReduction.agda`). The same method for substitutions: substituting a renaming is renaming, identity, the three fusions and extensionality (Thms 5.1–5.5), the one-variable and one-lock laws (`sub-sub₁`, `sub-↑`, `sub-openV`, `sub-dropW`, …), and tree reduction is stable under substitution (`sub-↦`).

**Determinism** (`Metatheory/Determinism.agda`). A step function `next` finds the redex through the frames of `to` and `app`; every step agrees with it (`step-next`), so `↦-det : M ↦ M₁ → M ↦ M₂ → M₁ ≡ M₂`, and `return` and `op` are normal (`ret-normal`, `op-normal`).

**Chains** (`Metatheory/Chain.agda`). Data substitutions have no composite with the right source: under a lock, `σ₁` then `σ₂` reads a body at `posW κ (wmS σ₁) (posW κ (wmS σ₂) q)`, and one substitution over the composite world map reads it at a position equal to that one only propositionally. So the Kripke structure ranges over formal composites `Chain Θ Θ'` (lists of substitutions) acting by iterated substitution (`chV`, `chC`), with their lifts `liftᶜ`, `lockᶜ`, `wordᶜ`. A chain commutes with every term former and with crossing and opening a lock (`ch-to`, …, `ch-inl`, `ch-inr`, `ch-case₊`, `ch-absurd`, `ch-op`, `ch-shut`, `ch-↑`, `ch-openV`, `ch-β`): each law is by induction on the chain, one substitution law (5.6) per step.

**The logical relation** (`Metatheory/LogicalRelation.agda`). A lock telescope (`IsLT`) is a root followed by locks only. It has no variables, but it has neutrals, the names `up^j (nm k)`, all of base type (`LT-ne`). The relation is defined at every telescope; its Kripke quantifiers range over chains into lock telescopes:

```text
𝒞⟦ F A ⟧ = Tree 𝒱⟦ A ⟧     leaf (related value) | node (related continuations) | back (anti-reduction)
𝒱⟦ U B ⟧ Θ V = ∀ Θ' lock telescope, χ : Chain Θ Θ'.  𝒞⟦ B ⟧ Θ' (force (chV χ V))
𝒱⟦ [ κ ] A ⟧ Θ V = ∀ q.  𝒱⟦ A ⟧ (Θ ⧀⟨ κ , q ⟩) (openV V q)          (R_κ)
𝒱⟦ base b ⟧ = ⊤     𝒱⟦ 𝟙 ⟧, 𝒱⟦ A × A' ⟧: canonical values, neutrals unrelated
𝒱⟦ 𝟘 ⟧ = ⊥          𝒱⟦ A ⊕ A' ⟧ Θ (inl V) = 𝒱⟦ A ⟧ Θ V,  (inr V') = 𝒱⟦ A' ⟧ Θ V',  neutrals unrelated
𝒞⟦ A ⇒ B ⟧ Θ M = ∀ Θ' lock telescope, χ, related V.  𝒞⟦ B ⟧ Θ' (app (chC χ M) V)
𝒢 χ = every neutral n goes to a related chV χ (ne n)
```

Lemma 6.5: `mono𝒱`, `mono𝒞` (along any chain), `back𝒞`, `op𝒞` (at `A ⇒ B` it uses `op-app` and moves the argument across the word's locks), `seq𝒞`, `case𝒞`, `case₊𝒞`, and the environment lemmas (`𝒢-LT`: on a lock telescope the empty chain is related; `𝒢-lock`, `𝒢-word`, `𝒢-β`, `𝒢-β₂`).

**Fundamental lemma** (`Metatheory/Fundamental.agda`, Thm 6.6). Semantic typing `⊨V V`, `⊨C M`: every related chain into a lock telescope sends the term to a related one. Each term former preserves it (`compat-ne`, `compat-tt`, `compat-inl`, `compat-inr`, `compat-pair`, `compat-thunk`, `compat-const`, `compat-shut`, `compat-return`, `compat-to`, `compat-force`, `compat-case`, `compat-case₊`, `compat-absurd`, `compat-lam`, `compat-app`, `compat-op`), so every term is semantically typed (`semV`, `semC`, which only dispatch), i.e. `fundV V l χ G : 𝒱⟦ A ⟧ Σ (chV χ V)` and `fundC M l χ G : 𝒞⟦ B ⟧ Σ (chC χ M)` for `l : IsLT Σ`, `G : 𝒢 χ`.

**Termination** (`Metatheory/Termination.agda`). `related : IsLT Θ → (M : Comp Θ (F A)) → Tree 𝒱⟦ A ⟧ Θ M` (Cor 6.7, the fundamental lemma at the empty chain). Operation trees `OpTree A Θ` (`leaf V`, `node o vs t` with `t a ps` behind the slot's locks) are the normal forms, and `treeNF` reads a `Tree` back as a reduction. Thm 6.8: `termination : IsLT Θ → (M : Comp Θ (F A)) → Σ[ t ∈ OpTree A Θ ] (M ↦* reify t)`. At the root the parameters of an operation are constants (`closeVals-consts`); behind a lock they may also be names.

### The equational theory (parity stage F)

`Metatheory/Equational.agda`, `Metatheory/EqSubstitution.agda`, `Metatheory/EqLogicalRelation.agda`, `Semantics/EquationalSoundness.agda` and `Semantics/EqCanonicity.agda` mirror the POPL formalization's `Equational`, `EquationalSoundness`, `EqLogicalRelation` and `EqCanonicity`, on telescopes with locks. Each takes a theory over the polynomial, `eqs : Machine.Equations L O`. The two semantic ones also take a free model of the theory, `fm : FreeModel (theory eqs)`, and `ec : ExpClosed eqs` (below), and are about the free-model denotation of `Semantics/Free/` (POPL's `Denotation 𝒯 fm`), not about `Semantics/Denotation.agda`, which interprets `F A` by the term algebra and is unchanged.

**The relation** (`Metatheory/Equational.agda`). As in POPL (its D4), terms stay a plain inductive type and the theory is an inductive relation on them, at every telescope: `V ≈v V'`, `vs ≈vs vs'` (parameter lists, pointwise) and `M ≈c M'`. It is an equivalence (`≈refl`, `≈sym`, `≈trans`) and a congruence for every term former (`inl≈`, `inr≈`, `pair≈`, `thunk≈`, `shut≈`, `return≈`, `to≈`, `force≈`, `case≈`, `case₊≈`, `absurd≈`, `lam≈`, `app≈`, `op≈`; `ne`, `tt` and `const` have no subterms). Its axioms are the full β/η set (POPL's D5):

| | Axiom | Agda |
|---|---|---|
| β | `return V to N = N[V]`, `force (thunk M) = M`, `case (pair V V') M = M[V, V']`, `case₊ (inl V) M N = M[V]`, `case₊ (inr V) M N = N[V]`, `app (lam M) V = M[V]` | `F-β`, `U-β`, `×-β`, `+-β₁`, `+-β₂`, `⇒-β` |
| β for `[ κ ]` | `openV (shut V) q = V q` | `[κ]-β` (by definition: `openV` resolves at `shut`) |
| η for values | `V = tt` at `𝟙`; `thunk (force V) = V`; `shut (λ q → openV V q) = V` at `[ κ ] A` | `η𝟙`, `ηU`, `η[κ]` |
| η for computations | `M[V] = absurd V` at `𝟘`; `M[V] = case₊ V M[inl x] M[inr y]`; `M[V] = case V M[pair x y]`; `lam (app (wkC M) x) = M`; `S[M] = M to S[return x]` for every stack `S` | `η𝟘`, `η+`, `η×`, `η⇒`, `ηF` |
| algebraicity | `S[op o vs k] = op o vs (λ a ps → S'[k a ps])` for every stack `S`, with `S'` the stack moved across the slot's locks (`dropW`) | `op-stack`; `op-to≈`, `op-app≈` are its one-frame instances |
| the theory | every equation of `eqs`, in closed computations, moved into any telescope along a world map | `theory` |

There are no value eliminators (no complex values), so the η laws of `𝟘`, `+` and `×` are stated for computations only (POPL's `η𝟘c`, `η+c`, `η×c`). `open≈` shows that `openV` is a congruence. Tree reduction is contained in `≈` (`⇝→≈`, `↦→≈`, `↦*→≈`): each head step is a β law, or `op-stack` at a one-frame stack.

*The theory's equations.* An equation `e` is a pair of polynomial terms at the world `equationWorld e`, over a presheaf of variables. The syntactic model of the polynomial is the closed computations with the operation node `opNodeC`. A `ClosedEnv X B` sends each variable to a closed computation, naturally in the world (fields `at` and `nat`), and `inst γ t` evaluates `t`, each node to `opNodeC`. The axiom is

```text
theory e γ g : renC (root g) (inst γ (lhs e)) ≈c renC (root g) (inst γ (rhs e))      g : WMap (equationWorld e) (world Θ)
```

that is, the equation itself (`g = idW`), or its instance at a world reached from the equation's world, in any telescope. Stating it under `root g` makes `≈` closed under substitution. POPL instantiates its equations with open computations. Here the leaves are closed: at a general `W` an environment into open computations is not a natural transformation, so `Satisfies` would not make such an instance sound. Some open instances are derivable: if the leaves are open only in variables that can be λ-abstracted into closed computations of a function type, use `theory` at that function type, then `op-app≈` and `⇒-β`. Instances whose leaves use the names a slot's lock binds (`nm`, as opposed to the constants `const`) are not derivable. `sub₁≈` (`V ≈v V'` gives `sub₁ M V ≈c sub₁ M V'`, through `⇒-β`) is derived.

**Closure under substitution** (`Metatheory/EqSubstitution.agda`). `sub≈v`, `sub≈vs`, `sub≈c` (`V ≈ V'` gives `subX σ V ≈ subX σ V'`) and, one substitution at a time, `ch≈v`, `ch≈vs`, `ch≈c` for chains. The congruences go under the lifted substitution, as `subX` does. Each other axiom is the same axiom at the substituted terms, up to a law of substitution: `sub-⇝` for the β laws, `sub-sub₁` with `sub-inlS`, `sub-inrS`, `sub-pairS` (the η substitutions commute with `liftS`; both sides fuse to one substitution) for `η𝟘`, `η+`, `η×`, `sub-liftS-wkC` for `η⇒`, `sub-openV` for `η[κ]`, `sub-plug` with `sub-wkS` for `ηF`, `sub-plug` with `sub-dropWS` (a stack moved across a word, then substituted under it) for `op-stack`, and `sub-root` (a closed term moved in by `root g` and then `σ` is moved in by `root (g ⋆W wmS σ)`) for `theory`.

**Models closed under exponentials** (`Semantics/StrongTheory.agda`). The free-model denotation interprets `M to N` in an environment `G` by extending `N` along the universal property of the free model into the exponential algebra `G ⇒ ⟦ B ⟧` (`Algebra.expAlg`: an operation acts pointwise, the argument moved into each continuation along the strength `ι`), and it interprets `A ⇒ B` by that exponential. Both need

```text
ExpClosed eqs = (G : 𝒱) (B : Algebra P) → Satisfies (theory eqs) B → Satisfies (theory eqs) (expAlg G B)
```

the strength of the free-model monad for the polynomial's strength, which sequencing in a context needs (Moggi's strong monad). POPL works at `W = 1`, where every theory has it. Here `expClosed-noEquations` gives it for an equation-free theory at every `W`, and `expClosed-chaotic` for every theory when `W` is chaotic (`Chaotic`: exactly one map between any two worlds, e.g. `TerminalCategory`). The chaotic proof reads an environment `ρ` into `G ⇒ B` at a fixed `γ : G v` as an environment `ρ^` into `B` (natural because all maps are equal) and shows that evaluation in `G ⇒ B` at `(h , γ)` is evaluation in `B` at `ρ^`, moved along `h` (`eval-chaotic`). At a general `W` it is a real condition (see Deviations and limits).

**The free-model denotation** (`Semantics/Free/`, parameters `L O eqs fm ec`). `Free/Denotation.agda` builds, from the adjunction of `fm`: the free model `T X` and its unit `η`; the extension `ext` into a model with `ext-η` and `ext-unique` (the universal property); `expModel` (the exponential model, by `ec`); `preExp` (precomposition in the environment, a homomorphism of exponentials); `bind` (opaque) with the old interface `bind-pre`, `bind-η`, `bind-op`, proved from the universal property instead of by induction on terms; and `bind-unique` (a map algebraic in its first argument is the bind of its restriction to the unit). The types are as in `Denotation.agda` except `⟦ F A ⟧m = T ⟦ A ⟧v` and `⟦ A ⇒ B ⟧m = expModel ⟦ A ⟧v ⟦ B ⟧m`, so every computation type denotes a model (`⟦_⟧m`; `⟦_⟧c`, `⟦_⟧u` are its algebra and carrier); `return` is `η`, `to` is `bind`, and every other clause is the same text. Everything independent of the types (`K`, `KW`, `Cst`, `Par`, `namesR`, `opNode`, the exponential algebra) is reused from `Denotation.agda`. `Free/Renaming.agda`, `Free/Substitution.agda`, `Free/Soundness.agda` (tree soundness: `sound⇝`, `den-plug`, `shutW-strength`, `sound↦`, `sound↦*`) and `Free/Closed.agda` (`denClosed`, `denClosed-reindex`, `opNodeC-den` at every type, `close-den`) are the old modules' proofs over this denotation.

**Soundness** (`Semantics/EquationalSoundness.agda`). `sound-v`, `sound-vs`, `sound-c`: `M ≈c M'` gives `⟦ M ⟧C .N-ob v e ≡ ⟦ M' ⟧C .N-ob v e` at every world and environment, for the free-model denotation, with no hypothesis beyond the module's `fm` and `ec`; `sound-v≡`, `sound-c≡` give equal maps of presheaves. The proof is by induction on `≈`: the β laws are `Free.Soundness.sound⇝`; `η[κ]` is `Lock.shut-open`; `η+` and `η×` are `den-sub₁` and `den-subC` at the η substitutions; `η⇒` is naturality of `⟦ M ⟧`; `ηF` and `op-stack` use `den-stack-op` (a stack denotes an algebra homomorphism in its hole) with `stack-bind` (so it is the bind of its restriction to the unit: `bind-unique`) and `shutW-strength`; `theory` uses `den-inst` (`inst` denotes evaluation in `⟦ B ⟧c`, via `Free.Closed.opNodeC-den`), `at-root` (a computation at a root is determined by its denotation at the identity) and that `⟦ B ⟧` is a model (`⟦ B ⟧m .snd`).

**The equational logical relation** (`Metatheory/EqLogicalRelation.agda`). As in POPL (its D6, D7) the predicates are written by hand and closed under `≈` by construction. As in stage B they are defined at every telescope, with Kripke quantifiers over chains into lock telescopes:

```text
𝒞⟦ F A ⟧ = FPred 𝒱⟦ A ⟧     ret (related value) | node (related continuations) | conv (M ≈c M', related M')
𝒱⟦ 𝟘 ⟧ = ⊥     𝒱⟦ 𝟙 ⟧ = ⊤     𝒱⟦ base b ⟧ = ⊤
𝒱⟦ A ⊕ A' ⟧ Θ V = Σ X. V ≈ inl X × 𝒱⟦ A ⟧ Θ X  ⊎  Σ X'. V ≈ inr X' × 𝒱⟦ A' ⟧ Θ X'
𝒱⟦ A × A' ⟧ Θ V = Σ X X'. V ≈ pair X X' × 𝒱⟦ A ⟧ Θ X × 𝒱⟦ A' ⟧ Θ X'
𝒱⟦ U B ⟧ Θ V = ∀ Θ' lock telescope, χ : Chain Θ Θ'.  𝒞⟦ B ⟧ Θ' (force (chV χ V))
𝒱⟦ [ κ ] A ⟧ Θ V = ∀ q.  𝒱⟦ A ⟧ (Θ ⧀⟨ κ , q ⟩) (openV V q)
𝒞⟦ A ⇒ B ⟧ Θ M = ∀ Θ' lock telescope, χ, related V.  𝒞⟦ B ⟧ Θ' (app (chC χ M) V)
```

Closure under `≈` is `𝒱-conv`, `𝒞-conv` (along every chain, by `ch≈`; at `[ κ ] A` by `open≈`). `mono𝒱`, `mono𝒞` give Kripke monotonicity (a `conv` is moved by `ch≈c`). `𝒞-op` is POPL's CPred condition (at `A ⇒ B` by `op-stack` at `app• hole V`), `seq𝒞` is POPL's `fund-bind` (`F-β` at a leaf, `op-stack` at a node, `to≈` at a `conv`), and `case𝒞`, `case₊𝒞` use the β laws after the value's `≈`. The environment lemmas and the compatibility lemmas are stage B's, with each anti-reduction step replaced by `conv` along the matching β law. The fundamental theorem is `fundV`, `fundC`, and

```text
related               : IsLT Θ → (M : Comp Θ B) → 𝒞⟦ B ⟧ Θ M
equational-canonicity : IsLT Θ → (M : Comp Θ (F A)) → Σ[ t ∈ OpTree A Θ ] (M ≈c reify t)
```

so every closed computation (more generally, every computation of a lock telescope) is `≈` to an operation tree whose leaves are values of lock telescopes, i.e. closed values (`canonical-form` reads a derivation back).

**Canonical forms** (`Semantics/EqCanonicity.agda`). `⌊ t ⌋ : ⟦ Θ ⟧ → T ⟦ A ⟧`, into the free model of the theory, is built from the free model's unit and operations only (`η` at a leaf, the free model's operation at a node, the continuations shut through their words), and `⌊ t ⌋₀` is its element of `T ⟦ A ⟧ w` at a root. `den-reify : ⟦ reify t ⟧C ≡ ⌊ t ⌋`. Then `canonical-form-denotes` (`M ≈c reify t` gives `⟦ M ⟧C ≡ ⌊ t ⌋`, and `denClosed M ≡ ⌊ t ⌋₀` at a root), `canonical-form-unique` (POPL's corrected C3: two canonical forms of `M` agree in the free model; the trees themselves need not, since with equations two trees can be `≈`, and `⌊_⌋` identifies them because `T ⟦ A ⟧` satisfies the theory), and `canonicity` (on a lock telescope a canonical form exists and computes `⟦ M ⟧`).

### Relating the denotations, tree canonicity, canonicity of the machine (parity stage G)

**The two denotations, related** (`Semantics/Free/Comparison.agda`, parameters `L O eqs fm ec`). `Semantics/Denotation.agda` interprets `F A` by the term algebra `T_P ⟦ A ⟧` (tree soundness, closing and the machine are about it); `Semantics/Free/Denotation.agda` by the free model `T ⟦ A ⟧` of the theory (the equational theory is about it). They differ at `U B`, hence at every type above it, and `A ⇒ B` is contravariant in `A`, so there is no map between them at every type. The standard tool is a binary Kripke logical relation, one relation per type and per telescope, each closed under the presheaf action (`monoV`, `monoC`, `monoΘ`):

```text
Rv 𝟘 = ⊥    Rv 𝟙 = ⊤    Rv (A ⊕ A')  inl ~ inl, inr ~ inr    Rv (A × A')  componentwise
Rv ([ κ ] A)  at every position      Rv (base b)  equality       Rv (U B) = Rc B
Rc (F A) = Lifted (Rv A)    var a ~ η a' for a ~ a';  ops o ts ~ the free model's node at cs, for ts ~ cs
Rc (A ⇒ B)  related arguments, at every later world, to related results
RΘ (∅ w)  equality    RΘ (Θ , A)  componentwise
RΘ (Θ ⧀⟨ κ , p ⟩)  the same map into the world, and points of the two locks with representatives
                   ⟪ v , q , g , e ⟫ and ⟪ v , q , g , e' ⟫ for related e, e'   (LRel)
```

The lock's relation is stated on representatives, so no `Type`-valued map out of the set quotient is needed: a map out of a lock is an `unlock`, which computes on a representative (`unlock-rel`), and R's introduction `shut` sends related environments to related elements at every position (`shut-rel`, moving the free side's point into the term side's summand with `copair-at`, as related environments lie over the same world map, `over`; `shutW-rel` along a word). Every `Rc B` is closed under the operations (`opsC`: at `F A` by `node~`, at `A ⇒ B` through `expAlgebra-ob` and `monoV` along `ι`), the two binds preserve the relation (`bind-rel`, by induction on `Lifted` with `bind-η` and `bind-op` on both sides), and the **fundamental lemma** `fundNe`, `fundV`, `fundVs`, `fundC` says: for related environments, the two denotations of every term are related (`related-closed` for closed computations of every type).

At a first-order type (`FirstOrder`: `𝟘`, `𝟙`, `⊕`, `×`, `[ κ ]`, base; no `U`) the relation is a function, `same : ⟦ A ⟧ → ⟦ A ⟧'` (`same-rel`), and `Lifted (Rv A)` is the graph of the **canonical algebra map** `canon : T_P ⟦ A ⟧ → T ⟦ A ⟧'`, the unique homomorphism extending `η ∘ same` (`evaluateHom`: evaluation of terms in the free model; `lift-canon`). So:

| | Statement | Agda |
|---|---|---|
| comparison | `⟦ M ⟧ ; canon = ⟦ M ⟧'` for `M : Comp (∅ w) (F A)`, `A` first-order | `comparison`, `comparison₀` (at the identity) |
| the machine's map | `Machine.Run.h` (the term-algebra denotation at the identity, evaluated in the free model on `⟦ A ⟧` at the unit; `hClosed`), followed by `T (same)`, is the free-model denotation | `relabel`, `machine-comparison` |

Tree soundness needs no transfer: `Semantics/Free/Soundness.agda` proves it for the free-model denotation directly.

**Tree normalization** (`Metatheory/TreeNormalization.agda`). `strong-normalization : IsLT Θ → (M : Comp Θ (F A)) → Acc _↤_ M`, with `M' ↤ M` iff `M ↦ M'` (POPL's D9: accessibility for the converse). A derivation of the logical relation is a chain of `back` steps ending in `return` or `op`, which do not step (`ret-normal`, `op-normal`), and `↦` is deterministic (`↦-det`), so every step is the derivation's first (`tree-acc`). POPL needs its decreasing metric (C7) because its tree reduction also reduces under `op`; here `↦` never does (only `↦*`'s `op*`).

**Tree canonicity** (`Semantics/TreeCanonicity.agda`, parameters `L O eqs fm ec`). POPL's C8:

```text
tree-canonicity : IsLT Θ → (M : Comp Θ (F A)) → Σ[ t ∈ OpTree A Θ ] (M ↦* reify t) × (⌊ t ⌋ ≡ ⟦ M ⟧C)
```

for the free-model denotation, from `termination`, `EqCanonicity.den-reify` and `Free.Soundness.sound↦*`; `tree-canonicity₀` at a root with `denClosed`. The tree `t` is the one `termination` extracts, which does not compute to a normal form by `refl` (stage E's probe); the statement does not need it to.

**Ground types** (`Semantics/Ground.agda`). `Ground` is built from `𝟘`, `𝟙`, `⊕`, `×` and base types: a closed value of base type is a constant (no neutral lives at `∅ w`) and `⟦ base b ⟧` at `w` is `Const b w`, so base types are read back from constants. `reflect : Ground A → El ⟦ A ⟧v w → Val (∅ w) A`, and `reflect-den`: `reflect g (⟦ V ⟧V at the identity) ≡ V`. `[ κ ] A` is not ground (the body of `shut` lives behind a lock and may use its names).

**Canonicity of the machine** (`Semantics/ConfigCanonicity.agda`, the machine's data: `laws`, `eqs`, `freeModel`, `Q′`, `R`, `A`). Generic in the right module:

| | Statement | Agda |
|---|---|---|
| final configurations | a shape of `Q′` with a closed value at every hole; returned at every hole; its values' closed denotations, in `Q ⟦ A ⟧` | `Final`, `retF` (POPL's `T(ret)(ṽ)`), `denF` |
| den-final | `denote (retF ṽ) ≡ denF ṽ`: a returned value denotes `η` of its value and `ρ ∘ Q η = id` is the module's unit law, so it holds in any right module | `den-final` |
| D12 | given a left inverse `r` of the closed denotation at `A`, two final configurations reached from one configuration are equal (machine soundness, then `Q r`); no affinity needed | `final-unique` |
| existence | under `finOp`, `finQ`, affinity (module `WithAffinity`): every configuration reaches a final one | `terminal-final`, `normalize` (POPL's `normalize-T`) |
| ground canonicity | at a ground type, a unique one | `ground-canonicity` |

At Q = T (`Semantics/SelfCanonicity.agda`, the data of `SelfMachine`): `canonicity-T` (POPL's: `η M` reaches some `retF ṽ`), `ground-canonicity-T`; `denote-ηC` (by `refl`: the machine's denotation of `η M` is the term `h M`) and `denote-ηC-free` (at a first-order type, followed by `Q (same)`, it is the free-model denotation of `M` for the equation-free theory, through `machine-comparison`). `Semantics/RunNormalization.agda` re-exports the generic results at every runner. Instances: `state-ground-canonicity`, `guarded-ground-canonicity` (and `state-sn`, `state-wn`, `guarded-sn`, `guarded-wn` now at every result type), the uniqueness of the runs' final configurations `toggle-unique`, `toggle-false-unique`, `delay-delay-unique`, and at Q = T for error `error-ground-canonicity-T`, `error-denote-free`.

### Runners and instances (`Semantics/Runner.agda`, `Semantics/RunMachine.agda`, `Instances/Machines/`)

**A deterministic runner** is effect data for an equation-free theory. It consists of states `S w` at each world, halting outcomes `H`, and a transition

```text
δ : S w → (o : Shape w) → H ⊎ Σ (p : Position w o). S (scope w o p)
```

At an operation node, δ either halts or picks a position and the next state, at that position's scope (so nothing is transported). From it, `Semantics/Runner.agda` builds:

| | Definition | Agda |
|---|---|---|
| the configuration container | shapes `(Σ_w S w) ⊎ H`; a running shape `(w , σ)` has one hole at `w`, a halted shape none: `Q X = Σ_w S w × X w + H` | `RunQ′`, `Conf`, `running`, `halted` |
| running a term | `run σ (var x) = running σ x`; at `ops o k`, `δ σ o` decides: halt with `h`, or `run σ' (k p)` | `run`, `Outcome`, `continue` (a non-`with` helper), `next`, `continue-map` |
| the right module | `ρ_X ((w , σ) , t) = run σ t`, `ρ_X h = h` | `act`, `ρ` |
| Thm 10.1 | `(RunQ′ , ρ)` is a right module of the term monad: naturality is `run-natural` and associativity `run-assoc`, both by induction on terms; the unit law holds by computation | `runnerModule` |
| the effect step at a running configuration | RMR's effect step on any P-algebra's operation steps to `next σ o k` | `effect-at` (with `context`, `plug-context`, `plug-mapped-context`) |

The module is natural in `X`, not in worlds, so the polynomial's reindexing (`pos-is` / `smap-is`) never enters. `ER` is RMR's `EffectReduction` at `RunQ′`.

**The machine at a runner** (`Semantics/RunMachine.agda`, parameters `L O isSetLk isSetBase S H isSetConf isSetH δ A`). It opens `Run` at the equation-free theory, its free model, `RunQ′` and `runnerModule` (`Rn` is the runner module), with the proved `closedLaws`. Configurations are `running σ M` and `halted h`; `next σ o cs ks` is what δ makes of an operation node. The derived rules:

| Rule | Statement |
|---|---|
| `pure-at` | `M ↦ M'` gives `running σ M ⟶ running σ M'` |
| `op-step` | the machine's effect step at a running configuration: `running σ (op o vs k) ⟶ next σ o (closeVals vs) (closeK on every slot)` |
| `op-at` | `op-step` as a run (`⟶*`) |
| `_then*_` | runs compose |

Corollaries of Thm 9.1 (Cor 10.2): `denote-running` (`denote (running σ M) = run σ (h M)`, by `refl`); `h-is-denClosed` (`h M = denClosed M`); and

| | Statement |
|---|---|
| `run-return` | `running σ M ⟶* running σ' (return V)` implies `run σ (denClosed M) ≡ Rn.running ⟦A⟧ σ' (⟦V⟧ id)` |
| `run-halt` | `running σ M ⟶* halted h` implies `run σ (denClosed M) ≡ Rn.halted ⟦A⟧ h` |

So every machine run from a closed program that returns or halts ends where the runner ends when it runs the program's denotation.

**The instances.** Each file gives `isSet` proofs for `Lk` and `Base`, the runner (`S`, `H`, `δ`, `isSetConf`), and the runs. `P` is the polynomial's notation (`Shape`, `Position`, `scope`).

| Instance | `W` | `S w` | `H` | `δ` | `Q X` |
|---|---|---|---|---|---|
| Error (`Instances/Machines/Error.agda`) | 1 | 1 | 1 (raised) | `raise` halts | `X tt + 1` |
| Global state (`Instances/Machines/GlobalState.agda`) | 1 | `Bool` | `⊥` | `get`: continue in slot `s`, same state; `put b`: continue, state `b` | `Bool × X tt` |
| Local state (`Instances/Machines/LocalState.agda`) | `Inj` | `Store n = Fin n → Bool` | `⊥` | `lookup c`: slot `σ c`; `update b c`: overwrite `c`; `new b`: continue at `n + 1` with a new cell `b` | `Σ_n Store n × X n` |
| Guarded (`Instances/Machines/Guarded.agda`) | `ω^op` | 1 | 1 (timeout) | `step` at `n + 1`: continue at `n`; at 0: halt | `(Σ_n X n) + 1` |

Local state needs no Plotkin-power reassociation, because the runner reads the child at `n + 1` directly. Closing `new`'s lock with `close tt idW` turns the name `ℓ` into the constant `freshCell n`, the cell the runner has just initialised (`init b` is the new cell's store).

The runs, their corollaries (`run-return` / `run-halt`), and the same equations computed by `refl` independently of the machine:

| Instance | Run | Corollary | By `refl` |
|---|---|---|---|
| Error | `raise-to : running tt (raiseC to N) ⟶* halted tt` (pure `op-to`, then the fused effect step `op-at`) | `raise-to-halts` | none (`⟦ to ⟧` is the opaque `bind`) |
| Global state | `toggle-run : running true toggle ⟶* running false (return tt)`, and `toggle-run-false` from `false` | `toggle-run-sound`, `toggle-run-false-sound` | `toggle-run-den`, `toggle-run-false-den` |
| Local state (`ReturnsLoc`) | `alloc-write : running {0} emptyStore allocWrite ⟶* running {1} σ₁ (return (cell (freshCell 0)))` | `alloc-write-sound` | `alloc-write-den`; probe `newRet` |
| Guarded | `delay-delay : running {2} tt (delay (delay (return tt))) ⟶* running {0} tt (return tt)`; `delay-delay-timeout`: from `{1}` it ends `halted tt` | `delay-delay-sound`, `delay-delay-timeout-sound` | `delay-delay-den`, `delay-delay-timeout-den`; probe `delayRet` |

Every run is `op-at then* op-at`, one `op-at`, or a `pure-at` followed by `op-at`. Their normalization corollaries are in `Instances/Normalization/` (below). No `_by-equation_` is needed, because the closed continuations are only ever applied, never compared as functions. `allocWrite = newℓ false (write ℓ true (return ℓ))`; `σ₁`, `σ₂`, `c₀` and `c₁` are the expected stores and cells. The other per-instance names are the isSet proofs `isSetLk`, `isSetBase`, `isSet⊥`, `isSetLSLk`, `isSetLSBase`, `isSetGLk` and `isSetGBase`.

**The guarded lock is the earlier modality** (`Semantics/GuardedLock.agda`). On an instance the coend collapses to the evident functor. For `tick`, `earlierIso : L_tick Γ t ≅ Γ (t + 1)`, with `earlier` and `later` its two directions and `earlier-nat` the naturality of `earlier`. Every point `⟪ v + 1 , tt , g , e ⟫` is identified with `⟪ t + 1 , tt , id , Γ (v + 1 → t + 1) e ⟫`.

### Normalization of the machine (`Semantics/Normalization.agda`)

**The theorem.** Take the machine's data: the syntactic laws, a theory over the polynomial with a free model (monad `T`), a configuration container `Q′`, a right module `R` (`ρ : Q ∘ T ⇒ Q`), and the result type `A`. Assume

| Hypothesis | Meaning | Agda |
|---|---|---|
| `finOp` | every operation has finitely many continuations at every world: `Σ a. WPos (slot o a) w` is a finite set | `isFinSet` |
| `finQ` | every configuration shape has finitely many holes, with a chosen numbering | `isFinOrd (Pos s)` |
| `aff` | the module is affine: at every generic redex, distinct holes of the result have distinct origins (below) | `Affinity.ModuleAffine R` |

Then:

| | Statement | Agda |
|---|---|---|
| C.1 | every step lowers the measure: `x ⟶ y` implies `measure y ⊏ measure x` | `decrease` |
| C.2 | every configuration is strongly normalizing: there is no infinite run | `strongNormalization : ∀ x → Acc (λ y x → x ⟶ y) x` |
| C.3 | a configuration is terminal when every hole returns a value; every configuration is terminal or steps | `Terminal`, `progress` |
| | every configuration reaches a terminal one, and the denotation is unchanged | `weakNormalization`, `wn-sound` |

`progress` picks the first hole, in `finQ`'s numbering, whose derivation (below) is not a leaf: a `back` step is a pure step, a `node` an effect step. `weakNormalization` iterates `progress`, which terminates by C.2.

**Affinity, read off the module** (`Semantics/Affinity.agda`; nothing in it is specific to PRACBPV). Fix a shape `s`, a hole `p` and an operation `o` at `p`'s world. The *sources* of a redex are the other holes `r ≠ p` and the positions `q` of `o`, each at its world. `Gen` is the coproduct of the representables at the sources, and the *generic redex* fills every source with its own generator. Its step (`generic`) is a configuration of `Gen`: a shape (`composite`), and at each hole an element of `Gen`, that is a source (`origin`) and a world map out of it (`moved`). By naturality of `ρ` (Yoneda), every actual step is the generic one renamed along the map that sends a generator to its filler (`represent`): each hole of the result holds its origin's filler, moved along `moved`. `ModuleAffine` asks that `origin` be injective at every generic redex, so no step copies a filler; fillers are moved, dropped or new. A module whose configurations have at most one hole is affine (`affine-subsingleton`).

**The measure.** Every closed computation `M : Comp (∅ w) (F A)` has a derivation of the logical relation (`related`), and by determinism all its derivations have the same height `sz M` (`Metatheory/TreeSize.agda`: a leaf is 0, `back` adds 1, a node is 1 + the largest of its continuations; `size-unique`). A configuration is measured by the multiset of the heights of its holes, written as a counting function `count n = #{holes of height ≥ n}` (`FinCount.agda`). The order is the standard top-down comparison: `G′ ⊏ G` iff for some `m`, `G′ m < G m` and `G′ n ≤ G n` for all `n > m`. It is well founded on counting functions that vanish above a bound (`⊏-vanishing-acc`); on finite multisets of ℕ it agrees with the Dershowitz–Manna order (a remark, not formalised).

- A pure step lowers its hole's height by one (`sz-step`) and leaves the others (`count-update`).
- An effect step replaces the hole's `op o vs k`, of height `h`, by holes that come from sources, injectively (affinity). A source is another hole, whose filler is only reindexed, which cannot raise a height (`sz-reindex`), or a continuation, closed and reindexed, of height below `h` (`sz-cont`). So one element of the multiset is replaced by smaller ones and the others are moved injectively without growing (`count-replace`).

Neither case needs the module to keep the number of holes, or its world maps to be bijective on positions. That is why the size is a height and not a node count (substitution can repeat or drop continuation positions), why the measure is a multiset and not a sum (one hole of height `h` becomes several of height below `h`), and why RMRCanonicity's position-transport hypothesis `te` is not needed (reindexing only has to not raise a height). The derivation is used through the opaque `rel = related lt∅`, so the fundamental lemma is never unfolded during conversion.

### Normalization at the instances (`Instances/Normalization/`, `Instances/SelfModule/`)

#### Runners

A runner's configurations have at most one hole: a running shape one, a halted shape none. So its module is affine and has finitely many holes, for any equation-free theory (`Semantics/RunnerAffine.agda`: `runner-affine` by `affine-subsingleton`, `runner-finQ`). `Semantics/RunNormalization.agda` takes `RunMachine`'s data and `finOp`, and gives `strongNormalization`, `progress`, `weakNormalization` and `wn-sound` at the runner, and re-exports the canonicity results of `ConfigCanonicity` there (`Final`, `retF`, `den-final`, `final-unique`, `normalize`, `ground-canonicity`). It re-exports `RunMachine`, and the terminal configurations are `running σ (return V)` (`running-terminal`) and `halted h` (`halted-terminal`).

| Instance | `finOp` | Normalization | Runs ending terminal |
|---|---|---|---|
| Error | `raise` has no continuations | `error-sn`, `error-wn` | `raise-to-normal` (from `raise-to`) |
| Global state | `get` two, `put b` one | `state-sn`, `state-wn` (every `A`), `state-ground-canonicity` | `toggle-normal`, `toggle-false-normal`; unique: `toggle-unique`, `toggle-false-unique` |
| Local state | `lookup` two, `update b` and `new b` one | `local-sn`, `local-wn` | `alloc-write-normal` |
| Guarded | `step` one at `n + 1`, none at 0 | `guarded-sn`, `guarded-wn` (every `A`), `guarded-ground-canonicity` | `delay-delay-normal`, `delay-delay-timeout-normal`; unique: `delay-delay-unique` |

The runs are the ones of `Instances/Machines/`; each is paired with the terminal configuration it ends in.

#### Q = T: configurations are terms (`Semantics/SelfModule.agda`)

This is the POPL setting, for an equation-free theory with signature `P` (so `T X` = terms over `X`). Assume the worlds form a set and the operations' positions are discrete. Terms form an RMR configuration container `TermQ′`:

| | Definition |
|---|---|
| shapes | `Σ_w Term P 1 w`: a world and a term with no data at its variables (`1` the terminal presheaf `𝟏`) |
| positions | `Leaf t`, the leaves (variable occurrences) of `t`, defined by recursion on `t`; discrete (`discreteLeaf`) |
| input | `leafWorld t l`, the world of the leaf |

So `Q X ≅ Σ_w T X w` (`confIso`): a term splits into its shape and the variables at its leaves (`fromTerm` = `shape` and `leafVar`, inverse `toTerm` = `assemble`). A configuration of terms is a term whose leaves hold terms, and the action substitutes them: `ρ_X ((w , t) , f) = fromTerm (w , μ (t with f at its leaves))` (`graft`, `act`; `ρ-is-μ`). The module laws are the monad laws, read through the isomorphism (`conf-ext`: configurations are equal when their terms are): naturality `graft-map` / `assemble-map`, unit `graft-unit`, associativity `graft-assoc`. This is `selfModule : RightModule T Q`.

**It is affine** (`self-affine`). At the generic redex, the hole `p` of `t` holds the operation node `o` over the fresh generators `inr q`, and every other leaf `r` holds its own generator `inl r`. A leaf of the grafted term is a leaf `l` of `t` followed by a leaf of what `l` holds (`split`, with inverse `unsplit`), and it holds that leaf's generator (`split-at`). The generators are pairwise distinct (`Σ-inj`: a map out of a Σ type that is injective on each fibre and remembers the base point is injective), so the origins of the result's holes are distinct. If every operation has finitely many positions, numbered, so does every term (`finLeaf`, `self-finQ`).

**The machine at Q = T** (`Semantics/SelfMachine.agda`). Data: `L`, `O`, `isSet Lk`, `isSet Base`, `isSet` of the worlds, the result type `A`, and `finCont : ∀ o w → isFinOrd (Σ a. WPos (slot o a) w)` (finitely many continuations, numbered). From `finCont` it derives discrete positions, `finOp` and `finQ`, so `Normalization` applies: `strongNormalization`, `progress`, `weakNormalization`, `wn-sound`. Configurations and rules:

| | Statement |
|---|---|
| `ηC M` | `η M`: one leaf, holding `M` |
| `nodeC o cs ks` | one operation node, its leaves holding the threads `ks` |
| `pure-root` | `M ↦ M'` gives `ηC M ⟶ ηC M'` |
| `op-root` | `ηC (op o vs k) ⟶ nodeC o (closeVals vs) (closeK on every slot)`: the operation becomes the configuration's node, its continuations new threads |
| `pure-in`, `op-in` | the same at any leaf `p` of any configuration (the target of `op-in` is RMR's step, to be read off with `conf-ext`) |

**Instances** (`Instances/SelfModule/`), both on `W = 1` with no locks:

| Instance | Signature | Normalization | Runs |
|---|---|---|---|
| Error | `raise`, no continuations | `error-sn`, `error-wn` | `raise-run : ηC raiseC ⟶* raised` and `raise-to-run : ηC (raiseC to N) ⟶* raised` (a tree step, then raise), where `raised` is the term `raise`: one node, no leaves; `raise-normal`, `raise-to-normal`, `raise-run-sound` |
| List nondeterminism, no equations | `or` (continuations `Bool`), `fail` (none) | `list-sn`, `list-wn` | `orFail-run : ηC (or (return tt) fail) ⟶* orFailDone`, in two effect steps (`op-root`, then `op-in` at the second leaf); `orFailDone` is the tree `or(thread returning tt, fail)`; `orFail-normal`, `orFail-run-sound` |

Without equations the free model is binary trees with `or` nodes, `fail` leaves and variables: `or` is not associative and `fail` is not its unit. A configuration is such a tree whose leaves are threads; `or` in a thread splits it into two, `fail` ends it. RMR's list configurations (`Q = T = List`, `ρ = concat`) are the quotient by the monoid equations. Their free model is a higher inductive type, and **list with the monoid equations is out of scope here**: no free model of a theory with equations is built.

### Q = T with equations: the POPL instances (parity stage H)

POPL's operational model is `Q = T` for a free model that is a polynomial, `T X = ⟦ p ⟧ X`, with the action `μ`. Here that is two generic modules and four instances.

**`ρ = μ` for a presented free model** (`Semantics/PolySelfModule.agda`; any `W`, any theory, a free model `fm`, a container `Q′` and a world `w₀`). A `Presentation` is a natural isomorphism `to : Q X → T X w₀`, `from` (with `to-from`, `from-to`, `to-nat`). Then `ρ_X = from ∘ μ_X ∘ to` (`ρ-is-μ`), and `polyModule : RightModule T Q`: the module laws are the monad laws (`idr-μ`, `assoc-μ`, naturality of `μ`) carried along the isomorphism. The unit configuration `η-conf x = from (η x)` denotes `h x`, presented (`denote-η`, by `μ ∘ η = id`).

**The machine there** (`Semantics/PolyMachine.agda`; the data of `PolySelfModule` and of the machine). `ηC M` (one thread holding `M`) and `denote-ηC`; the steps at any hole (`ctxAt`, `plug-unplug`, `pure-in`, `op-in`) and `effect-in`, whose target is `μ` of `spliced`: the free model's operation at the hole (`spliced-hole`) and the unit of its thread at every other hole (`spliced-other`); `Final`, `retF`, `denF`, `den-final`, `final-unique` (no affinity); in `Comparing ec`, `denote-ηC-free` and `final-comparison` (at a first-order type, the values of a final configuration that `η M` reaches, renamed along `same`, are the free-model denotation of `M`, presented); `Affine` (the module's affinity, as `Semantics.Affinity` states it), `affine-subsingleton`, and the generic redex for affinity proofs (`Gen`, `origin`, `genSpliced`, `origin-is`, `genSpliced-hole`, `genSpliced-other`); in `WithAffinity finOp finQ aff`, SN, WN, `normalize`, `ground-canonicity`, `canonicity-T`, `ground-canonicity-T`.

**Free models at `W = 1`** (`Instances/Equational/Common.agda`). For plain operations (`constOps`: no locks, no parameters) and a container with shapes `Sh` and positions `Ps`, the carrier on `X` is `Ext (X tt) = Σ_{s ∈ Sh} (Ps s → X tt)`, POPL's `⟦ p ⟧`. An instance gives the unit shape, the operations on every `Ext Z` (natural in `Z`), and `PolyFree`: satisfaction and the universal property at the level of types, exactly POPL's `FreeModel` record (`ext`, `ext-η`, `ext-hom`, `ext-unique`). `WithFree` builds RMR's `FreeModel` (`RightModuleReduction.FreeAdjunction`) and the `Presentation` (both directions the identity, by `refl`). `chaotic` gives `ExpClosed` for every theory, `finOpOf` gives `finOp`.

**The instances** (`Instances/Equational/`; POPL's `Instances/{Writer,Errors,State,WeightedMonoid,WeightedMonoidRules}`):

| Instance | Theory | Free model (container) | Derived rules (machine steps) | Normalization | Run |
|---|---|---|---|---|---|
| Writer (a monoid `M`, a set) | `tell_m`; `tell_ε x = x`, `tell_m (tell_n x) = tell_{m·n} x` | `M × X` (shapes `M`, one position) | `writer-effect : ⟨m , tell_n M⟩ ⟶ ⟨m · n , M⟩` | `writer-affine` (one hole), `writer-sn`, `writer-wn`, `writer-ground-canonicity` | `writer-run`, `writer-run-unique`, `writer-run-comparison` |
| Errors | `raise`, no equations | `X + 1` (shapes `Bool`: run with one position, raised with none) | `err-pure`, `err-effect : ⟨run , S[raise]⟩ ⟶ raised` | `err-affine` (at most one hole), `err-sn`, `err-wn`, `err-ground-canonicity` | `err-run` (`raise to return tt`), `err-run-unique`, `err-run-comparison` |
| Boolean state | `get`, `set_c` (`put c`); get-set, set-get, set-set, get-get | `(Bool × X)^Bool` (shapes `Bool → Bool`, positions `Bool`) | `state-get`, `state-set`, at any hole `p` (POPL: at `s₀`) | `state-affine` (POPL's case analysis on the generic redex), `state-sn`, `state-wn`, `state-ground-canonicity` | `toggle-run` (from both initial states, four steps, to `(not , return tt)`), `toggle-unique`, `toggle-comparison` |
| Weighted monoid (weights a monoid `R`, a set) | `e`, `⊗`, `act_r`; the seven laws | weighted lists `List (R × X)` (shapes `Σ n. Fin n → R`, positions `Fin n`) | `wm-act`, `wm-unit`, `wm-mul` at the first thread | **none: affinity deferred by user decision** | `wm-run`, `wm-run-sound`, `wm-run-unique`, `wm-run-comparison` |

Errors has the theory of `Instances/SelfModule/Error.agda` (no equations); there the free model is the terms over `X`, here `X + 1`. The machines agree on reachable configurations: the configuration `raise` of the term model is `raised` here.

Performance notes (CLAUDE.md): an instance never restates a type that mentions `PolySelfModule.polyModule` at its concrete free model (checking it unifies the result type first, with metavariables, and unfolds the free model), so affinity is stated as `PolyMachine.Affine`; the polynomial is always written `PM.polynomial L₁ O₁` (an alias made the theory's terms take a minute); and the weighted monoid's list bijection `fromL` / `toL` is `opaque` with its lemmas (unfolding it inside a comparison copies each list three times per layer).

### Why the lock must be a quotient

Take the lock's representatives without the relation: at `t`, the set `Σ_v Σ_{q ∈ Pos v} W(scope v q , t) × Γ v`. It is still a presheaf, still lies over `E w` when `Γ` lies over `y w`, and every map out of a lock that the syntax uses can be written on it. But transposition breaks. `transpose ψ e q = ψ (v , q , id , e)` is natural in `e` only if `ψ` sends `(v , q , id , Γ f e)` and `(v' , pos f q , smap f q , e)` to the same element, and that is exactly the coend relation. In fact the plain Σ is `L_κ (Lan_δ U Γ)`, the lock of the free presheaf on `Γ`'s underlying family of sets (`δ : |W| → W`). By Yoneda, a natural map `ψ` out of it is an arbitrary family of elements `ψ (v , q , id , e) ∈ X (scope v q)`, with no condition relating different `v`. Its right adjoint is the step-free Kripke box `Ran_δ U R_κ`: an element at `w` is a choice of an `R_κ`-element at every map out of `w`, with no naturality. That is not `R_κ`.

The right adjoint is not ours to choose. `[ κ ] A` must denote `R_κ ⟦A⟧`, because RMR fixes the arity of an operation: `Ext X w = Σ_o Π_p X (scope w o p)`, so a continuation behind a lock word is an element of `R_μ X`, and RMR's free model, effect step and right modules are all stated for that polynomial. Left adjoints are unique up to isomorphism, so the lock must be the left adjoint of `R_κ`, which is the coend. One can instead keep the representatives and impose the relation as an invariance condition on maps out of them (a presentation by generators and steps). That computes, but its canonicity is then the quotient isomorphism argued on paper, and it needs the objects of `W` to form a set. Here the quotient is formed (`Cubical.HITs.SetQuotients`), and `L ⊣ R` is proved as a bijection (Prop 1.1). On instances it still computes: denotations at the root reduce by `refl` (the `-den` runs and probes above), and the tick lock is the evident `Γ (− + 1)` (`earlierIso`).

### Module map and dependency order

The rows are in dependency order: each module imports only modules in its own or earlier rows (the Imports column lists the main direct imports), and nothing from other `RMRCanonicity` folders.

| Layer | Module | Imports (PRACBPV) | Contents |
|---|---|---|---|
| parameter | `Fam.agda` | | `Fam W`, arities, `cmaps` |
| | `Signature.agda` | Fam | `LockSig`, `OpSig`, words |
| | `Types.agda` | | `ValTy`, `CompTy` |
| | `Polynomial.agda` | Fam, Signature | the polynomial and its strength; `pos-is`, `smap-is` |
| syntax | `Syntax.agda` | Fam, Signature, Types | telescopes, terms, `Ren`, `Sub` |
| | `Properties.agda` | Signature, Syntax | injectivity, `locks-mono` |
| | `Reduction.agda` | Signature, Syntax | `dropW`, `_⇝_`, `_↦_`, `_↦*_` |
| | `Closing.agda` | Fam, Signature, Syntax | `wsW`, `opNodeC`, `closeVals`, `closeK`, `closeOp`, `wpos`, `wsmap`, `ClosedLaws` |
| | `Instances/Constant.agda`, `Instances/LocalState.agda`, `Instances/Guarded.agda`, `Instances/Polynomials.agda` | Syntax, Properties, Polynomial | the instances' signatures and terms |
| semantics | `Semantics/Presheaf.agda` | | `𝒱`, `El`, `Y`, `Ymap`, `fromFun`, `yoneda`, `Env`, `reWorld`, `Exp`, `λExp`, `appExp` |
| | `Semantics/Lock.agda` | Fam, Presheaf | the lock and Props 1.1–1.5 |
| | `Semantics/Algebra.agda` | Presheaf | `Ext`, `strength`, `expAlg`, `η`, `bind` and its interface |
| | `Semantics/Denotation.agda` | Lock, Algebra, Polynomial, Syntax | `K`, `KW`, `⟦_⟧v`, `⟦_⟧c`, `⟦_⟧u`, `⟦_⟧t`, `πt`, `⟦_⟧ne`, `⟦_⟧V`, `⟦_⟧Vs`, `⟦_⟧C`, `⟦_⟧S`, `shutW`, `opNode`, `opDen` |
| | `Semantics/Renaming.agda` | Denotation | `pos-smapW`, `⟦_⟧r`, `ren-over`, Thm 5.1, `shutW-ren` |
| | `Semantics/Substitution.agda` | Denotation, Renaming | `⟦_⟧s`, `sub-over`, Thm 5.2, Lemma 5.3, `shutW-sub` |
| | `Semantics/Soundness.agda` | Reduction, Substitution | `dropW-split`, `shutW-strength`, Thm 6.2 |
| | `Semantics/Closed.agda` | Closing, Substitution | `denClosed`, Lemmas 7.1–7.4, Cor 7.5 |
| | `Semantics/FreeModel.agda` | | the term model of an equation-free theory |
| | `Semantics/Machine.agda` | Soundness, Closed, Closing | `Equations`, `theory`, `WithLaws`, `Run`, Thm 9.1 |
| metatheory | `Metatheory/TypesSet.agda` | Types | `isSetValTy`, `isSetCompTy` |
| | `Metatheory/TermsSet.agda` | Syntax, TypesSet | Thm 8.1 |
| | `Metatheory/Renaming.agda` | Syntax | Thms 8.2–8.4 |
| | `Metatheory/Substitution.agda` | Reduction, Renaming | Thms 5.1–5.5, the laws 5.6 |
| | `Metatheory/SubstReduction.agda` | Reduction, Substitution | `sub-plug`, `sub-⇝`, `sub-↦`, `ren-↦` |
| | `Metatheory/Determinism.agda` | Reduction | `next`, `↦-det`, `op-normal`, `ret-normal`, `↦-to`, `↦-app` |
| | `Metatheory/Chain.agda` | Substitution, SubstReduction | `Chain`, `chV`, `chC`, `liftᶜ`, `lockᶜ`, `wordᶜ` and their laws |
| | `Metatheory/LogicalRelation.agda` | Chain, Determinism | `IsLT`, `LT-ne`, `Tree`, `𝒱⟦_⟧`, `𝒞⟦_⟧`, `𝒢`, Lemma 6.5 |
| | `Metatheory/Fundamental.agda` | LogicalRelation | `⊨V`, `⊨C`, `compat-…`, Thm 6.6 |
| | `Metatheory/Termination.agda` | Fundamental, Closing | `OpTree`, `reify`, `treeNF`, Cor 6.7, Thm 6.8 |
| | `Metatheory/ClosedLaws.agda` | Closing, TermsSet, Renaming | `renVs-consts`, `keepW-wsW`, `closedLaws` |
| equational theory | `Metatheory/Equational.agda` | Reduction, Closing, Machine (for `Equations`) | `ClosedEnv`, `inst`, `inlS`, `inrS`, `pairS`, `_≈v_`, `_≈vs_`, `_≈c_`, `open≈`, `op-to≈`, `op-app≈`, `⇝→≈`, `↦*→≈` |
| | `Metatheory/EqSubstitution.agda` | Equational, Substitution, SubstReduction, Chain | `sub-root`, `sub-wkS`, `sub-dropWS`, `sub-inlS`, `sub-pairS`, `sub≈c`, `ch≈c` |
| | `Metatheory/EqLogicalRelation.agda` | EqSubstitution, LogicalRelation (`IsLT`, `LT-ne`), Termination (`OpTree`) | `FPred`, `𝒱⟦_⟧`, `𝒞⟦_⟧`, `𝒱-conv`, `𝒞-conv`, `fundV`, `fundC`, `equational-canonicity` |
| | `Semantics/StrongTheory.agda` | Denotation, Machine | `ExpClosed`, `expClosed-noEquations`, `Chaotic`, `eval-chaotic`, `expClosed-chaotic` |
| | `Semantics/Free/Denotation.agda` | Denotation (type-independent part), StrongTheory | `Model`, `T`, `η`, `ext`, `ext-η`, `ext-unique`, `expModel`, `preExp`, `bind`, `bind-pre`, `bind-η`, `bind-op`, `bind-unique`, `⟦_⟧m`, `⟦_⟧c`, `⟦_⟧t`, `⟦_⟧V`, `⟦_⟧C`, `⟦_⟧S` |
| | `Semantics/Free/Renaming.agda`, `Free/Substitution.agda`, `Free/Soundness.agda`, `Free/Closed.agda` | Free/Denotation | as `Renaming`, `Substitution`, `Soundness`, `Closed`, for the free-model denotation |
| | `Semantics/EquationalSoundness.agda` | Equational, Free/* | `den-stack-op`, `stack-bind`, `den-inst`, `sound-c`, `sound-c≡` |
| | `Semantics/EqCanonicity.agda` | EquationalSoundness, EqLogicalRelation | `⌊_⌋`, `den-reify`, `canonical-form-denotes`, `canonical-form-unique`, `canonicity` |
| stage G | `Semantics/Free/Comparison.agda` | Denotation, Free/Denotation, Machine (for `Equations`) | `Lifted`, `Rv`, `Rc`, `monoV`, `monoC`, `opsC`, `LRel`, `RΘ`, `over`, `monoΘ`, `unlock-rel`, `shut-rel`, `shutW-rel`, `bind-rel`, `fundNe`, `fundV`, `fundVs`, `fundC`, `related-closed`, `FirstOrder`, `same`, `canon`, `lift-canon`, `comparison`, `comparison₀`, `hClosed`, `machine-comparison` |
| | `Metatheory/TreeNormalization.agda` | Determinism, LogicalRelation, Termination | `_↤_`, `tree-acc`, `strong-normalization` |
| | `Semantics/TreeCanonicity.agda` | EqCanonicity, Free/Soundness, Termination | `tree-canonicity`, `tree-canonicity₀` |
| | `Semantics/Ground.agda` | Denotation | `Ground`, `reflect`, `reflect-den` |
| pure maths | `FinMax.agda`, `FinSum.agda`, `FinCount.agda` | | maxima and sums over finite sets; the multiset order in counting form and its well-foundedness |
| | `Multiset.agda` | | one-step Dershowitz–Manna on lists (present, not used by the theorems above) |
| metatheory | `Metatheory/TreeSize.agda` | Termination, Determinism, FinMax | the height of derivations, `size-unique`, `rel` (opaque), `sz`, `sz-step`, `sz-reindex`, `sz-cont` |
| normalization | `Semantics/Affinity.agda` | (RMR only) | the generic redex, `represent`, `ModuleAffine`, `affine-subsingleton` |
| | `Semantics/Normalization.agda` | Machine, Affinity, TreeSize, FinCount, FinSum | C.1–C.3 |
| | `Semantics/ConfigCanonicity.agda` | Machine, Normalization, Ground | `Final`, `retF`, `denF`, `den-final`, `final-unique`, `normalize`, `ground-canonicity` |
| runners | `Semantics/Runner.agda` | FreeModel | runners, Thm 10.1 |
| | `Semantics/RunMachine.agda` | Machine, Runner, Metatheory.ClosedLaws | derived rules, Cor 10.2 |
| | `Semantics/GuardedLock.agda` | Lock, Instances.Guarded | `earlierIso`, `earlier-nat` |
| | `Instances/Machines/Error.agda`, `Instances/Machines/GlobalState.agda`, `Instances/Machines/LocalState.agda`, `Instances/Machines/Guarded.agda` | RunMachine | runners and runs |
| instances | `Semantics/RunnerAffine.agda` | Runner, Affinity | `runner-affine`, `runner-finQ` |
| | `Semantics/RunNormalization.agda` | RunMachine, RunnerAffine, Normalization, ConfigCanonicity | normalization and canonicity at a runner |
| | `Instances/Normalization/Error.agda`, `…/GlobalState.agda`, `…/LocalState.agda`, `…/Guarded.agda` | RunNormalization, Instances/Machines | `finOp`, SN, WN, terminal runs |
| | `Semantics/SelfModule.agda` | FreeModel, Affinity | `TermQ′`, `confIso`, `selfModule`, `self-affine`, `self-finQ` |
| | `Semantics/SelfMachine.agda` | Machine, SelfModule, Normalization, Metatheory.ClosedLaws | the machine at Q = T, SN, WN, `op-root`, `op-in` |
| | `Semantics/SelfCanonicity.agda` | SelfMachine, ConfigCanonicity, Free/Comparison | `canonicity-T`, `ground-canonicity-T`, `denote-ηC`, `fromTerm-map`, `denote-ηC-free` |
| | `Instances/SelfModule/Error.agda`, `Instances/SelfModule/List.agda` | SelfMachine (Error also SelfCanonicity) | runs at Q = T |
| stage H | `Semantics/PolySelfModule.agda` | (RMR only) | `Presentation`, `from-nat`, `act`, `ρ-is-μ`, `polyModule`, `η-conf`, `denote-η` |
| | `Semantics/PolyMachine.agda` | Machine, PolySelfModule, Affinity, Normalization, ConfigCanonicity, Free/Comparison, Metatheory.ClosedLaws | `ηC`, `denote-ηC`, `pure-in`, `op-in`, `spliced`, `effect-in`, `final-comparison`, `Affine`, the generic redex, `canonicity-T` |
| | `Instances/Equational/Common.agda` | Constant, Machine, StrongTheory, PolySelfModule | `Presented`, `Ext`, `Nalg`, `Q′`, `polyAlg`, `PolyFree`, `freeModel`, `presentation`, `chaotic`, `finOpOf` |
| | `Instances/Equational/Writer.agda`, `Errors.agda`, `State.agda`, `WeightedMonoid.agda` | Common, PolyMachine | the POPL instances with equations |
| other | `Semantics/Branching.agda` | | branching monads (for comodels; present, not used by the theorems above) |

The semantic modules that import the metatheory are `Semantics/RunMachine.agda`, `Semantics/RunNormalization.agda` and `Semantics/SelfMachine.agda` (for `closedLaws`) and `Semantics/Normalization.agda` (for the derivations and their size), the stage-F semantic modules (for the equational theory and its logical relation), and the stage-G modules `Semantics/TreeCanonicity.agda` (for termination) and `Semantics/SelfCanonicity.agda` (for `closedLaws`). The only metatheory modules that import a semantic one are the three equational ones, for the record `Machine.Equations` (and `𝒱`, `El`); there is no cycle, as `Machine` imports no metatheory module. The index files are `Everything.lagda.md` (all of it), `Semantics/Everything.agda` (the semantics, the substitution lemmas, tree reduction, closing, the machine, affinity and normalization, with `Reduction` and `Closing`), `Metatheory/Everything.agda`, `Instances/Machines/Everything.agda`, `Instances/Normalization/Everything.agda`, `Instances/SelfModule/Everything.agda` and `Instances/Equational/Everything.agda`.

{% endraw %}
