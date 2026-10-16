---
title: "CBPV(𝒯) with one-frame algebraicity"
layout: agda
permalink: /33442060a57b5a1d/Everything.html
sitemap: false
---
{% raw %}
<link rel="stylesheet" href="Agda.css">

# CBPV(𝒯) with one-frame algebraicity

This is a minimal Agda development of the three-page note. Tree reduction moves an operation out through a stack one frame at a time, so it is closed under stacks. Strong normalization is proved with reducibility candidates, and tree adequacy is read off the logical relation. For an affine operational model, configuration reduction is strongly normalizing for every interleaving of Pure and Effect steps, it computes the denotation (configuration adequacy), and the final configuration is unique at ground types. Both tree adequacy and the termination measure rest on the strong-normalization logical relation: tree adequacy is read off its derivation of `𝒞⟦ F A ⟧ M`, and the strong normalization it gives makes the termination measure on configurations well founded.

The development depends only on the `cubical` library. It has no postulates, holes or termination pragmas, and every module is checked with `--cubical --safe`. Each name below links to its definition.

Notation: the note's `↦red` is `_⇝_`, its `↦tree` is `_↦_`, and its `𝒞[B]` is `𝒞⟦ B ⟧`.

## Tree reduction

| Note | Agda |
|---|---|
| β-steps | [`_↦red_`](CBPV.Reduction.html#2549) |
| redexes `↦red`: β-steps and algebraicity through one frame | [`_⇝_`](CBPV.Reduction.html#3416) |
| tree reduction `↦tree`: redexes, one frame at a time, one operation argument at a time | [`_↦_`](CBPV.Reduction.html#4342), [`_↦*_`](CBPV.Reduction.html#4845) |
| Closed under stacks | [`step-plug`](CBPV.Reduction.html#5596), [`steps-plug`](CBPV.Reduction.html#5955) |
| Whole stack, in `\|S\|` steps | [`whole-stack`](CBPV.Reduction.html#7427), [`whole-stack-len`](CBPV.Reduction.html#8364), [`depth`](CBPV.Reduction.html#6807) |
| Operation steps | [`op-step`](CBPV.Reduction.html#11826) |
| Under operations | [`op-cong*`](CBPV.Trees.html#2367) |
| Nondeterminism | [`nondet`](CBPV.Reduction.html#12510) |
| Soundness | [`sound↦`](CBPV.Soundness.html#1776), [`sound↦*`](CBPV.Soundness.html#2472) |

## Strong normalization and tree adequacy

| Note | Agda |
|---|---|
| Strongly normalizing | [`SN`](CBPV.SNRelation.html#2217) |
| Neutral terms | [`Neutral`](CBPV.SNRelation.html#2476) |
| Candidates (CR1–CR4) | [`SCand`](CBPV.SNRelation.html#8286) |
| Logical relation | [`𝒱⟦_⟧`](CBPV.SNRelation.html#10382), [`𝒞⟦_⟧`](CBPV.SNRelation.html#10415), and at `F A` [`SPred`](CBPV.SNRelation.html#9020) |
| Reducibility: each `𝒞⟦ B ⟧` is a candidate | [`𝒞⟦_⟧`](CBPV.SNRelation.html#10415) |
| Fundamental lemma | [`fundV`](CBPV.SNFundamental.html#6441), [`fundC`](CBPV.SNFundamental.html#6477), closed terms [`related`](CBPV.SNFundamental.html#8040) |
| strong normalization of every closed computation | [`strong-normalization`](CBPV.SNFundamental.html#8345) |
| Normal forms | [`NF`](CBPV.NormalForms.html#1076) |
| Progress | [`progress`](CBPV.NormalForms.html#2218) |
| trees as computations | [`reify`](CBPV.Trees.html#2695) |
| Tree adequacy | [`tree-adequacy`](CBPV.TreeAdequacy.html#902) |

## Configuration adequacy

| Note | Agda |
|---|---|
| configurations, Pure and Effect | [`Config`](CBPV.ConfigReduction.html#1320), [`_↦T_`](CBPV.ConfigReduction.html#1393), [`_↦T*_`](CBPV.ConfigReduction.html#1719) |
| soundness of `↦T` | [`sound-T`](CBPV.ConfigReduction.html#2707), [`sound-T*`](CBPV.ConfigReduction.html#3530) |
| affine operational model | [`Affine`](CBPV.ConfigReduction.html#4852) |
| Configuration progress | [`progress-T`](CBPV.ConfigProgress.html#1604) |
| Measure | [`‖_‖`](CBPV.Measure.html#15720), [`‖‖-ret`](CBPV.Measure.html#15766), [`‖‖-op`](CBPV.Measure.html#15823), [`‖‖-other`](CBPV.Measure.html#15960), [`‖_‖T`](CBPV.ConfigNormalization.html#4840) |
| well founded by strong normalization, since each `M` has finitely many reducts | [`strong-normalization`](CBPV.SNFundamental.html#8345), [`reducts`](CBPV.Measure.html#10813) |
| Measure decreases | [`step-dec`](CBPV.Measure.html#17781) |
| Stack bound | [`stack-op-bound`](CBPV.Measure.html#18556) |
| Strongly normalizing configurations | [`_↤T_`](CBPV.ConfigNormalization.html#6413) (accessibility) |
| Configuration strong normalization | [`decrease-T`](CBPV.ConfigNormalization.html#4973), [`strong-normalization-T`](CBPV.ConfigNormalization.html#6498) |
| steps in any order reach a final configuration | [`normalize-T`](CBPV.Adequacy.html#1655) |
| Configuration adequacy | [`config-adequacy`](CBPV.Adequacy.html#2064) |
| Uniqueness, for `A` built from `0, 1, +, ×` | [`uniqueness`](CBPV.Adequacy.html#4066), [`Ground`](CBPV.Adequacy.html#3191) |

## Modules

This page is the literate Agda module `Everything`, which imports every module.

<pre class="Agda"><a id="4684" class="Keyword">module</a> <a id="4691" href="Everything.html" class="Module">Everything</a> <a id="4702" class="Keyword">where</a>

<a id="4709" class="Keyword">import</a> <a id="4716" href="CBPV.Adequacy.html" class="Module">CBPV.Adequacy</a>
<a id="4730" class="Keyword">import</a> <a id="4737" href="CBPV.ConfigNormalization.html" class="Module">CBPV.ConfigNormalization</a>
<a id="4762" class="Keyword">import</a> <a id="4769" href="CBPV.ConfigProgress.html" class="Module">CBPV.ConfigProgress</a>
<a id="4789" class="Keyword">import</a> <a id="4796" href="CBPV.ConfigReduction.html" class="Module">CBPV.ConfigReduction</a>
<a id="4817" class="Keyword">import</a> <a id="4824" href="CBPV.Denotation.html" class="Module">CBPV.Denotation</a>
<a id="4840" class="Keyword">import</a> <a id="4847" href="CBPV.DenotationLemmas.html" class="Module">CBPV.DenotationLemmas</a>
<a id="4869" class="Keyword">import</a> <a id="4876" href="CBPV.Fin.html" class="Module">CBPV.Fin</a>
<a id="4885" class="Keyword">import</a> <a id="4892" href="CBPV.FreeModel.html" class="Module">CBPV.FreeModel</a>
<a id="4907" class="Keyword">import</a> <a id="4914" href="CBPV.Measure.html" class="Module">CBPV.Measure</a>
<a id="4927" class="Keyword">import</a> <a id="4934" href="CBPV.Models.html" class="Module">CBPV.Models</a>
<a id="4946" class="Keyword">import</a> <a id="4953" href="CBPV.NormalForms.html" class="Module">CBPV.NormalForms</a>
<a id="4970" class="Keyword">import</a> <a id="4977" href="CBPV.OperationalModel.html" class="Module">CBPV.OperationalModel</a>
<a id="4999" class="Keyword">import</a> <a id="5006" href="CBPV.Plug.html" class="Module">CBPV.Plug</a>
<a id="5016" class="Keyword">import</a> <a id="5023" href="CBPV.Polynomial.html" class="Module">CBPV.Polynomial</a>
<a id="5039" class="Keyword">import</a> <a id="5046" href="CBPV.Reduction.html" class="Module">CBPV.Reduction</a>
<a id="5061" class="Keyword">import</a> <a id="5068" href="CBPV.Renaming.html" class="Module">CBPV.Renaming</a>
<a id="5082" class="Keyword">import</a> <a id="5089" href="CBPV.SNFundamental.html" class="Module">CBPV.SNFundamental</a>
<a id="5108" class="Keyword">import</a> <a id="5115" href="CBPV.SNRelation.html" class="Module">CBPV.SNRelation</a>
<a id="5131" class="Keyword">import</a> <a id="5138" href="CBPV.Soundness.html" class="Module">CBPV.Soundness</a>
<a id="5153" class="Keyword">import</a> <a id="5160" href="CBPV.Substitution.html" class="Module">CBPV.Substitution</a>
<a id="5178" class="Keyword">import</a> <a id="5185" href="CBPV.Syntax.html" class="Module">CBPV.Syntax</a>
<a id="5197" class="Keyword">import</a> <a id="5204" href="CBPV.Theory.html" class="Module">CBPV.Theory</a>
<a id="5216" class="Keyword">import</a> <a id="5223" href="CBPV.TreeAdequacy.html" class="Module">CBPV.TreeAdequacy</a>
<a id="5241" class="Keyword">import</a> <a id="5248" href="CBPV.Trees.html" class="Module">CBPV.Trees</a>
<a id="5259" class="Keyword">import</a> <a id="5266" href="CBPV.Types.html" class="Module">CBPV.Types</a>
</pre>
{% endraw %}
