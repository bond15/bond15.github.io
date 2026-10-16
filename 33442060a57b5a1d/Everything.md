---
title: "Alternate operational semantics"
layout: agda
permalink: /33442060a57b5a1d/Everything.html
sitemap: false
---
{% raw %}
<link rel="stylesheet" href="Agda.css">

# Alternate operational semantics

Strong normalization is used in the tree adequacy result, but its main purpose is to make the termination measure well defined.

Notation: the note's `↦red` is `_⇝_`, its `↦tree` is `_↦_`, and its `𝒞[B]` is `𝒞⟦ B ⟧`.

## Tree reduction

| Note | Agda |
|---|---|
| β-steps | [`_↦red_`](CBPV.Reduction.html#2409) |
| redexes `↦red`: β-steps, and an operation moving out through one frame | [`_⇝_`](CBPV.Reduction.html#3252) |
| tree reduction `↦tree`: redexes, one frame at a time, one operation argument at a time | [`_↦_`](CBPV.Reduction.html#4173), [`_↦*_`](CBPV.Reduction.html#4671) |
| Closed under stacks | [`step-plug`](CBPV.Reduction.html#5280), [`steps-plug`](CBPV.Reduction.html#5639) |
| Whole stack, in `\|S\|` steps | [`whole-stack`](CBPV.Reduction.html#6807), [`whole-stack-len`](CBPV.Reduction.html#7744), [`depth`](CBPV.Reduction.html#6197) |
| Operation steps | [`op-step`](CBPV.Reduction.html#11201) |
| Under operations | [`op-cong*`](CBPV.Trees.html#2367) |
| Soundness | [`sound↦`](CBPV.Soundness.html#1799), [`sound↦*`](CBPV.Soundness.html#2495) |

## Strong normalization and tree adequacy

| Note | Agda |
|---|---|
| Strongly normalizing | [`SN`](CBPV.SNRelation.html#2217) |
| Neutral terms | [`Neutral`](CBPV.SNRelation.html#2476) |
| Candidates (CR1–CR4) | [`SCand`](CBPV.SNRelation.html#8303) |
| Logical relation | [`𝒱⟦_⟧`](CBPV.SNRelation.html#10399), [`𝒞⟦_⟧`](CBPV.SNRelation.html#10432), and at `F A` [`SPred`](CBPV.SNRelation.html#9037) |
| Reducibility: each `𝒞⟦ B ⟧` is a candidate | [`𝒞⟦_⟧`](CBPV.SNRelation.html#10432) |
| Fundamental lemma | [`fundV`](CBPV.SNFundamental.html#6374), [`fundC`](CBPV.SNFundamental.html#6405), closed terms [`related`](CBPV.SNFundamental.html#7963) |
| strong normalization of every closed computation | [`strong-normalization`](CBPV.SNFundamental.html#8268) |
| Normal forms | [`NF`](CBPV.NormalForms.html#1020) |
| Progress | [`progress`](CBPV.NormalForms.html#1837) |
| trees as computations | [`reify`](CBPV.Trees.html#2695) |
| Tree adequacy | [`tree-adequacy`](CBPV.TreeAdequacy.html#902) |

## Configuration adequacy

| Note | Agda |
|---|---|
| configurations, Pure and Effect | [`Config`](CBPV.ConfigReduction.html#1320), [`_↦T_`](CBPV.ConfigReduction.html#1393), [`_↦T*_`](CBPV.ConfigReduction.html#1719) |
| soundness of `↦T` | [`sound-T`](CBPV.ConfigReduction.html#2707), [`sound-T*`](CBPV.ConfigReduction.html#3530) |
| affine operational model | [`Affine`](CBPV.ConfigReduction.html#4852) |
| Configuration progress | [`progress-T`](CBPV.ConfigProgress.html#1604) |
| Measure | [`‖_‖`](CBPV.Measure.html#15710), [`‖‖-op`](CBPV.Measure.html#15756), [`‖‖-other`](CBPV.Measure.html#15893), [`‖_‖T`](CBPV.ConfigNormalization.html#4840) |
| well founded by strong normalization, since each `M` has finitely many reducts | [`strong-normalization`](CBPV.SNFundamental.html#8268), [`reducts`](CBPV.Measure.html#10803) |
| Measure decreases | [`step-dec`](CBPV.Measure.html#17714) |
| Stack bound | [`stack-op-bound`](CBPV.Measure.html#18489) |
| Strongly normalizing configurations | [`_↤T_`](CBPV.ConfigNormalization.html#6413) (accessibility) |
| Configuration strong normalization | [`decrease-T`](CBPV.ConfigNormalization.html#4973), [`strong-normalization-T`](CBPV.ConfigNormalization.html#6498) |
| steps in any order reach a final configuration | [`normalize-T`](CBPV.Adequacy.html#1655) |
| Configuration adequacy | [`config-adequacy`](CBPV.Adequacy.html#2064) |
| Uniqueness, for `A` built from `0, 1, +, ×` | [`uniqueness`](CBPV.Adequacy.html#4066), [`Ground`](CBPV.Adequacy.html#3191) |

## Modules

This page is the literate Agda module `Everything`, which imports every module.

<pre class="Agda"><a id="3751" class="Keyword">module</a> <a id="3758" href="Everything.html" class="Module">Everything</a> <a id="3769" class="Keyword">where</a>

<a id="3776" class="Keyword">import</a> <a id="3783" href="CBPV.Adequacy.html" class="Module">CBPV.Adequacy</a>
<a id="3797" class="Keyword">import</a> <a id="3804" href="CBPV.ConfigNormalization.html" class="Module">CBPV.ConfigNormalization</a>
<a id="3829" class="Keyword">import</a> <a id="3836" href="CBPV.ConfigProgress.html" class="Module">CBPV.ConfigProgress</a>
<a id="3856" class="Keyword">import</a> <a id="3863" href="CBPV.ConfigReduction.html" class="Module">CBPV.ConfigReduction</a>
<a id="3884" class="Keyword">import</a> <a id="3891" href="CBPV.Denotation.html" class="Module">CBPV.Denotation</a>
<a id="3907" class="Keyword">import</a> <a id="3914" href="CBPV.DenotationLemmas.html" class="Module">CBPV.DenotationLemmas</a>
<a id="3936" class="Keyword">import</a> <a id="3943" href="CBPV.Fin.html" class="Module">CBPV.Fin</a>
<a id="3952" class="Keyword">import</a> <a id="3959" href="CBPV.FreeModel.html" class="Module">CBPV.FreeModel</a>
<a id="3974" class="Keyword">import</a> <a id="3981" href="CBPV.Measure.html" class="Module">CBPV.Measure</a>
<a id="3994" class="Keyword">import</a> <a id="4001" href="CBPV.Models.html" class="Module">CBPV.Models</a>
<a id="4013" class="Keyword">import</a> <a id="4020" href="CBPV.NormalForms.html" class="Module">CBPV.NormalForms</a>
<a id="4037" class="Keyword">import</a> <a id="4044" href="CBPV.OperationalModel.html" class="Module">CBPV.OperationalModel</a>
<a id="4066" class="Keyword">import</a> <a id="4073" href="CBPV.Plug.html" class="Module">CBPV.Plug</a>
<a id="4083" class="Keyword">import</a> <a id="4090" href="CBPV.Polynomial.html" class="Module">CBPV.Polynomial</a>
<a id="4106" class="Keyword">import</a> <a id="4113" href="CBPV.Reduction.html" class="Module">CBPV.Reduction</a>
<a id="4128" class="Keyword">import</a> <a id="4135" href="CBPV.Renaming.html" class="Module">CBPV.Renaming</a>
<a id="4149" class="Keyword">import</a> <a id="4156" href="CBPV.SNFundamental.html" class="Module">CBPV.SNFundamental</a>
<a id="4175" class="Keyword">import</a> <a id="4182" href="CBPV.SNRelation.html" class="Module">CBPV.SNRelation</a>
<a id="4198" class="Keyword">import</a> <a id="4205" href="CBPV.Soundness.html" class="Module">CBPV.Soundness</a>
<a id="4220" class="Keyword">import</a> <a id="4227" href="CBPV.Substitution.html" class="Module">CBPV.Substitution</a>
<a id="4245" class="Keyword">import</a> <a id="4252" href="CBPV.Syntax.html" class="Module">CBPV.Syntax</a>
<a id="4264" class="Keyword">import</a> <a id="4271" href="CBPV.Theory.html" class="Module">CBPV.Theory</a>
<a id="4283" class="Keyword">import</a> <a id="4290" href="CBPV.TreeAdequacy.html" class="Module">CBPV.TreeAdequacy</a>
<a id="4308" class="Keyword">import</a> <a id="4315" href="CBPV.Trees.html" class="Module">CBPV.Trees</a>
<a id="4326" class="Keyword">import</a> <a id="4333" href="CBPV.Types.html" class="Module">CBPV.Types</a>
</pre>
{% endraw %}
