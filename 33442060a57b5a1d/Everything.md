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

## Confluence

| Note | Agda |
|---|---|
| Newman's lemma | [`newman`](CBPV.Newman.html#849) |
| local confluence | [`local-conf`](CBPV.Confluence.html#5660) |
| confluence | [`confluence`](CBPV.Confluence.html#8078) |
| unique normal forms; `reify` is injective; the tree in tree adequacy is unique | [`nf-unique`](CBPV.Confluence.html#8447), [`reify-inj`](CBPV.Confluence.html#9323), [`tree-unique`](CBPV.Confluence.html#9511) |

## Modules

This page is the literate Agda module `Everything`, which imports every module.

<pre class="Agda"><a id="4183" class="Keyword">module</a> <a id="4190" href="Everything.html" class="Module">Everything</a> <a id="4201" class="Keyword">where</a>

<a id="4208" class="Keyword">import</a> <a id="4215" href="CBPV.Adequacy.html" class="Module">CBPV.Adequacy</a>
<a id="4229" class="Keyword">import</a> <a id="4236" href="CBPV.ConfigNormalization.html" class="Module">CBPV.ConfigNormalization</a>
<a id="4261" class="Keyword">import</a> <a id="4268" href="CBPV.ConfigProgress.html" class="Module">CBPV.ConfigProgress</a>
<a id="4288" class="Keyword">import</a> <a id="4295" href="CBPV.ConfigReduction.html" class="Module">CBPV.ConfigReduction</a>
<a id="4316" class="Keyword">import</a> <a id="4323" href="CBPV.Confluence.html" class="Module">CBPV.Confluence</a>
<a id="4339" class="Keyword">import</a> <a id="4346" href="CBPV.Denotation.html" class="Module">CBPV.Denotation</a>
<a id="4362" class="Keyword">import</a> <a id="4369" href="CBPV.DenotationLemmas.html" class="Module">CBPV.DenotationLemmas</a>
<a id="4391" class="Keyword">import</a> <a id="4398" href="CBPV.Fin.html" class="Module">CBPV.Fin</a>
<a id="4407" class="Keyword">import</a> <a id="4414" href="CBPV.FreeModel.html" class="Module">CBPV.FreeModel</a>
<a id="4429" class="Keyword">import</a> <a id="4436" href="CBPV.Measure.html" class="Module">CBPV.Measure</a>
<a id="4449" class="Keyword">import</a> <a id="4456" href="CBPV.Models.html" class="Module">CBPV.Models</a>
<a id="4468" class="Keyword">import</a> <a id="4475" href="CBPV.Newman.html" class="Module">CBPV.Newman</a>
<a id="4487" class="Keyword">import</a> <a id="4494" href="CBPV.NormalForms.html" class="Module">CBPV.NormalForms</a>
<a id="4511" class="Keyword">import</a> <a id="4518" href="CBPV.OperationalModel.html" class="Module">CBPV.OperationalModel</a>
<a id="4540" class="Keyword">import</a> <a id="4547" href="CBPV.Plug.html" class="Module">CBPV.Plug</a>
<a id="4557" class="Keyword">import</a> <a id="4564" href="CBPV.Polynomial.html" class="Module">CBPV.Polynomial</a>
<a id="4580" class="Keyword">import</a> <a id="4587" href="CBPV.Reduction.html" class="Module">CBPV.Reduction</a>
<a id="4602" class="Keyword">import</a> <a id="4609" href="CBPV.Renaming.html" class="Module">CBPV.Renaming</a>
<a id="4623" class="Keyword">import</a> <a id="4630" href="CBPV.SNFundamental.html" class="Module">CBPV.SNFundamental</a>
<a id="4649" class="Keyword">import</a> <a id="4656" href="CBPV.SNRelation.html" class="Module">CBPV.SNRelation</a>
<a id="4672" class="Keyword">import</a> <a id="4679" href="CBPV.Soundness.html" class="Module">CBPV.Soundness</a>
<a id="4694" class="Keyword">import</a> <a id="4701" href="CBPV.Substitution.html" class="Module">CBPV.Substitution</a>
<a id="4719" class="Keyword">import</a> <a id="4726" href="CBPV.Syntax.html" class="Module">CBPV.Syntax</a>
<a id="4738" class="Keyword">import</a> <a id="4745" href="CBPV.Theory.html" class="Module">CBPV.Theory</a>
<a id="4757" class="Keyword">import</a> <a id="4764" href="CBPV.TreeAdequacy.html" class="Module">CBPV.TreeAdequacy</a>
<a id="4782" class="Keyword">import</a> <a id="4789" href="CBPV.Trees.html" class="Module">CBPV.Trees</a>
<a id="4800" class="Keyword">import</a> <a id="4807" href="CBPV.Types.html" class="Module">CBPV.Types</a>
</pre>
{% endraw %}
