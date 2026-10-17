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
| local confluence | [`local-conf`](CBPV.Confluence.html#5631) |
| confluence | [`confluence`](CBPV.Confluence.html#8049) |
| unique normal forms; the tree in tree adequacy is unique | [`nf-unique`](CBPV.Confluence.html#8418), [`tree-unique`](CBPV.Confluence.html#8827) |

## Modules

This page is the literate Agda module `Everything`, which imports every module.

<pre class="Agda"><a id="4119" class="Keyword">module</a> <a id="4126" href="Everything.html" class="Module">Everything</a> <a id="4137" class="Keyword">where</a>

<a id="4144" class="Keyword">import</a> <a id="4151" href="CBPV.Adequacy.html" class="Module">CBPV.Adequacy</a>
<a id="4165" class="Keyword">import</a> <a id="4172" href="CBPV.ConfigNormalization.html" class="Module">CBPV.ConfigNormalization</a>
<a id="4197" class="Keyword">import</a> <a id="4204" href="CBPV.ConfigProgress.html" class="Module">CBPV.ConfigProgress</a>
<a id="4224" class="Keyword">import</a> <a id="4231" href="CBPV.ConfigReduction.html" class="Module">CBPV.ConfigReduction</a>
<a id="4252" class="Keyword">import</a> <a id="4259" href="CBPV.Confluence.html" class="Module">CBPV.Confluence</a>
<a id="4275" class="Keyword">import</a> <a id="4282" href="CBPV.Denotation.html" class="Module">CBPV.Denotation</a>
<a id="4298" class="Keyword">import</a> <a id="4305" href="CBPV.DenotationLemmas.html" class="Module">CBPV.DenotationLemmas</a>
<a id="4327" class="Keyword">import</a> <a id="4334" href="CBPV.Fin.html" class="Module">CBPV.Fin</a>
<a id="4343" class="Keyword">import</a> <a id="4350" href="CBPV.FreeModel.html" class="Module">CBPV.FreeModel</a>
<a id="4365" class="Keyword">import</a> <a id="4372" href="CBPV.Measure.html" class="Module">CBPV.Measure</a>
<a id="4385" class="Keyword">import</a> <a id="4392" href="CBPV.Models.html" class="Module">CBPV.Models</a>
<a id="4404" class="Keyword">import</a> <a id="4411" href="CBPV.Newman.html" class="Module">CBPV.Newman</a>
<a id="4423" class="Keyword">import</a> <a id="4430" href="CBPV.NormalForms.html" class="Module">CBPV.NormalForms</a>
<a id="4447" class="Keyword">import</a> <a id="4454" href="CBPV.OperationalModel.html" class="Module">CBPV.OperationalModel</a>
<a id="4476" class="Keyword">import</a> <a id="4483" href="CBPV.Plug.html" class="Module">CBPV.Plug</a>
<a id="4493" class="Keyword">import</a> <a id="4500" href="CBPV.Polynomial.html" class="Module">CBPV.Polynomial</a>
<a id="4516" class="Keyword">import</a> <a id="4523" href="CBPV.Reduction.html" class="Module">CBPV.Reduction</a>
<a id="4538" class="Keyword">import</a> <a id="4545" href="CBPV.Renaming.html" class="Module">CBPV.Renaming</a>
<a id="4559" class="Keyword">import</a> <a id="4566" href="CBPV.SNFundamental.html" class="Module">CBPV.SNFundamental</a>
<a id="4585" class="Keyword">import</a> <a id="4592" href="CBPV.SNRelation.html" class="Module">CBPV.SNRelation</a>
<a id="4608" class="Keyword">import</a> <a id="4615" href="CBPV.Soundness.html" class="Module">CBPV.Soundness</a>
<a id="4630" class="Keyword">import</a> <a id="4637" href="CBPV.Substitution.html" class="Module">CBPV.Substitution</a>
<a id="4655" class="Keyword">import</a> <a id="4662" href="CBPV.Syntax.html" class="Module">CBPV.Syntax</a>
<a id="4674" class="Keyword">import</a> <a id="4681" href="CBPV.Theory.html" class="Module">CBPV.Theory</a>
<a id="4693" class="Keyword">import</a> <a id="4700" href="CBPV.TreeAdequacy.html" class="Module">CBPV.TreeAdequacy</a>
<a id="4718" class="Keyword">import</a> <a id="4725" href="CBPV.Trees.html" class="Module">CBPV.Trees</a>
<a id="4736" class="Keyword">import</a> <a id="4743" href="CBPV.Types.html" class="Module">CBPV.Types</a>
</pre>
{% endraw %}
