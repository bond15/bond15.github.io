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
| β-steps | [`_↦red_`](CBPV.Reduction.html#2560) |
| redexes `↦red`: β-steps, and an operation moving out through one frame | [`_⇝_`](CBPV.Reduction.html#3438) |
| tree reduction `↦tree`: redexes, one frame at a time, one operation argument at a time | [`_↦_`](CBPV.Reduction.html#4364), [`_↦*_`](CBPV.Reduction.html#4867) |
| Closed under stacks | [`step-plug`](CBPV.Reduction.html#5618), [`steps-plug`](CBPV.Reduction.html#5977) |
| Whole stack, in `\|S\|` steps | [`whole-stack`](CBPV.Reduction.html#7429), [`whole-stack-len`](CBPV.Reduction.html#8366), [`depth`](CBPV.Reduction.html#6819) |
| Operation steps | [`op-step`](CBPV.Reduction.html#11828) |
| Under operations | [`op-cong*`](CBPV.Trees.html#2367) |
| Nondeterminism | [`nondet`](CBPV.Reduction.html#12524) |
| Soundness | [`sound↦`](CBPV.Soundness.html#1799), [`sound↦*`](CBPV.Soundness.html#2495) |

## Strong normalization and tree adequacy

| Note | Agda |
|---|---|
| Strongly normalizing | [`SN`](CBPV.SNRelation.html#2217) |
| Neutral terms | [`Neutral`](CBPV.SNRelation.html#2476) |
| Candidates (CR1–CR4) | [`SCand`](CBPV.SNRelation.html#8308) |
| Logical relation | [`𝒱⟦_⟧`](CBPV.SNRelation.html#10404), [`𝒞⟦_⟧`](CBPV.SNRelation.html#10437), and at `F A` [`SPred`](CBPV.SNRelation.html#9042) |
| Reducibility: each `𝒞⟦ B ⟧` is a candidate | [`𝒞⟦_⟧`](CBPV.SNRelation.html#10437) |
| Fundamental lemma | [`fundV`](CBPV.SNFundamental.html#6464), [`fundC`](CBPV.SNFundamental.html#6500), closed terms [`related`](CBPV.SNFundamental.html#8063) |
| strong normalization of every closed computation | [`strong-normalization`](CBPV.SNFundamental.html#8368) |
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
| well founded by strong normalization, since each `M` has finitely many reducts | [`strong-normalization`](CBPV.SNFundamental.html#8368), [`reducts`](CBPV.Measure.html#10813) |
| Measure decreases | [`step-dec`](CBPV.Measure.html#17781) |
| Stack bound | [`stack-op-bound`](CBPV.Measure.html#18556) |
| Strongly normalizing configurations | [`_↤T_`](CBPV.ConfigNormalization.html#6413) (accessibility) |
| Configuration strong normalization | [`decrease-T`](CBPV.ConfigNormalization.html#4973), [`strong-normalization-T`](CBPV.ConfigNormalization.html#6498) |
| steps in any order reach a final configuration | [`normalize-T`](CBPV.Adequacy.html#1655) |
| Configuration adequacy | [`config-adequacy`](CBPV.Adequacy.html#2064) |
| Uniqueness, for `A` built from `0, 1, +, ×` | [`uniqueness`](CBPV.Adequacy.html#4066), [`Ground`](CBPV.Adequacy.html#3191) |

## Modules

This page is the literate Agda module `Everything`, which imports every module.

<pre class="Agda"><a id="3847" class="Keyword">module</a> <a id="3854" href="Everything.html" class="Module">Everything</a> <a id="3865" class="Keyword">where</a>

<a id="3872" class="Keyword">import</a> <a id="3879" href="CBPV.Adequacy.html" class="Module">CBPV.Adequacy</a>
<a id="3893" class="Keyword">import</a> <a id="3900" href="CBPV.ConfigNormalization.html" class="Module">CBPV.ConfigNormalization</a>
<a id="3925" class="Keyword">import</a> <a id="3932" href="CBPV.ConfigProgress.html" class="Module">CBPV.ConfigProgress</a>
<a id="3952" class="Keyword">import</a> <a id="3959" href="CBPV.ConfigReduction.html" class="Module">CBPV.ConfigReduction</a>
<a id="3980" class="Keyword">import</a> <a id="3987" href="CBPV.Denotation.html" class="Module">CBPV.Denotation</a>
<a id="4003" class="Keyword">import</a> <a id="4010" href="CBPV.DenotationLemmas.html" class="Module">CBPV.DenotationLemmas</a>
<a id="4032" class="Keyword">import</a> <a id="4039" href="CBPV.Fin.html" class="Module">CBPV.Fin</a>
<a id="4048" class="Keyword">import</a> <a id="4055" href="CBPV.FreeModel.html" class="Module">CBPV.FreeModel</a>
<a id="4070" class="Keyword">import</a> <a id="4077" href="CBPV.Measure.html" class="Module">CBPV.Measure</a>
<a id="4090" class="Keyword">import</a> <a id="4097" href="CBPV.Models.html" class="Module">CBPV.Models</a>
<a id="4109" class="Keyword">import</a> <a id="4116" href="CBPV.NormalForms.html" class="Module">CBPV.NormalForms</a>
<a id="4133" class="Keyword">import</a> <a id="4140" href="CBPV.OperationalModel.html" class="Module">CBPV.OperationalModel</a>
<a id="4162" class="Keyword">import</a> <a id="4169" href="CBPV.Plug.html" class="Module">CBPV.Plug</a>
<a id="4179" class="Keyword">import</a> <a id="4186" href="CBPV.Polynomial.html" class="Module">CBPV.Polynomial</a>
<a id="4202" class="Keyword">import</a> <a id="4209" href="CBPV.Reduction.html" class="Module">CBPV.Reduction</a>
<a id="4224" class="Keyword">import</a> <a id="4231" href="CBPV.Renaming.html" class="Module">CBPV.Renaming</a>
<a id="4245" class="Keyword">import</a> <a id="4252" href="CBPV.SNFundamental.html" class="Module">CBPV.SNFundamental</a>
<a id="4271" class="Keyword">import</a> <a id="4278" href="CBPV.SNRelation.html" class="Module">CBPV.SNRelation</a>
<a id="4294" class="Keyword">import</a> <a id="4301" href="CBPV.Soundness.html" class="Module">CBPV.Soundness</a>
<a id="4316" class="Keyword">import</a> <a id="4323" href="CBPV.Substitution.html" class="Module">CBPV.Substitution</a>
<a id="4341" class="Keyword">import</a> <a id="4348" href="CBPV.Syntax.html" class="Module">CBPV.Syntax</a>
<a id="4360" class="Keyword">import</a> <a id="4367" href="CBPV.Theory.html" class="Module">CBPV.Theory</a>
<a id="4379" class="Keyword">import</a> <a id="4386" href="CBPV.TreeAdequacy.html" class="Module">CBPV.TreeAdequacy</a>
<a id="4404" class="Keyword">import</a> <a id="4411" href="CBPV.Trees.html" class="Module">CBPV.Trees</a>
<a id="4422" class="Keyword">import</a> <a id="4429" href="CBPV.Types.html" class="Module">CBPV.Types</a>
</pre>
{% endraw %}
