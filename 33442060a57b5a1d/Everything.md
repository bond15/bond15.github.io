---
title: "CBPV(𝒯) with one-frame algebraicity"
layout: agda
permalink: /33442060a57b5a1d/Everything.html
sitemap: false
---
{% raw %}
<link rel="stylesheet" href="Agda.css">

# CBPV(𝒯) with one-frame algebraicity

This is a minimal Agda development of the three-page note. Tree reduction moves an operation out through a stack one frame at a time, so it is closed under stacks. Strong normalization is proved with reducibility candidates, and tree adequacy is read off the logical relation. For an affine operational model, configuration reduction is strongly normalizing for every interleaving of Pure and Effect steps, it computes the denotation (configuration adequacy), and the final configuration is unique at ground types. Both tree adequacy and the termination measure rest on the strong-normalization logical relation: tree adequacy is read off its derivation of `𝒮⟦ F A ⟧ M`, and the strong normalization it gives makes the termination measure on configurations well founded.

The development depends only on the `cubical` library. It has no postulates, holes or termination pragmas, and every module is checked with `--cubical --safe`. Each name below links to its definition.

Notation: the note's `↦red` is `_⇝_`, its `↦tree` is `_↦_`, and its `𝒞[B]` is `𝒮⟦ B ⟧`.

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
| Strongly normalizing | [`SN`](CBPV.SNRelation.html#2221) |
| Neutral terms | [`Neutral`](CBPV.SNRelation.html#2480) |
| Candidates (CR1–CR4) | [`SCand`](CBPV.SNRelation.html#8290) |
| Logical relation | [`𝒱ˢ⟦_⟧`](CBPV.SNRelation.html#10386), [`𝒮⟦_⟧`](CBPV.SNRelation.html#10420), and at `F A` [`SPred`](CBPV.SNRelation.html#9024) |
| Reducibility: each `𝒮⟦ B ⟧` is a candidate | [`𝒮⟦_⟧`](CBPV.SNRelation.html#10420) |
| Fundamental lemma | [`fundVˢ`](CBPV.SNFundamental.html#6478), [`fundCˢ`](CBPV.SNFundamental.html#6516), closed terms [`relatedˢ`](CBPV.SNFundamental.html#8132) |
| strong normalization of every closed computation | [`strong-normalization`](CBPV.SNFundamental.html#8440) |
| Normal forms | [`NF`](CBPV.NormalForms.html#1076) |
| Progress | [`progress`](CBPV.NormalForms.html#2218) |
| trees as computations | [`reify`](CBPV.Trees.html#2695) |
| Tree adequacy | [`tree-adequacy`](CBPV.TreeAdequacy.html#903) |

## Configuration adequacy

| Note | Agda |
|---|---|
| configurations, Pure and Effect | [`Config`](CBPV.ConfigReduction.html#1320), [`_↦T_`](CBPV.ConfigReduction.html#1393), [`_↦T*_`](CBPV.ConfigReduction.html#1719) |
| soundness of `↦T` | [`sound-T`](CBPV.ConfigReduction.html#2707), [`sound-T*`](CBPV.ConfigReduction.html#3530) |
| affine operational model | [`Affine`](CBPV.ConfigReduction.html#4852) |
| Configuration progress | [`progress-T`](CBPV.ConfigProgress.html#1604) |
| Measure | [`‖_‖`](CBPV.Measure.html#15720), [`‖‖-ret`](CBPV.Measure.html#15766), [`‖‖-op`](CBPV.Measure.html#15823), [`‖‖-other`](CBPV.Measure.html#15960), [`‖_‖T`](CBPV.ConfigNormalization.html#4840) |
| well founded by strong normalization, since each `M` has finitely many reducts | [`strong-normalization`](CBPV.SNFundamental.html#8440), [`reducts`](CBPV.Measure.html#10813) |
| Measure decreases | [`step-dec`](CBPV.Measure.html#17781) |
| Stack bound | [`stack-op-bound`](CBPV.Measure.html#18556) |
| Strongly normalizing configurations | [`_↤T_`](CBPV.ConfigNormalization.html#6413) (accessibility) |
| Configuration strong normalization | [`decrease-T`](CBPV.ConfigNormalization.html#4973), [`strong-normalization-T`](CBPV.ConfigNormalization.html#6498) |
| steps in any order reach a final configuration | [`normalize-T`](CBPV.Adequacy.html#1655) |
| Configuration adequacy | [`config-adequacy`](CBPV.Adequacy.html#2064) |
| Uniqueness, for `A` built from `0, 1, +, ×` | [`uniqueness`](CBPV.Adequacy.html#4066), [`Ground`](CBPV.Adequacy.html#3191) |

## Modules

This page is the literate Agda module `Everything`, which imports every module.

<pre class="Agda"><a id="4688" class="Keyword">module</a> <a id="4695" href="Everything.html" class="Module">Everything</a> <a id="4706" class="Keyword">where</a>

<a id="4713" class="Keyword">import</a> <a id="4720" href="CBPV.Adequacy.html" class="Module">CBPV.Adequacy</a>
<a id="4734" class="Keyword">import</a> <a id="4741" href="CBPV.ConfigNormalization.html" class="Module">CBPV.ConfigNormalization</a>
<a id="4766" class="Keyword">import</a> <a id="4773" href="CBPV.ConfigProgress.html" class="Module">CBPV.ConfigProgress</a>
<a id="4793" class="Keyword">import</a> <a id="4800" href="CBPV.ConfigReduction.html" class="Module">CBPV.ConfigReduction</a>
<a id="4821" class="Keyword">import</a> <a id="4828" href="CBPV.Denotation.html" class="Module">CBPV.Denotation</a>
<a id="4844" class="Keyword">import</a> <a id="4851" href="CBPV.DenotationLemmas.html" class="Module">CBPV.DenotationLemmas</a>
<a id="4873" class="Keyword">import</a> <a id="4880" href="CBPV.Fin.html" class="Module">CBPV.Fin</a>
<a id="4889" class="Keyword">import</a> <a id="4896" href="CBPV.FreeModel.html" class="Module">CBPV.FreeModel</a>
<a id="4911" class="Keyword">import</a> <a id="4918" href="CBPV.Measure.html" class="Module">CBPV.Measure</a>
<a id="4931" class="Keyword">import</a> <a id="4938" href="CBPV.Models.html" class="Module">CBPV.Models</a>
<a id="4950" class="Keyword">import</a> <a id="4957" href="CBPV.NormalForms.html" class="Module">CBPV.NormalForms</a>
<a id="4974" class="Keyword">import</a> <a id="4981" href="CBPV.OperationalModel.html" class="Module">CBPV.OperationalModel</a>
<a id="5003" class="Keyword">import</a> <a id="5010" href="CBPV.Plug.html" class="Module">CBPV.Plug</a>
<a id="5020" class="Keyword">import</a> <a id="5027" href="CBPV.Polynomial.html" class="Module">CBPV.Polynomial</a>
<a id="5043" class="Keyword">import</a> <a id="5050" href="CBPV.Reduction.html" class="Module">CBPV.Reduction</a>
<a id="5065" class="Keyword">import</a> <a id="5072" href="CBPV.Renaming.html" class="Module">CBPV.Renaming</a>
<a id="5086" class="Keyword">import</a> <a id="5093" href="CBPV.SNFundamental.html" class="Module">CBPV.SNFundamental</a>
<a id="5112" class="Keyword">import</a> <a id="5119" href="CBPV.SNRelation.html" class="Module">CBPV.SNRelation</a>
<a id="5135" class="Keyword">import</a> <a id="5142" href="CBPV.Soundness.html" class="Module">CBPV.Soundness</a>
<a id="5157" class="Keyword">import</a> <a id="5164" href="CBPV.Substitution.html" class="Module">CBPV.Substitution</a>
<a id="5182" class="Keyword">import</a> <a id="5189" href="CBPV.Syntax.html" class="Module">CBPV.Syntax</a>
<a id="5201" class="Keyword">import</a> <a id="5208" href="CBPV.Theory.html" class="Module">CBPV.Theory</a>
<a id="5220" class="Keyword">import</a> <a id="5227" href="CBPV.TreeAdequacy.html" class="Module">CBPV.TreeAdequacy</a>
<a id="5245" class="Keyword">import</a> <a id="5252" href="CBPV.Trees.html" class="Module">CBPV.Trees</a>
<a id="5263" class="Keyword">import</a> <a id="5270" href="CBPV.Types.html" class="Module">CBPV.Types</a>
</pre>
{% endraw %}
