---
title: "Option C"
layout: agda
permalink: /33442060a57b5a1d/Everything.html
sitemap: false
---
{% raw %}
<link rel="stylesheet" href="Agda.css">

# Option C: CBPV(𝒯) with one-frame algebraicity

This is a minimal Agda development of the three-page note on Option C. Tree reduction moves an operation out through a stack one frame at a time, so it is closed under stacks. Strong normalization is proved with reducibility candidates, and tree adequacy is read off the logical relation. For an affine operational model, configuration reduction is strongly normalizing for every interleaving of Pure and Effect steps, it computes the denotation (configuration adequacy), and the final configuration is unique at ground types.

The development depends only on the `cubical` library. It has no postulates, holes or termination pragmas, and every module is checked with `--cubical --safe`. Each name below links to its definition.

Notation: the note's `↦red` is `_⇝_`, its `↦tree` is `_↦_`, and its `𝒞[B]` is `𝒮⟦ B ⟧`.

## Tree reduction

| Note | Agda |
|---|---|
| β-steps | [`_↦red_`](OptionC.Reduction.html#2611) |
| redexes `↦red`: β-steps and algebraicity through one frame | [`_⇝_`](OptionC.Reduction.html#3478) |
| tree reduction `↦tree`: redexes, one frame at a time, one operation argument at a time | [`_↦_`](OptionC.Reduction.html#4404), [`_↦*_`](OptionC.Reduction.html#4907) |
| Closed under stacks | [`step-plug`](OptionC.Reduction.html#5658), [`steps-plug`](OptionC.Reduction.html#6017) |
| Whole stack, in `\|S\|` steps | [`whole-stack`](OptionC.Reduction.html#7489), [`whole-stack-len`](OptionC.Reduction.html#8426), [`depth`](OptionC.Reduction.html#6869) |
| Operation steps | [`op-step`](OptionC.Reduction.html#11888) |
| Under operations | [`op-cong*`](OptionC.Trees.html#2392) |
| Nondeterminism | [`nondet`](OptionC.Reduction.html#12572) |
| Soundness | [`sound↦`](OptionC.Soundness.html#1918), [`sound↦*`](OptionC.Soundness.html#2614) |

## Strong normalization and tree adequacy

| Note | Agda |
|---|---|
| Strongly normalizing | [`SN`](OptionC.SNRelation.html#2297) |
| Neutral terms | [`Neutral`](OptionC.SNRelation.html#2556) |
| Candidates (CR1–CR4) | [`SCand`](OptionC.SNRelation.html#8382) |
| Logical relation | [`𝒱ˢ⟦_⟧`](OptionC.SNRelation.html#10478), [`𝒮⟦_⟧`](OptionC.SNRelation.html#10512), and at `F A` [`SPred`](OptionC.SNRelation.html#9116) |
| Reducibility: each `𝒮⟦ B ⟧` is a candidate | [`𝒮⟦_⟧`](OptionC.SNRelation.html#10512) |
| Fundamental lemma | [`fundVˢ`](OptionC.SNFundamental.html#6556), [`fundCˢ`](OptionC.SNFundamental.html#6594), closed terms [`relatedˢ`](OptionC.SNFundamental.html#8210) |
| strong normalization of every closed computation | [`strong-normalization`](OptionC.SNFundamental.html#8518) |
| Normal forms | [`NF`](OptionC.NormalForms.html#1104) |
| Progress | [`progress`](OptionC.NormalForms.html#2246) |
| trees as computations | [`reify`](OptionC.Trees.html#2720) |
| Tree adequacy | [`tree-adequacy`](OptionC.TreeAdequacy.html#946) |

## Configuration adequacy

| Note | Agda |
|---|---|
| configurations, Pure and Effect | [`Config`](OptionC.ConfigReduction.html#1461), [`_↦T_`](OptionC.ConfigReduction.html#1534), [`_↦T*_`](OptionC.ConfigReduction.html#1860) |
| soundness of `↦T` | [`sound-T`](OptionC.ConfigReduction.html#2848), [`sound-T*`](OptionC.ConfigReduction.html#3671) |
| affine operational model | [`Affine`](OptionC.ConfigReduction.html#5077) |
| Configuration progress | [`progress-T`](OptionC.ConfigProgress.html#1704) |
| Measure | [`‖_‖`](OptionC.Measure.html#15763), [`‖‖-ret`](OptionC.Measure.html#15809), [`‖‖-op`](OptionC.Measure.html#15866), [`‖‖-other`](OptionC.Measure.html#16003), [`‖_‖T`](OptionC.ConfigNormalization.html#5073) |
| well defined by strong normalization, since each `M` has finitely many reducts | [`reducts`](OptionC.Measure.html#10856) |
| Measure decreases | [`step-dec`](OptionC.Measure.html#17824) |
| Stack bound | [`stack-op-bound`](OptionC.Measure.html#18599) |
| Strongly normalizing configurations | [`_↤T_`](OptionC.ConfigNormalization.html#6646) (accessibility) |
| Configuration strong normalization | [`decrease-T`](OptionC.ConfigNormalization.html#5206), [`strong-normalization-T`](OptionC.ConfigNormalization.html#6731) |
| steps in any order reach a final configuration | [`normalize-T`](OptionC.Adequacy.html#1695) |
| Configuration adequacy | [`config-adequacy`](OptionC.Adequacy.html#2104) |
| Uniqueness, for `A` built from `0, 1, +, ×` | [`uniqueness`](OptionC.Adequacy.html#4106), [`Ground`](OptionC.Adequacy.html#3231) |

## Modules

This page is the literate Agda module `Everything`, which imports every module.

<pre class="Agda"><a id="4551" class="Keyword">module</a> <a id="4558" href="Everything.html" class="Module">Everything</a> <a id="4569" class="Keyword">where</a>

<a id="4576" class="Keyword">import</a> <a id="4583" href="OptionC.Adequacy.html" class="Module">OptionC.Adequacy</a>
<a id="4600" class="Keyword">import</a> <a id="4607" href="OptionC.ConfigNormalization.html" class="Module">OptionC.ConfigNormalization</a>
<a id="4635" class="Keyword">import</a> <a id="4642" href="OptionC.ConfigProgress.html" class="Module">OptionC.ConfigProgress</a>
<a id="4665" class="Keyword">import</a> <a id="4672" href="OptionC.ConfigReduction.html" class="Module">OptionC.ConfigReduction</a>
<a id="4696" class="Keyword">import</a> <a id="4703" href="OptionC.Denotation.html" class="Module">OptionC.Denotation</a>
<a id="4722" class="Keyword">import</a> <a id="4729" href="OptionC.DenotationLemmas.html" class="Module">OptionC.DenotationLemmas</a>
<a id="4754" class="Keyword">import</a> <a id="4761" href="OptionC.Fin.html" class="Module">OptionC.Fin</a>
<a id="4773" class="Keyword">import</a> <a id="4780" href="OptionC.FreeModel.html" class="Module">OptionC.FreeModel</a>
<a id="4798" class="Keyword">import</a> <a id="4805" href="OptionC.Measure.html" class="Module">OptionC.Measure</a>
<a id="4821" class="Keyword">import</a> <a id="4828" href="OptionC.Models.html" class="Module">OptionC.Models</a>
<a id="4843" class="Keyword">import</a> <a id="4850" href="OptionC.NormalForms.html" class="Module">OptionC.NormalForms</a>
<a id="4870" class="Keyword">import</a> <a id="4877" href="OptionC.OperationalModel.html" class="Module">OptionC.OperationalModel</a>
<a id="4902" class="Keyword">import</a> <a id="4909" href="OptionC.Plug.html" class="Module">OptionC.Plug</a>
<a id="4922" class="Keyword">import</a> <a id="4929" href="OptionC.Polynomial.html" class="Module">OptionC.Polynomial</a>
<a id="4948" class="Keyword">import</a> <a id="4955" href="OptionC.Reduction.html" class="Module">OptionC.Reduction</a>
<a id="4973" class="Keyword">import</a> <a id="4980" href="OptionC.Renaming.html" class="Module">OptionC.Renaming</a>
<a id="4997" class="Keyword">import</a> <a id="5004" href="OptionC.SNFundamental.html" class="Module">OptionC.SNFundamental</a>
<a id="5026" class="Keyword">import</a> <a id="5033" href="OptionC.SNRelation.html" class="Module">OptionC.SNRelation</a>
<a id="5052" class="Keyword">import</a> <a id="5059" href="OptionC.Soundness.html" class="Module">OptionC.Soundness</a>
<a id="5077" class="Keyword">import</a> <a id="5084" href="OptionC.Substitution.html" class="Module">OptionC.Substitution</a>
<a id="5105" class="Keyword">import</a> <a id="5112" href="OptionC.Syntax.html" class="Module">OptionC.Syntax</a>
<a id="5127" class="Keyword">import</a> <a id="5134" href="OptionC.Theory.html" class="Module">OptionC.Theory</a>
<a id="5149" class="Keyword">import</a> <a id="5156" href="OptionC.TreeAdequacy.html" class="Module">OptionC.TreeAdequacy</a>
<a id="5177" class="Keyword">import</a> <a id="5184" href="OptionC.Trees.html" class="Module">OptionC.Trees</a>
<a id="5198" class="Keyword">import</a> <a id="5205" href="OptionC.Types.html" class="Module">OptionC.Types</a>
</pre>
{% endraw %}
