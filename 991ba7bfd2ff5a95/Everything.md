---
title: "POPL'27 formalization"
layout: agda
permalink: /991ba7bfd2ff5a95/Everything.html
sitemap: false
---
{% raw %}
<link rel="stylesheet" href="Agda.css">

# POPL'27 formalization

This is an Agda formalization of `popl27/popl27.tex`. It has no postulates, holes or termination pragmas, and it is checked with `--cubical --safe`. Every correction to the paper and every significant departure from it is listed in [Deviations from the paper](#deviations-from-the-paper) below, with the same `C#` or `D#` tag as the comment in the code. Typos in the paper that do not affect the formalization are not listed.

This page is the literate Agda module `Everything`. Every name in the code blocks links to its definition.

<pre class="Agda"><a id="610" class="Keyword">module</a> <a id="617" href="Everything.html" class="Module">Everything</a> <a id="628" class="Keyword">where</a>

<a id="635" class="Keyword">import</a> <a id="642" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a>
<a id="667" class="Keyword">import</a> <a id="674" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a>
<a id="695" class="Keyword">import</a> <a id="702" href="POPL.Denotation.html" class="Module">POPL.Denotation</a>
<a id="718" class="Keyword">import</a> <a id="725" href="POPL.DenotationLemmas.html" class="Module">POPL.DenotationLemmas</a>
<a id="747" class="Keyword">import</a> <a id="754" href="POPL.EqCanonicity.html" class="Module">POPL.EqCanonicity</a>
<a id="772" class="Keyword">import</a> <a id="779" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a>
<a id="802" class="Keyword">import</a> <a id="809" href="POPL.Equational.html" class="Module">POPL.Equational</a>
<a id="825" class="Keyword">import</a> <a id="832" href="POPL.EquationalSoundness.html" class="Module">POPL.EquationalSoundness</a>
<a id="857" class="Keyword">import</a> <a id="864" href="POPL.Fin.html" class="Module">POPL.Fin</a>
<a id="873" class="Keyword">import</a> <a id="880" href="POPL.FreeModel.html" class="Module">POPL.FreeModel</a>
<a id="895" class="Keyword">import</a> <a id="902" href="POPL.Instances.Common.html" class="Module">POPL.Instances.Common</a>
<a id="924" class="Keyword">import</a> <a id="931" href="POPL.Instances.Errors.html" class="Module">POPL.Instances.Errors</a>
<a id="953" class="Keyword">import</a> <a id="960" href="POPL.Instances.State.html" class="Module">POPL.Instances.State</a>
<a id="981" class="Keyword">import</a> <a id="988" href="POPL.Instances.WeightedMonoid.html" class="Module">POPL.Instances.WeightedMonoid</a>
<a id="1018" class="Keyword">import</a> <a id="1025" href="POPL.Instances.WeightedMonoidAffine.html" class="Module">POPL.Instances.WeightedMonoidAffine</a>
<a id="1061" class="Keyword">import</a> <a id="1068" href="POPL.Instances.WeightedMonoidRules.html" class="Module">POPL.Instances.WeightedMonoidRules</a>
<a id="1103" class="Keyword">import</a> <a id="1110" href="POPL.Instances.Writer.html" class="Module">POPL.Instances.Writer</a>
<a id="1132" class="Keyword">import</a> <a id="1139" href="POPL.Models.html" class="Module">POPL.Models</a>
<a id="1151" class="Keyword">import</a> <a id="1158" href="POPL.MonadContainer.Base.html" class="Module">POPL.MonadContainer.Base</a>
<a id="1183" class="Keyword">import</a> <a id="1190" href="POPL.MonadContainer.ConfigNormalization.html" class="Module">POPL.MonadContainer.ConfigNormalization</a>
<a id="1230" class="Keyword">import</a> <a id="1237" href="POPL.MonadContainer.ConfigReduction.html" class="Module">POPL.MonadContainer.ConfigReduction</a>
<a id="1273" class="Keyword">import</a> <a id="1280" href="POPL.MonadContainer.Equiv.html" class="Module">POPL.MonadContainer.Equiv</a>
<a id="1306" class="Keyword">import</a> <a id="1313" href="POPL.MonadContainer.OperationalModel.html" class="Module">POPL.MonadContainer.OperationalModel</a>
<a id="1350" class="Keyword">import</a> <a id="1357" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a>
<a id="1380" class="Keyword">import</a> <a id="1387" href="POPL.OperationalModel.html" class="Module">POPL.OperationalModel</a>
<a id="1409" class="Keyword">import</a> <a id="1416" href="POPL.Plug.html" class="Module">POPL.Plug</a>
<a id="1426" class="Keyword">import</a> <a id="1433" href="POPL.Polynomial.html" class="Module">POPL.Polynomial</a>
<a id="1449" class="Keyword">import</a> <a id="1456" href="POPL.Renaming.html" class="Module">POPL.Renaming</a>
<a id="1470" class="Keyword">import</a> <a id="1477" href="POPL.Substitution.html" class="Module">POPL.Substitution</a>
<a id="1495" class="Keyword">import</a> <a id="1502" href="POPL.Syntax.html" class="Module">POPL.Syntax</a>
<a id="1514" class="Keyword">import</a> <a id="1521" href="POPL.Theory.html" class="Module">POPL.Theory</a>
<a id="1533" class="Keyword">import</a> <a id="1540" href="POPL.TreeCanonicity.html" class="Module">POPL.TreeCanonicity</a>
<a id="1560" class="Keyword">import</a> <a id="1567" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a>
<a id="1590" class="Keyword">import</a> <a id="1597" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a>
<a id="1616" class="Keyword">import</a> <a id="1623" href="POPL.TreeSoundness.html" class="Module">POPL.TreeSoundness</a>
<a id="1642" class="Keyword">import</a> <a id="1649" href="POPL.Types.html" class="Module">POPL.Types</a>
</pre>
## Build

The project depends only on the `cubical` library. The file `libraries` is ignored by git and lists the path to `cubical.agda-lib`.

```bash
agda --library-file=libraries Everything.lagda.md
```

`Everything.lagda.md` is this README as literate Agda: it imports every module, and its code blocks list the definitions for each result of the paper. To get the browsable HTML, in which every name links to its definition, run

```bash
agda --library-file=libraries --html --html-highlight=auto --html-dir=html Everything.lagda.md
```

This writes one `.html` page per module, plus `html/Everything.md`: Markdown prose with highlighted, hyperlinked code blocks, for a Markdown renderer such as Jekyll.

`./check.sh FILE` checks a single module with a time and memory cap.

## Design choices

- **Syntax.** One mode-indexed syntax covers both calculi:
  - mode `cbpv` is CBPV(𝒯);
  - mode `cbpv⁺` adds Fig. 1's grey rules (complex values and complex stacks).

  Terms are intrinsically typed, with list contexts (non-unary) and de Bruijn variables. The metatheory is proved once for both modes.
- **Equations.** The equational theory of CBPV⁺ is an inductive relation `≈` on plain terms, not a quotient.
- **Semantics.** The denotational semantics and both logical relations are defined directly, without the CBPV doctrine or gluing. Their fundamental theorems are proved by induction on terms.
- **Operational models.** The main development uses the paper's definition. `POPL/MonadContainer/` repeats §5 with operational models defined as monad containers (Uustalu), with operations given by generic effects, and proves the two definitions equivalent (D15).
- **Effect rule.** Configuration reduction uses the derivative form of the Effect rule, `C⟪S[op M⃗]⟫ ↦T μ((∂η C)⟪⟦op⟧(η(S[M⃗]))⟫)`. Affinity is stated through the generic step.

## Paper → Agda

### Algebraic theories, free model monads, and the syntax (§2)

<pre class="Agda"><a id="3596" class="Comment">-- §2.1 signatures, terms, equations, algebras, models</a>
<a id="3651" class="Keyword">open</a> <a id="3656" href="POPL.Theory.html" class="Module">POPL.Theory</a> <a id="3668" class="Keyword">using</a> <a id="3674" class="Symbol">(</a><a id="3675" href="POPL.Theory.html#675" class="Record">Signature</a><a id="3684" class="Symbol">;</a> <a id="3686" href="POPL.Theory.html#825" class="Datatype">Term</a><a id="3690" class="Symbol">;</a> <a id="3692" href="POPL.Theory.html#2041" class="Record">Theory</a><a id="3698" class="Symbol">;</a> <a id="3700" href="POPL.Theory.html#2402" class="Record">Model</a><a id="3705" class="Symbol">;</a> <a id="3707" href="POPL.Theory.html#1461" class="Record">IsHom</a><a id="3712" class="Symbol">)</a>

<a id="3715" class="Comment">-- §2.1 free model monad</a>
<a id="3740" class="Keyword">open</a> <a id="3745" href="POPL.FreeModel.html" class="Module">POPL.FreeModel</a> <a id="3760" class="Keyword">using</a> <a id="3766" class="Symbol">(</a><a id="3767" href="POPL.FreeModel.html#745" class="Record">FreeModel</a><a id="3776" class="Symbol">)</a>
<a id="3778" class="Keyword">open</a> <a id="3783" href="POPL.FreeModel.html#745" class="Module">POPL.FreeModel.FreeModel</a> <a id="3808" class="Keyword">using</a> <a id="3814" class="Symbol">(</a><a id="3815" href="POPL.FreeModel.html#1223" class="Field">ext-uniq</a><a id="3823" class="Symbol">;</a> <a id="3825" href="POPL.FreeModel.html#1632" class="Function">μ</a><a id="3826" class="Symbol">;</a> <a id="3828" href="POPL.FreeModel.html#1555" class="Function">map</a><a id="3831" class="Symbol">)</a>

<a id="3834" class="Comment">-- §2.3 Fig. 1 syntax of CBPV(𝒯) and CBPV⁺(𝒯)</a>
<a id="3880" class="Keyword">open</a> <a id="3885" href="POPL.Types.html" class="Module">POPL.Types</a> <a id="3896" class="Keyword">using</a> <a id="3902" class="Symbol">(</a><a id="3903" href="POPL.Types.html#499" class="Datatype">VTy</a><a id="3906" class="Symbol">;</a> <a id="3908" href="POPL.Types.html#515" class="Datatype">CTy</a><a id="3911" class="Symbol">;</a> <a id="3913" href="POPL.Types.html#1215" class="Datatype">Mode</a><a id="3917" class="Symbol">)</a>
<a id="3919" class="Keyword">open</a> <a id="3924" href="POPL.Syntax.html" class="Module">POPL.Syntax</a> <a id="3936" class="Keyword">using</a> <a id="3942" class="Symbol">(</a><a id="3943" href="POPL.Syntax.html#1048" class="Datatype">Val</a><a id="3946" class="Symbol">;</a> <a id="3948" href="POPL.Syntax.html#1093" class="Datatype">Comp</a><a id="3952" class="Symbol">;</a> <a id="3954" href="POPL.Syntax.html#1138" class="Datatype">Stack</a><a id="3959" class="Symbol">)</a>

<a id="3962" class="Comment">-- §2.3 Fig. 2 operations: V[γ], M[γ], S[γ], δ[γ], S[M], S&#39;[S]</a>
<a id="4025" class="Keyword">open</a> <a id="4030" href="POPL.Renaming.html" class="Module">POPL.Renaming</a> <a id="4044" class="Keyword">using</a> <a id="4050" class="Symbol">(</a><a id="4051" href="POPL.Renaming.html#730" class="Function">renC</a><a id="4055" class="Symbol">)</a>
<a id="4057" class="Keyword">open</a> <a id="4062" href="POPL.Substitution.html" class="Module">POPL.Substitution</a> <a id="4080" class="Keyword">using</a> <a id="4086" class="Symbol">(</a><a id="4087" href="POPL.Substitution.html#762" class="Function">subV</a><a id="4091" class="Symbol">;</a> <a id="4093" href="POPL.Substitution.html#805" class="Function">subC</a><a id="4097" class="Symbol">;</a> <a id="4099" href="POPL.Substitution.html#850" class="Function">subS</a><a id="4103" class="Symbol">;</a> <a id="4105" href="POPL.Substitution.html#2412" class="Function Operator">_⊚_</a><a id="4108" class="Symbol">)</a>
<a id="4110" class="Keyword">open</a> <a id="4115" href="POPL.Plug.html" class="Module">POPL.Plug</a> <a id="4125" class="Keyword">using</a> <a id="4131" class="Symbol">(</a><a id="4132" href="POPL.Plug.html#454" class="Function">plug</a><a id="4136" class="Symbol">;</a> <a id="4138" href="POPL.Plug.html#814" class="Function Operator">_∘ˢ_</a><a id="4142" class="Symbol">;</a> <a id="4144" href="POPL.Plug.html#1893" class="Function">plug-sub</a><a id="4152" class="Symbol">)</a>

<a id="4155" class="Comment">-- §2.3 Fig. 2 equational theory</a>
<a id="4188" class="Keyword">open</a> <a id="4193" href="POPL.Equational.html" class="Module">POPL.Equational</a> <a id="4209" class="Keyword">using</a> <a id="4215" class="Symbol">(</a><a id="4216" href="POPL.Equational.html#3013" class="Datatype Operator">_≈v_</a><a id="4220" class="Symbol">;</a> <a id="4222" href="POPL.Equational.html#3074" class="Datatype Operator">_≈c_</a><a id="4226" class="Symbol">)</a>
</pre>
### Denotational semantics and equational canonicity (§3)

<pre class="Agda"><a id="4300" class="Comment">-- §3.2 Fig. 3 denotational semantics</a>
<a id="4338" class="Keyword">open</a> <a id="4343" href="POPL.Denotation.html" class="Module">POPL.Denotation</a> <a id="4359" class="Keyword">using</a> <a id="4365" class="Symbol">(</a><a id="4366" href="POPL.Denotation.html#1525" class="Function Operator">⟦_⟧v</a><a id="4370" class="Symbol">;</a> <a id="4372" href="POPL.Denotation.html#1543" class="Function Operator">⟦_⟧c</a><a id="4376" class="Symbol">;</a> <a id="4378" href="POPL.Denotation.html#2117" class="Function Operator">⟦_⟧V</a><a id="4382" class="Symbol">;</a> <a id="4384" href="POPL.Denotation.html#2151" class="Function Operator">⟦_⟧C</a><a id="4388" class="Symbol">;</a> <a id="4390" href="POPL.Denotation.html#2185" class="Function Operator">⟦_⟧S</a><a id="4394" class="Symbol">)</a>
<a id="4396" class="Keyword">open</a> <a id="4401" href="POPL.Models.html#350" class="Module">POPL.Models.Models-of</a> <a id="4423" class="Keyword">using</a> <a id="4429" class="Symbol">(</a><a id="4430" href="POPL.Models.html#949" class="Function">powModel</a><a id="4438" class="Symbol">;</a> <a id="4440" href="POPL.Models.html#1889" class="Function">prodModel</a><a id="4449" class="Symbol">)</a>

<a id="4452" class="Comment">-- §3.2 the denotation preserves substitution, plugging and operations</a>
<a id="4523" class="Keyword">open</a> <a id="4528" href="POPL.DenotationLemmas.html" class="Module">POPL.DenotationLemmas</a> <a id="4550" class="Keyword">using</a> <a id="4556" class="Symbol">(</a><a id="4557" href="POPL.DenotationLemmas.html#6656" class="Function">den-subC</a><a id="4565" class="Symbol">;</a> <a id="4567" href="POPL.DenotationLemmas.html#11466" class="Function">den-plug</a><a id="4575" class="Symbol">;</a> <a id="4577" href="POPL.DenotationLemmas.html#12237" class="Function">den-stack-hom</a><a id="4590" class="Symbol">)</a>

<a id="4593" class="Comment">-- §3.2 soundness of ⟦-⟧ for the equations</a>
<a id="4636" class="Keyword">open</a> <a id="4641" href="POPL.EquationalSoundness.html" class="Module">POPL.EquationalSoundness</a> <a id="4666" class="Keyword">using</a> <a id="4672" class="Symbol">(</a><a id="4673" href="POPL.EquationalSoundness.html#1966" class="Function">sound-c</a><a id="4680" class="Symbol">)</a>

<a id="4683" class="Comment">-- §3.3 Fig. 6 equational logical relation</a>
<a id="4726" class="Keyword">open</a> <a id="4731" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="4754" class="Keyword">using</a> <a id="4760" class="Symbol">(</a><a id="4761" href="POPL.EqLogicalRelation.html#1918" class="Function Operator">𝒱⟦_⟧</a><a id="4765" class="Symbol">;</a> <a id="4767" href="POPL.EqLogicalRelation.html#1951" class="Function Operator">𝒞⟦_⟧</a><a id="4771" class="Symbol">;</a> <a id="4773" href="POPL.EqLogicalRelation.html#1654" class="Datatype">FPred</a><a id="4778" class="Symbol">)</a>

<a id="4781" class="Comment">-- §3.4 Fundamental Theorem</a>
<a id="4809" class="Keyword">open</a> <a id="4814" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="4837" class="Keyword">using</a> <a id="4843" class="Symbol">(</a><a id="4844" href="POPL.EqLogicalRelation.html#4697" class="Function">fundV</a><a id="4849" class="Symbol">;</a> <a id="4851" href="POPL.EqLogicalRelation.html#4729" class="Function">fundC</a><a id="4856" class="Symbol">)</a>

<a id="4859" class="Comment">-- §3.4 Corollary (equational canonicity)</a>
<a id="4901" class="Keyword">open</a> <a id="4906" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="4929" class="Keyword">using</a> <a id="4935" class="Symbol">(</a><a id="4936" href="POPL.EqLogicalRelation.html#8241" class="Function">equational-canonicity</a><a id="4957" class="Symbol">)</a>

<a id="4960" class="Comment">-- §3.4 Corollary (uniqueness; corrected, C3)</a>
<a id="5006" class="Keyword">open</a> <a id="5011" href="POPL.EqCanonicity.html" class="Module">POPL.EqCanonicity</a> <a id="5029" class="Keyword">using</a> <a id="5035" class="Symbol">(</a><a id="5036" href="POPL.EqCanonicity.html#1862" class="Function">canonical-form-unique</a><a id="5057" class="Symbol">)</a>
</pre>
### Tree reduction (§4)

<pre class="Agda"><a id="5097" class="Comment">-- §4.1 Fig. 5 tree reduction</a>
<a id="5127" class="Keyword">open</a> <a id="5132" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a> <a id="5151" class="Keyword">using</a> <a id="5157" class="Symbol">(</a><a id="5158" href="POPL.TreeReduction.html#1982" class="Datatype Operator">_↦red_</a><a id="5164" class="Symbol">;</a> <a id="5166" href="POPL.TreeReduction.html#2948" class="Datatype Operator">_↦h_</a><a id="5170" class="Symbol">;</a> <a id="5172" href="POPL.TreeReduction.html#3204" class="Datatype Operator">_↦_</a><a id="5175" class="Symbol">;</a> <a id="5177" href="POPL.TreeReduction.html#11340" class="Function">det</a><a id="5180" class="Symbol">)</a>

<a id="5183" class="Comment">-- §4.1 Theorem (soundness of ↦tree)</a>
<a id="5220" class="Keyword">open</a> <a id="5225" href="POPL.TreeSoundness.html" class="Module">POPL.TreeSoundness</a> <a id="5244" class="Keyword">using</a> <a id="5250" class="Symbol">(</a><a id="5251" href="POPL.TreeSoundness.html#1747" class="Function">sound↦</a><a id="5257" class="Symbol">)</a>

<a id="5260" class="Comment">-- §4.2 Fig. 7 operational logical relation</a>
<a id="5304" class="Keyword">open</a> <a id="5309" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="5332" class="Keyword">using</a> <a id="5338" class="Symbol">(</a><a id="5339" href="POPL.OpLogicalRelation.html#5256" class="Function Operator">𝒱⟦_⟧</a><a id="5343" class="Symbol">;</a> <a id="5345" href="POPL.OpLogicalRelation.html#5289" class="Function Operator">𝒞⟦_⟧</a><a id="5349" class="Symbol">;</a> <a id="5351" href="POPL.OpLogicalRelation.html#4983" class="Datatype">FPred</a><a id="5356" class="Symbol">)</a>

<a id="5359" class="Comment">-- §4.2 Lemma (anti-reduction; corrected, C5)</a>
<a id="5405" class="Keyword">open</a> <a id="5410" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a> <a id="5429" class="Keyword">using</a> <a id="5435" class="Symbol">(</a><a id="5436" href="POPL.TreeReduction.html#12231" class="Function">hjoin</a><a id="5441" class="Symbol">)</a>
<a id="5443" class="Keyword">open</a> <a id="5448" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="5471" class="Keyword">using</a> <a id="5477" class="Symbol">(</a><a id="5478" href="POPL.OpLogicalRelation.html#5911" class="Function">AR</a><a id="5480" class="Symbol">;</a> <a id="5482" href="POPL.OpLogicalRelation.html#5976" class="Function">FW</a><a id="5484" class="Symbol">)</a>

<a id="5487" class="Comment">-- §4.2 Lemma (congruence)</a>
<a id="5514" class="Keyword">open</a> <a id="5519" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="5542" class="Keyword">using</a> <a id="5548" class="Symbol">(</a><a id="5549" href="POPL.OpLogicalRelation.html#7469" class="Function">𝒞-op</a><a id="5553" class="Symbol">)</a>

<a id="5556" class="Comment">-- §4.3 Fundamental Lemma</a>
<a id="5582" class="Keyword">open</a> <a id="5587" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="5610" class="Keyword">using</a> <a id="5616" class="Symbol">(</a><a id="5617" href="POPL.OpLogicalRelation.html#9896" class="Function">fundV</a><a id="5622" class="Symbol">;</a> <a id="5624" href="POPL.OpLogicalRelation.html#9932" class="Function">fundC</a><a id="5629" class="Symbol">;</a> <a id="5631" href="POPL.OpLogicalRelation.html#11374" class="Function">related</a><a id="5638" class="Symbol">)</a>

<a id="5641" class="Comment">-- §4.3 Corollary (termination)</a>
<a id="5673" class="Keyword">open</a> <a id="5678" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="5701" class="Keyword">using</a> <a id="5707" class="Symbol">(</a><a id="5708" href="POPL.TreeNormalization.html#4103" class="Function">termination</a><a id="5719" class="Symbol">)</a>

<a id="5722" class="Comment">-- §4.3 Corollary (strong normalization)</a>
<a id="5763" class="Keyword">open</a> <a id="5768" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="5791" class="Keyword">using</a> <a id="5797" class="Symbol">(</a><a id="5798" href="POPL.TreeNormalization.html#6686" class="Function">strong-normalization</a><a id="5818" class="Symbol">)</a>

<a id="5821" class="Comment">-- §4.3 Corollary (canonicity; corrected, C8)</a>
<a id="5867" class="Keyword">open</a> <a id="5872" href="POPL.TreeCanonicity.html" class="Module">POPL.TreeCanonicity</a> <a id="5892" class="Keyword">using</a> <a id="5898" class="Symbol">(</a><a id="5899" href="POPL.TreeCanonicity.html#1406" class="Function">tree-canonicity</a><a id="5914" class="Symbol">)</a>
</pre>
### Configuration reduction (§5)

<pre class="Agda"><a id="5963" class="Comment">-- §5.2 polynomials, ∂p, plugging</a>
<a id="5997" class="Keyword">open</a> <a id="6002" href="POPL.Polynomial.html" class="Module">POPL.Polynomial</a> <a id="6018" class="Keyword">using</a> <a id="6024" class="Symbol">(</a><a id="6025" href="POPL.Polynomial.html#1032" class="Record">Poly</a><a id="6029" class="Symbol">;</a> <a id="6031" href="POPL.Polynomial.html#1126" class="Function Operator">⟦_⟧</a><a id="6034" class="Symbol">;</a> <a id="6036" href="POPL.Polynomial.html#1421" class="Function">∂</a><a id="6037" class="Symbol">;</a> <a id="6039" href="POPL.Polynomial.html#1828" class="Function">plug</a><a id="6043" class="Symbol">;</a> <a id="6045" href="POPL.Polynomial.html#2386" class="Function">plug-map</a><a id="6053" class="Symbol">)</a>

<a id="6056" class="Comment">-- §5.2 Def. (Operational Model)</a>
<a id="6089" class="Keyword">open</a> <a id="6094" href="POPL.OperationalModel.html" class="Module">POPL.OperationalModel</a> <a id="6116" class="Keyword">using</a> <a id="6122" class="Symbol">(</a><a id="6123" href="POPL.OperationalModel.html#417" class="Record">OperationalModel</a><a id="6139" class="Symbol">)</a>
<a id="6141" class="Keyword">open</a> <a id="6146" href="POPL.OperationalModel.html#417" class="Module">POPL.OperationalModel.OperationalModel</a> <a id="6185" class="Keyword">using</a> <a id="6191" class="Symbol">(</a><a id="6192" href="POPL.OperationalModel.html#622" class="Field">map-poly</a><a id="6200" class="Symbol">)</a>

<a id="6203" class="Comment">-- §5.3 Fig. &quot;Configuration Reduction&quot; (derivative form)</a>
<a id="6260" class="Keyword">open</a> <a id="6265" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="6286" class="Keyword">using</a> <a id="6292" class="Symbol">(</a><a id="6293" href="POPL.ConfigReduction.html#2128" class="Datatype Operator">_↦T_</a><a id="6297" class="Symbol">)</a>

<a id="6300" class="Comment">-- §5.3 Theorem (soundness of the initial configuration)</a>
<a id="6357" class="Keyword">open</a> <a id="6362" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="6383" class="Keyword">using</a> <a id="6389" class="Symbol">(</a><a id="6390" href="POPL.ConfigReduction.html#2938" class="Function">sound-init</a><a id="6400" class="Symbol">)</a>

<a id="6403" class="Comment">-- §5.3 Theorem (soundness of ↦T)</a>
<a id="6437" class="Keyword">open</a> <a id="6442" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="6463" class="Keyword">using</a> <a id="6469" class="Symbol">(</a><a id="6470" href="POPL.ConfigReduction.html#3612" class="Function">sound-T</a><a id="6477" class="Symbol">)</a>

<a id="6480" class="Comment">-- §5.4 Def. (Affinity), and appendix &quot;Simplification&quot;</a>
<a id="6535" class="Keyword">open</a> <a id="6540" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="6561" class="Keyword">using</a> <a id="6567" class="Symbol">(</a><a id="6568" href="POPL.ConfigReduction.html#4970" class="Function">step</a><a id="6572" class="Symbol">;</a> <a id="6574" href="POPL.ConfigReduction.html#5250" class="Function">ρ</a><a id="6575" class="Symbol">;</a> <a id="6577" href="POPL.ConfigReduction.html#5536" class="Function">Affine</a><a id="6583" class="Symbol">;</a> <a id="6585" href="POPL.ConfigReduction.html#5718" class="Function">simplification</a><a id="6599" class="Symbol">;</a> <a id="6601" href="POPL.ConfigReduction.html#6377" class="Function">effect-via-step</a><a id="6616" class="Symbol">)</a>

<a id="6619" class="Comment">-- §5.4 Lemma (Progress)</a>
<a id="6644" class="Keyword">open</a> <a id="6649" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6674" class="Keyword">using</a> <a id="6680" class="Symbol">(</a><a id="6681" href="POPL.ConfigNormalization.html#8153" class="Function">progress-T</a><a id="6691" class="Symbol">)</a>

<a id="6694" class="Comment">-- §5.4 Def. (Termination Metric; corrected, C7)</a>
<a id="6743" class="Keyword">open</a> <a id="6748" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="6771" class="Keyword">using</a> <a id="6777" class="Symbol">(</a><a id="6778" href="POPL.TreeNormalization.html#4346" class="Function">size</a><a id="6782" class="Symbol">;</a> <a id="6784" href="POPL.TreeNormalization.html#6016" class="Function Operator">‖_‖</a><a id="6787" class="Symbol">)</a>
<a id="6789" class="Keyword">open</a> <a id="6794" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6819" class="Keyword">using</a> <a id="6825" class="Symbol">(</a><a id="6826" href="POPL.ConfigNormalization.html#5205" class="Function Operator">‖_‖T</a><a id="6830" class="Symbol">)</a>

<a id="6833" class="Comment">-- §5.4 Theorem (strong normalization for ↦T)</a>
<a id="6879" class="Keyword">open</a> <a id="6884" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6909" class="Keyword">using</a> <a id="6915" class="Symbol">(</a><a id="6916" href="POPL.ConfigNormalization.html#7236" class="Function">strong-normalization-T</a><a id="6938" class="Symbol">;</a> <a id="6940" href="POPL.ConfigNormalization.html#8949" class="Function">normalize-T</a><a id="6951" class="Symbol">;</a> <a id="6953" href="POPL.ConfigNormalization.html#9367" class="Function">canonicity-T</a><a id="6965" class="Symbol">)</a>

<a id="6968" class="Comment">-- §5.4 Lemma (uniqueness of the result)</a>
<a id="7009" class="Keyword">open</a> <a id="7014" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="7039" class="Keyword">using</a> <a id="7045" class="Symbol">(</a><a id="7046" href="POPL.ConfigNormalization.html#9893" class="Function">final-unique</a><a id="7058" class="Symbol">;</a> <a id="7060" href="POPL.ConfigNormalization.html#11328" class="Function">ground-canonicity</a><a id="7077" class="Symbol">)</a>

<a id="7080" class="Comment">-- §5.2 monad containers (Uustalu), and the equivalence of their two sets of laws (D15)</a>
<a id="7168" class="Keyword">open</a> <a id="7173" href="POPL.MonadContainer.Base.html" class="Module">POPL.MonadContainer.Base</a> <a id="7198" class="Keyword">using</a> <a id="7204" class="Symbol">(</a><a id="7205" href="POPL.MonadContainer.Base.html#1617" class="Record">MCOps</a><a id="7210" class="Symbol">;</a> <a id="7212" href="POPL.MonadContainer.Base.html#2212" class="Record">MonadLaws</a><a id="7221" class="Symbol">;</a> <a id="7223" href="POPL.MonadContainer.Base.html#2486" class="Record">UustaluLaws</a><a id="7234" class="Symbol">;</a> <a id="7236" href="POPL.MonadContainer.Base.html#4731" class="Function">M→U</a><a id="7239" class="Symbol">;</a> <a id="7241" href="POPL.MonadContainer.Base.html#4079" class="Function">U→M</a><a id="7244" class="Symbol">;</a> <a id="7246" href="POPL.MonadContainer.Base.html#5696" class="Record">MonadContainer</a><a id="7260" class="Symbol">)</a>

<a id="7263" class="Comment">-- §5.2 Def. (Operational Model) as a monad container (D15)</a>
<a id="7323" class="Keyword">open</a> <a id="7328" href="POPL.MonadContainer.OperationalModel.html" class="Module">POPL.MonadContainer.OperationalModel</a> <a id="7365" class="Keyword">using</a> <a id="7371" class="Symbol">(</a><a id="7372" href="POPL.MonadContainer.OperationalModel.html#1612" class="Record">OperationalModel</a><a id="7388" class="Symbol">)</a>
<a id="7390" class="Keyword">open</a> <a id="7395" href="POPL.MonadContainer.OperationalModel.html#1612" class="Module">POPL.MonadContainer.OperationalModel.OperationalModel</a> <a id="7449" class="Keyword">using</a> <a id="7455" class="Symbol">(</a><a id="7456" href="POPL.MonadContainer.OperationalModel.html#1811" class="Field">gen</a><a id="7459" class="Symbol">;</a> <a id="7461" href="POPL.MonadContainer.OperationalModel.html#3087" class="Function">μₘ≡μ</a><a id="7465" class="Symbol">;</a> <a id="7467" href="POPL.MonadContainer.OperationalModel.html#3296" class="Function">map-poly</a><a id="7475" class="Symbol">)</a>

<a id="7478" class="Comment">-- §5.3–5.4 for monad-container operational models (D15)</a>
<a id="7535" class="Keyword">open</a> <a id="7540" href="POPL.MonadContainer.ConfigReduction.html" class="Module">POPL.MonadContainer.ConfigReduction</a> <a id="7576" class="Keyword">using</a> <a id="7582" class="Symbol">(</a><a id="7583" href="POPL.MonadContainer.ConfigReduction.html#1604" class="Datatype Operator">_↦T_</a><a id="7587" class="Symbol">;</a> <a id="7589" href="POPL.MonadContainer.ConfigReduction.html#3089" class="Function">sound-T</a><a id="7596" class="Symbol">;</a> <a id="7598" href="POPL.MonadContainer.ConfigReduction.html#5277" class="Function">step-shape</a><a id="7608" class="Symbol">;</a> <a id="7610" href="POPL.MonadContainer.ConfigReduction.html#5354" class="Function">step-pos</a><a id="7618" class="Symbol">;</a> <a id="7620" href="POPL.MonadContainer.ConfigReduction.html#5648" class="Function">Affine</a><a id="7626" class="Symbol">)</a>
<a id="7628" class="Keyword">open</a> <a id="7633" href="POPL.MonadContainer.ConfigNormalization.html" class="Module">POPL.MonadContainer.ConfigNormalization</a> <a id="7673" class="Keyword">using</a> <a id="7679" class="Symbol">(</a><a id="7680" href="POPL.MonadContainer.ConfigNormalization.html#6583" class="Function">strong-normalization-T</a><a id="7702" class="Symbol">;</a> <a id="7704" href="POPL.MonadContainer.ConfigNormalization.html#8714" class="Function">canonicity-T</a><a id="7716" class="Symbol">;</a> <a id="7718" href="POPL.MonadContainer.ConfigNormalization.html#10675" class="Function">ground-canonicity</a><a id="7735" class="Symbol">)</a>
</pre>
### Instances (§2.2, §5.3)

<pre class="Agda"><a id="7778" class="Comment">-- the two definitions of operational model are equivalent (D15)</a>
<a id="7843" class="Keyword">open</a> <a id="7848" href="POPL.MonadContainer.Equiv.html" class="Module">POPL.MonadContainer.Equiv</a> <a id="7874" class="Keyword">using</a> <a id="7880" class="Symbol">(</a><a id="7881" href="POPL.MonadContainer.Equiv.html#1550" class="Function">toPoly</a><a id="7887" class="Symbol">;</a> <a id="7889" href="POPL.MonadContainer.Equiv.html#4784" class="Function">fromPoly</a><a id="7897" class="Symbol">;</a> <a id="7899" href="POPL.MonadContainer.Equiv.html#5121" class="Function">fromPoly-η</a><a id="7909" class="Symbol">;</a> <a id="7911" href="POPL.MonadContainer.Equiv.html#5221" class="Function">fromPoly-μ</a><a id="7921" class="Symbol">;</a> <a id="7923" href="POPL.MonadContainer.Equiv.html#5326" class="Function">fromPoly-ops</a><a id="7935" class="Symbol">;</a> <a id="7937" href="POPL.MonadContainer.Equiv.html#5794" class="Function">roundtrip-•</a><a id="7948" class="Symbol">)</a>

<a id="7951" class="Comment">-- Writer: theory, free model, affinity, derived rule</a>
<a id="8005" class="Keyword">open</a> <a id="8010" href="POPL.Instances.Writer.html" class="Module">POPL.Instances.Writer</a> <a id="8032" class="Keyword">using</a> <a id="8038" class="Symbol">(</a><a id="8039" href="POPL.Instances.Writer.html#1667" class="Function">writerTheory</a><a id="8051" class="Symbol">;</a> <a id="8053" href="POPL.Instances.Writer.html#2989" class="Function">writerFree</a><a id="8063" class="Symbol">;</a> <a id="8065" href="POPL.Instances.Writer.html#3544" class="Function">writerOM</a><a id="8073" class="Symbol">;</a> <a id="8075" href="POPL.Instances.Writer.html#3846" class="Function">writer-affine</a><a id="8088" class="Symbol">;</a> <a id="8090" href="POPL.Instances.Writer.html#4117" class="Function">writer-effect</a><a id="8103" class="Symbol">)</a>

<a id="8106" class="Comment">-- Errors</a>
<a id="8116" class="Keyword">open</a> <a id="8121" href="POPL.Instances.Errors.html" class="Module">POPL.Instances.Errors</a> <a id="8143" class="Keyword">using</a> <a id="8149" class="Symbol">(</a><a id="8150" href="POPL.Instances.Errors.html#957" class="Function">errTheory</a><a id="8159" class="Symbol">;</a> <a id="8161" href="POPL.Instances.Errors.html#2032" class="Function">errFree</a><a id="8168" class="Symbol">;</a> <a id="8170" href="POPL.Instances.Errors.html#2291" class="Function">errOM</a><a id="8175" class="Symbol">;</a> <a id="8177" href="POPL.Instances.Errors.html#2585" class="Function">err-affine</a><a id="8187" class="Symbol">;</a> <a id="8189" href="POPL.Instances.Errors.html#2910" class="Function">err-effect</a><a id="8199" class="Symbol">)</a>

<a id="8202" class="Comment">-- Boolean state, and the get and set rules</a>
<a id="8246" class="Keyword">open</a> <a id="8251" href="POPL.Instances.State.html" class="Module">POPL.Instances.State</a> <a id="8272" class="Keyword">using</a> <a id="8278" class="Symbol">(</a><a id="8279" href="POPL.Instances.State.html#2503" class="Function">stateTheory</a><a id="8290" class="Symbol">;</a> <a id="8292" href="POPL.Instances.State.html#6038" class="Function">stateFree</a><a id="8301" class="Symbol">;</a> <a id="8303" href="POPL.Instances.State.html#6262" class="Function">stateOM</a><a id="8310" class="Symbol">;</a> <a id="8312" href="POPL.Instances.State.html#6843" class="Function">state-affine</a><a id="8324" class="Symbol">;</a> <a id="8326" href="POPL.Instances.State.html#7922" class="Function">state-get</a><a id="8335" class="Symbol">;</a> <a id="8337" href="POPL.Instances.State.html#8287" class="Function">state-set</a><a id="8346" class="Symbol">)</a>

<a id="8349" class="Comment">-- Weighted monoid</a>
<a id="8368" class="Keyword">open</a> <a id="8373" href="POPL.Instances.WeightedMonoid.html" class="Module">POPL.Instances.WeightedMonoid</a> <a id="8403" class="Keyword">using</a> <a id="8409" class="Symbol">(</a><a id="8410" href="POPL.Instances.WeightedMonoid.html#3428" class="Function">wmTheory</a><a id="8418" class="Symbol">;</a> <a id="8420" href="POPL.Instances.WeightedMonoid.html#11826" class="Function">wmFree</a><a id="8426" class="Symbol">;</a> <a id="8428" href="POPL.Instances.WeightedMonoid.html#13605" class="Function">wmOM</a><a id="8432" class="Symbol">)</a>
<a id="8434" class="Keyword">open</a> <a id="8439" href="POPL.Instances.WeightedMonoidAffine.html" class="Module">POPL.Instances.WeightedMonoidAffine</a> <a id="8475" class="Keyword">using</a> <a id="8481" class="Symbol">(</a><a id="8482" href="POPL.Instances.WeightedMonoidAffine.html#5703" class="Function">wm-affine</a><a id="8491" class="Symbol">)</a>
<a id="8493" class="Keyword">open</a> <a id="8498" href="POPL.Instances.WeightedMonoidRules.html" class="Module">POPL.Instances.WeightedMonoidRules</a> <a id="8533" class="Keyword">using</a> <a id="8539" class="Symbol">(</a><a id="8540" href="POPL.Instances.WeightedMonoidRules.html#2226" class="Function">wm-act</a><a id="8546" class="Symbol">;</a> <a id="8548" href="POPL.Instances.WeightedMonoidRules.html#2765" class="Function">wm-unit</a><a id="8555" class="Symbol">;</a> <a id="8557" href="POPL.Instances.WeightedMonoidRules.html#3077" class="Function">wm-mul</a><a id="8563" class="Symbol">)</a>
</pre>
## Deviations from the paper

Each entry is also a comment at the cited place in the code, under the same tag.

- **Corrections** (`C#`) fix a mistake in the paper: a typo, a missing rule, a false statement, or an incomplete proof.
- **Deviations** (`D#`) are choices of presentation. The paper's statement still holds; it is either formalized in a different but equivalent way or generalized.

### Corrections

#### C5: the Anti-reduction Lemma (§4.2) is restricted to head steps and gets a new proof

This is the largest change. [`POPL/OpLogicalRelation.agda`](POPL.OpLogicalRelation.html) gives the full account in its header.

**Paper.** The lemma says: for every `B`, if `M ↦tree M'` then `𝒞[B](M') ⇒ 𝒞[B](M)`. The proof says the cases `→` and `&` are "immediate from inductive hypothesis".

**Problem.** Those cases need `M ↦ M'` to imply `M V ↦ M' V`. Fig. 5 does not give that. The operation rule `S[op(K⃗)] ↦ op(S[K⃗])` moves the whole stack in one step:

```text
M    = (op(K₁,K₂)) W      ↦  op(K₁ W, K₂ W)      = M'
M V  = (op(K₁,K₂)) W V    ↦  op(K₁ W V, K₂ W V)
M' V = (op(K₁ W,K₂ W)) V  ↦  op(K₁ W V, K₂ W V)
```

`M V` does not step to `M' V`; the two only share a reduct. Steps under an operation fail in the same way. The paper's commented-out claim that "stacks are graph homomorphisms" is false for `↦tree`.

**Fix.**

1. The lemma is stated for head steps `↦h` only: redex steps under a stack, and operation steps. Those are the only steps the paper ever applies it to:
   - the congruence lemma uses `op(M⃗) V ↦ op(M⃗ V)`;
   - the fundamental lemma uses β-steps and the two bind sub-cases;
   - the `back` clause of `𝒞[FA]` requires `M ≠ op`, which forces a head step.
2. Anti-reduction is proved together with forward preservation, by induction on `B`. The proof uses two lemmas that are new relative to the paper:
   - **`hjoin`.** If `M ↦h M'`, then for every stack `S'`, either `S'[M] ↦h S'[M']`, or both terms head-step to a common term.
   - **Determinism of head steps.** The paper assumes this ("only one reduction applies") but never proves it. Here it is proved by computing head reduction with a function.

The logical relation and the statements of all other results are unchanged.

#### Smaller corrections

| Tag | Paper | Correction | Code |
|---|---|---|---|
| C3 | §3.4, uniqueness corollary: if `Val(A) ≅ ⟦A⟧` then `∃! t : Term_Σ(Val A). M = reify(t)`. | False when the theory has equations. For writer, `tell_e(ret V) = ret V`, so `tell_e(var V)` and `var V` both reify to `M`. What holds is uniqueness of the canonical form's image `⌊t⌋` in the free model `T⟦A⟧`, and `⌊t⌋ = ⟦M⟧`. | [`EqCanonicity.agda`](POPL.EqCanonicity.html) |
| C6 | Fig. 7 defines `𝒱[1]` only at `⋆`, and `𝒱[A+A']`, `𝒱[A×A']` only at `σᵢ W` and pairs. | Every undefined clause is read as `⊥`. In CBPV(𝒯) the only other closed values of these types have the form `absurd V`, and no closed values of type `0` exist. | [`OpLogicalRelation.agda`](POPL.OpLogicalRelation.html) |
| C7 | §5.4, Def. "Termination Metric": `\|M\| = max_{M↦N} \|N\|` for `M ≠ op`. Under this definition a pure step does not decrease the metric. | `\|M\| = 1 + \|N\|` for the unique `N`, which is unique by determinism. The metric is defined on derivations of `𝒞⟦FA⟧` and shown not to depend on the derivation. | [`TreeNormalization.agda`](POPL.TreeNormalization.html) |
| C8 | §4.3, last corollary: if `⟦·⟧_A` is a bijection, then `M ↦* reify(⟦M⟧)`. This is ill-typed: `⟦M⟧ ∈ T⟦A⟧`, but `reify` takes a `Term_Σ`. | For every `A`: there is a `t` with `M ↦* reify t` and `⌊t⌋ = ⟦M⟧` in `T⟦A⟧`. No bijection is needed. | [`TreeCanonicity.agda`](POPL.TreeCanonicity.html) |

### Deviations

#### D8: one stack rule for redexes, with no `S ≠ •` side condition

Fig. 5 lists the primitive redexes `M ↦red M'` and then the rule `S[M] ↦tree S[M']` for `M ↦red M'`, with the side condition `S ≠ •`. Read literally, the figure has no rule by which a redex at the root steps: the only rule that mentions `↦red` excludes the empty stack, so `force(thunk(ret ⋆))`, for example, would be stuck, and the Fundamental Lemma and the termination corollary would fail. The prose instead says that `↦tree` "consists of the usual β rules `↦red`", that is, `↦red ⊆ ↦tree`, and the proofs use root steps (the β cases of the Fundamental Lemma, and the first case of the bind case). Under that reading, `S ≠ •` only stops the stack rule from deriving the root steps a second time. Either way, the intended relation is that a redex reduces under any stack, including the empty one.

We formalize that intended relation with one rule, `stk : N ↦red N' → S[N] ↦h S[N']`, for every stack `S` including `•`; the root redexes are its `S = •` instances. The relation is the same as the paper's under the prose reading, and every step still has exactly one derivation. The benefit is that every head step has the same shape, a redex under a stack, so the determinism proof (`hs-stk`), the join lemma (`hjoin`) and Progress need no separate case for root redexes. The camera-ready should either drop the side condition or add the inclusion `↦red ⊆ ↦tree` to Fig. 5. The other `S ≠ •` in Fig. 5, on the operation rule `S[op(M⃗)] ↦ op(S[M⃗])`, is different and essential: with `S = •` the rule would be `op(M⃗) ↦ op(M⃗)`, a loop that breaks strong normalization and the metric. We keep it, as the `NonEmptyS S` argument of `opS` in [`TreeReduction.agda`](POPL.TreeReduction.html).

#### D15: operational models as monad containers, side by side

**Paper.** §5.2 defines an operational model as a function `T` such that `T(X)` is the free model of 𝒯 on `X` and the induced functorial action is polynomial. The rebuttal and the camera-ready plan (F14) promise to use the established notion of a *monadic container*: Uustalu's mnd-container ("Container combinatorics: monads and lax monoidal functors", TTCS 2017). Such a container is a polynomial `(S, P)` with a shape `e`, a shape multiplication `s • v`, and position maps `↖`, `↗`, whose extension is a monad with `η x = (e, λ_. x)` and `μ(s, v) = (s • v₀, λq. v₁ (↖ q) (↗ q))`.

**What we do.** The main development uses the paper's definition ([`OperationalModel.agda`](POPL.OperationalModel.html)), and the instances are built in that form. The directory [`POPL/MonadContainer/`](POPL/MonadContainer) develops the monad-container definition beside it and repeats §5 for it, rather than transporting results across an equivalence:
- [`Base.agda`](POPL.MonadContainer.Base.html): monad containers, with their laws stated in two ways. `MonadLaws` gives the three monad laws on `⟦S, P⟧ X`, as plain paths. `UustaluLaws` gives Uustalu's eight laws: three on shapes, and five on positions as dependent paths over the shape laws. `M→U` and `U→M` prove the two equivalent for the same data. `U→M` computes both sides of each monad law. `M→U` instantiates each monad law at a generic element, whose leaves are its own positions, and reads the shape law off the first component of the path and the position law off the second.
- [`OperationalModel.agda`](POPL.MonadContainer.OperationalModel.html): an operational model is a monad container (with `MonadLaws`), together with a generic effect `⌈op⌉ ∈ T(Fin ar(op))` for each operation, the equations of 𝒯, and freeness of `T(X)` on `X` with unit the container's `η`. The operations are `⟦op⟧(args) = μ(T(args)(⌈op⌉))`, the Plotkin–Power correspondence between generic effects and algebraic operations. The paper's defining condition is a theorem here (`map-poly`), as is the fact that the container's `μ` is the free model's (`μₘ≡μ`).
- [`Equiv.agda`](POPL.MonadContainer.Equiv.html): the two definitions are equivalent. `toPoly` and `fromPoly` keep the polynomial and preserve `η`, `μ` and the operations up to paths, and `fromPoly ∘ toPoly` gives back the same `e`, `•` and generic effects. `fromPoly` reads the container structure off the free model monad: `e` is the shape of `η(tt)`, and `•`, `↖`, `↗` come from `μ` applied to the generic element `(s, λp. (v p, λm. (p, m)))`. By naturality of `μ`, `μ` of every element is an image of that one, which is the container formula. This is a logical equivalence with agreement of the structure, not an isomorphism of the record types.
- [`ConfigReduction.agda`](POPL.MonadContainer.ConfigReduction.html) and [`ConfigNormalization.agda`](POPL.MonadContainer.ConfigNormalization.html) repeat §5.3–5.4 for monad-container models: configuration reduction, soundness, the generic step and affinity, strong normalization, canonicity and uniqueness. The Effect rule keeps the derivative form `C⟪S[op M⃗]⟫ ↦T μ((∂η C)⟪⟦op⟧(η(S[M⃗]))⟫)`, with the container's `η` and `μ`. As a result the paper's own definitions of `s ∘ᵢ op` and `ρ_{s,i,op}` hold by definition: the shape of the generic step is `s • vᵢ`, where `vᵢ` is the shape of `⌈op⌉` at `i` and `e` elsewhere, and its positions are given by `↖` and `↗` (`step-shape`, `step-pos`). The proofs are those of the main development, plus the lemma `μₘ≡μ`.

#### Other deviations

| Tag | Paper | Formalization | Code |
|---|---|---|---|
| D3 | `⟦-⟧` comes from initiality of the CBPV⁺ doctrine (§3.1). | `⟦-⟧` is defined directly by the recursive equations of Fig. 3. The facts initiality would provide are proved by induction: the substitution and plugging lemmas, algebraicity of stacks, and soundness for `≈`. The doctrine itself is not formalized. | [`Denotation.agda`](POPL.Denotation.html), [`DenotationLemmas.agda`](POPL.DenotationLemmas.html), [`EquationalSoundness.agda`](POPL.EquationalSoundness.html) |
| D4 | CBPV⁺ terms are a quotient by the equational theory. | Terms are plain inductive data, and the equational theory is an inductive relation `≈`. CBPV(𝒯) and CBPV⁺(𝒯) share one mode-indexed syntax (`Types.agda`); the grey rules of Fig. 1 exist only in mode `cbpv⁺`. Computations and stacks are separate types rather than one judgement with a stoup. | [`Equational.agda`](POPL.Equational.html), [`Syntax.agda`](POPL.Syntax.html) |
| D5 | Fig. 2 gives a "fragment" of the β/η laws. | The standard full set (Levy). The η laws for `+`, `×` and `0` are in substitution form. F-η is the general stack form `S[M] = x ← M; S[ret x]`. | [`Equational.agda`](POPL.Equational.html) |
| D6 | The logical relations are glued models; the fundamental theorems follow from initiality. | Relations defined by hand by recursion on types, with `𝒞⟦FA⟧` inductive. Fundamental theorems proved by induction on terms. | [`EqLogicalRelation.agda`](POPL.EqLogicalRelation.html), [`OpLogicalRelation.agda`](POPL.OpLogicalRelation.html) |
| D7 | Fig. 6 says "V = σᵢ W", "(V,V')", and so on; these presume the quotient. | The equational predicates are closed under `≈` by construction: `𝒱⟦A+A'⟧ V` asks for `V ≈ σᵢ W`, and `𝒞⟦FA⟧` has a `conv` clause. This follows from D4. | [`EqLogicalRelation.agda`](POPL.EqLogicalRelation.html) |
| D9 | Strong normalization (§4.3 for `↦tree`, §5.4 for `↦T`) is proved by a classical argument on infinite sequences. | Stated constructively as accessibility (`Acc`) for converse reduction, and derived from the decreasing metric. | [`TreeNormalization.agda`](POPL.TreeNormalization.html), [`ConfigNormalization.agda`](POPL.ConfigNormalization.html) |
| D10 | The Effect rule is written in substitution notation: `⟨s, γ, S[op M⃗]/xᵢ⟩ ↦T T(γ ⊎ S[M⃗])(T(ρ)(s ∘ᵢ op))`. | As requested, the derivative form from the appendix: `C⟪S[op M⃗]⟫ ↦T μ((∂η C)⟪⟦op⟧(η(S[M⃗]))⟫)`. Affinity is stated through the generic step `step(s,i,op) = μ(∂(η∘σ₁)(Cₛⁱ)⟪T(σ₂)⌈op⌉⟫)`, whose shape is `s ∘ᵢ op` and whose positions are `ρ`. The appendix's "Simplification" lemma, `effect-via-step`, shows that the derivative form equals the paper's form; in the monad-container version (D15) the paper's `s ∘ᵢ op` and `ρ` are the container's `•`, `↖` and `↗` by definition. | [`ConfigReduction.agda`](POPL.ConfigReduction.html) |
| D11 | Progress (§5.4) is stated for closed computations, by inspecting the term. | Proved from the logical relation (a derivation is `ret`, `op`, or a step) and stated for configurations: a configuration is `T(ret)(ṽ)` or it steps. | [`ConfigNormalization.agda`](POPL.ConfigNormalization.html) |
| D12 | The uniqueness lemma (§5.4) assumes `⟦·⟧ : Val(A) ≅ ⟦A⟧`. | Assumes only a left inverse. `Ground` types (built from 0, 1, +, ×) have one. Uniqueness does not use affinity. | [`ConfigNormalization.agda`](POPL.ConfigNormalization.html) |
| D13 | §2.1 lists the lens laws for state only as "including" two of them. | The standard complete set (Plotkin–Power): get-set, set-get, set-set, get-get. | [`Instances/State.agda`](POPL.Instances.State.html) |

## Not formalized

- **The CBPV⁺ doctrine (§3.1) and the glued models.** The user asked for no gluing. The results these give are proved directly (D3, D6).
- **The free models of R-semimodules, convex spaces and pre-convex spaces.**
  - Semimodules and convex spaces are not operational models in the paper either.
  - Pre-convex spaces would need real numbers in [0, 1].
- **The syntactic free model `Term_𝒯 X` as a quotient-inductive type (§2.1, Example).** Nothing in the paper's results depends on it. The free model is an input, given by a universal property.

{% endraw %}
