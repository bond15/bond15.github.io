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
<a id="895" class="Keyword">import</a> <a id="902" href="POPL.FutureWork.WriterWithErrors.html" class="Module">POPL.FutureWork.WriterWithErrors</a>
<a id="935" class="Keyword">import</a> <a id="942" href="POPL.Instances.Common.html" class="Module">POPL.Instances.Common</a>
<a id="964" class="Keyword">import</a> <a id="971" href="POPL.Instances.Errors.html" class="Module">POPL.Instances.Errors</a>
<a id="993" class="Keyword">import</a> <a id="1000" href="POPL.Instances.State.html" class="Module">POPL.Instances.State</a>
<a id="1021" class="Keyword">import</a> <a id="1028" href="POPL.Instances.WeightedMonoid.html" class="Module">POPL.Instances.WeightedMonoid</a>
<a id="1058" class="Keyword">import</a> <a id="1065" href="POPL.Instances.WeightedMonoidAffine.html" class="Module">POPL.Instances.WeightedMonoidAffine</a>
<a id="1101" class="Keyword">import</a> <a id="1108" href="POPL.Instances.WeightedMonoidRules.html" class="Module">POPL.Instances.WeightedMonoidRules</a>
<a id="1143" class="Keyword">import</a> <a id="1150" href="POPL.Instances.Writer.html" class="Module">POPL.Instances.Writer</a>
<a id="1172" class="Keyword">import</a> <a id="1179" href="POPL.Models.html" class="Module">POPL.Models</a>
<a id="1191" class="Keyword">import</a> <a id="1198" href="POPL.MonadContainer.Base.html" class="Module">POPL.MonadContainer.Base</a>
<a id="1223" class="Keyword">import</a> <a id="1230" href="POPL.MonadContainer.ConfigNormalization.html" class="Module">POPL.MonadContainer.ConfigNormalization</a>
<a id="1270" class="Keyword">import</a> <a id="1277" href="POPL.MonadContainer.ConfigReduction.html" class="Module">POPL.MonadContainer.ConfigReduction</a>
<a id="1313" class="Keyword">import</a> <a id="1320" href="POPL.MonadContainer.Equiv.html" class="Module">POPL.MonadContainer.Equiv</a>
<a id="1346" class="Keyword">import</a> <a id="1353" href="POPL.MonadContainer.OperationalModel.html" class="Module">POPL.MonadContainer.OperationalModel</a>
<a id="1390" class="Keyword">import</a> <a id="1397" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a>
<a id="1420" class="Keyword">import</a> <a id="1427" href="POPL.OperationalModel.html" class="Module">POPL.OperationalModel</a>
<a id="1449" class="Keyword">import</a> <a id="1456" href="POPL.Plug.html" class="Module">POPL.Plug</a>
<a id="1466" class="Keyword">import</a> <a id="1473" href="POPL.Polynomial.html" class="Module">POPL.Polynomial</a>
<a id="1489" class="Keyword">import</a> <a id="1496" href="POPL.Renaming.html" class="Module">POPL.Renaming</a>
<a id="1510" class="Keyword">import</a> <a id="1517" href="POPL.Substitution.html" class="Module">POPL.Substitution</a>
<a id="1535" class="Keyword">import</a> <a id="1542" href="POPL.Syntax.html" class="Module">POPL.Syntax</a>
<a id="1554" class="Keyword">import</a> <a id="1561" href="POPL.Theory.html" class="Module">POPL.Theory</a>
<a id="1573" class="Keyword">import</a> <a id="1580" href="POPL.TreeCanonicity.html" class="Module">POPL.TreeCanonicity</a>
<a id="1600" class="Keyword">import</a> <a id="1607" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a>
<a id="1630" class="Keyword">import</a> <a id="1637" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a>
<a id="1656" class="Keyword">import</a> <a id="1663" href="POPL.TreeSoundness.html" class="Module">POPL.TreeSoundness</a>
<a id="1682" class="Keyword">import</a> <a id="1689" href="POPL.Types.html" class="Module">POPL.Types</a>
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

<pre class="Agda"><a id="3636" class="Comment">-- §2.1 signatures, terms, equations, algebras, models</a>
<a id="3691" class="Keyword">open</a> <a id="3696" href="POPL.Theory.html" class="Module">POPL.Theory</a> <a id="3708" class="Keyword">using</a> <a id="3714" class="Symbol">(</a><a id="3715" href="POPL.Theory.html#675" class="Record">Signature</a><a id="3724" class="Symbol">;</a> <a id="3726" href="POPL.Theory.html#825" class="Datatype">Term</a><a id="3730" class="Symbol">;</a> <a id="3732" href="POPL.Theory.html#2041" class="Record">Theory</a><a id="3738" class="Symbol">;</a> <a id="3740" href="POPL.Theory.html#2402" class="Record">Model</a><a id="3745" class="Symbol">;</a> <a id="3747" href="POPL.Theory.html#1461" class="Record">IsHom</a><a id="3752" class="Symbol">)</a>

<a id="3755" class="Comment">-- §2.1 free model monad</a>
<a id="3780" class="Keyword">open</a> <a id="3785" href="POPL.FreeModel.html" class="Module">POPL.FreeModel</a> <a id="3800" class="Keyword">using</a> <a id="3806" class="Symbol">(</a><a id="3807" href="POPL.FreeModel.html#745" class="Record">FreeModel</a><a id="3816" class="Symbol">)</a>
<a id="3818" class="Keyword">open</a> <a id="3823" href="POPL.FreeModel.html#745" class="Module">POPL.FreeModel.FreeModel</a> <a id="3848" class="Keyword">using</a> <a id="3854" class="Symbol">(</a><a id="3855" href="POPL.FreeModel.html#1223" class="Field">ext-uniq</a><a id="3863" class="Symbol">;</a> <a id="3865" href="POPL.FreeModel.html#1632" class="Function">μ</a><a id="3866" class="Symbol">;</a> <a id="3868" href="POPL.FreeModel.html#1555" class="Function">map</a><a id="3871" class="Symbol">)</a>

<a id="3874" class="Comment">-- §2.3 Fig. 1 syntax of CBPV(𝒯) and CBPV⁺(𝒯)</a>
<a id="3920" class="Keyword">open</a> <a id="3925" href="POPL.Types.html" class="Module">POPL.Types</a> <a id="3936" class="Keyword">using</a> <a id="3942" class="Symbol">(</a><a id="3943" href="POPL.Types.html#499" class="Datatype">VTy</a><a id="3946" class="Symbol">;</a> <a id="3948" href="POPL.Types.html#515" class="Datatype">CTy</a><a id="3951" class="Symbol">;</a> <a id="3953" href="POPL.Types.html#1215" class="Datatype">Mode</a><a id="3957" class="Symbol">)</a>
<a id="3959" class="Keyword">open</a> <a id="3964" href="POPL.Syntax.html" class="Module">POPL.Syntax</a> <a id="3976" class="Keyword">using</a> <a id="3982" class="Symbol">(</a><a id="3983" href="POPL.Syntax.html#1048" class="Datatype">Val</a><a id="3986" class="Symbol">;</a> <a id="3988" href="POPL.Syntax.html#1093" class="Datatype">Comp</a><a id="3992" class="Symbol">;</a> <a id="3994" href="POPL.Syntax.html#1138" class="Datatype">Stack</a><a id="3999" class="Symbol">)</a>

<a id="4002" class="Comment">-- §2.3 Fig. 2 operations: V[γ], M[γ], S[γ], δ[γ], S[M], S&#39;[S]</a>
<a id="4065" class="Keyword">open</a> <a id="4070" href="POPL.Renaming.html" class="Module">POPL.Renaming</a> <a id="4084" class="Keyword">using</a> <a id="4090" class="Symbol">(</a><a id="4091" href="POPL.Renaming.html#730" class="Function">renC</a><a id="4095" class="Symbol">)</a>
<a id="4097" class="Keyword">open</a> <a id="4102" href="POPL.Substitution.html" class="Module">POPL.Substitution</a> <a id="4120" class="Keyword">using</a> <a id="4126" class="Symbol">(</a><a id="4127" href="POPL.Substitution.html#762" class="Function">subV</a><a id="4131" class="Symbol">;</a> <a id="4133" href="POPL.Substitution.html#805" class="Function">subC</a><a id="4137" class="Symbol">;</a> <a id="4139" href="POPL.Substitution.html#850" class="Function">subS</a><a id="4143" class="Symbol">;</a> <a id="4145" href="POPL.Substitution.html#2412" class="Function Operator">_⊚_</a><a id="4148" class="Symbol">)</a>
<a id="4150" class="Keyword">open</a> <a id="4155" href="POPL.Plug.html" class="Module">POPL.Plug</a> <a id="4165" class="Keyword">using</a> <a id="4171" class="Symbol">(</a><a id="4172" href="POPL.Plug.html#454" class="Function">plug</a><a id="4176" class="Symbol">;</a> <a id="4178" href="POPL.Plug.html#814" class="Function Operator">_∘ˢ_</a><a id="4182" class="Symbol">;</a> <a id="4184" href="POPL.Plug.html#1893" class="Function">plug-sub</a><a id="4192" class="Symbol">)</a>

<a id="4195" class="Comment">-- §2.3 Fig. 2 equational theory</a>
<a id="4228" class="Keyword">open</a> <a id="4233" href="POPL.Equational.html" class="Module">POPL.Equational</a> <a id="4249" class="Keyword">using</a> <a id="4255" class="Symbol">(</a><a id="4256" href="POPL.Equational.html#3013" class="Datatype Operator">_≈v_</a><a id="4260" class="Symbol">;</a> <a id="4262" href="POPL.Equational.html#3074" class="Datatype Operator">_≈c_</a><a id="4266" class="Symbol">)</a>
</pre>
### Denotational semantics and equational canonicity (§3)

<pre class="Agda"><a id="4340" class="Comment">-- §3.2 Fig. 3 denotational semantics</a>
<a id="4378" class="Keyword">open</a> <a id="4383" href="POPL.Denotation.html" class="Module">POPL.Denotation</a> <a id="4399" class="Keyword">using</a> <a id="4405" class="Symbol">(</a><a id="4406" href="POPL.Denotation.html#1525" class="Function Operator">⟦_⟧v</a><a id="4410" class="Symbol">;</a> <a id="4412" href="POPL.Denotation.html#1543" class="Function Operator">⟦_⟧c</a><a id="4416" class="Symbol">;</a> <a id="4418" href="POPL.Denotation.html#2117" class="Function Operator">⟦_⟧V</a><a id="4422" class="Symbol">;</a> <a id="4424" href="POPL.Denotation.html#2151" class="Function Operator">⟦_⟧C</a><a id="4428" class="Symbol">;</a> <a id="4430" href="POPL.Denotation.html#2185" class="Function Operator">⟦_⟧S</a><a id="4434" class="Symbol">)</a>
<a id="4436" class="Keyword">open</a> <a id="4441" href="POPL.Models.html#350" class="Module">POPL.Models.Models-of</a> <a id="4463" class="Keyword">using</a> <a id="4469" class="Symbol">(</a><a id="4470" href="POPL.Models.html#949" class="Function">powModel</a><a id="4478" class="Symbol">;</a> <a id="4480" href="POPL.Models.html#1889" class="Function">prodModel</a><a id="4489" class="Symbol">)</a>

<a id="4492" class="Comment">-- §3.2 the denotation preserves substitution, plugging and operations</a>
<a id="4563" class="Keyword">open</a> <a id="4568" href="POPL.DenotationLemmas.html" class="Module">POPL.DenotationLemmas</a> <a id="4590" class="Keyword">using</a> <a id="4596" class="Symbol">(</a><a id="4597" href="POPL.DenotationLemmas.html#6656" class="Function">den-subC</a><a id="4605" class="Symbol">;</a> <a id="4607" href="POPL.DenotationLemmas.html#11466" class="Function">den-plug</a><a id="4615" class="Symbol">;</a> <a id="4617" href="POPL.DenotationLemmas.html#12237" class="Function">den-stack-hom</a><a id="4630" class="Symbol">)</a>

<a id="4633" class="Comment">-- §3.2 soundness of ⟦-⟧ for the equations</a>
<a id="4676" class="Keyword">open</a> <a id="4681" href="POPL.EquationalSoundness.html" class="Module">POPL.EquationalSoundness</a> <a id="4706" class="Keyword">using</a> <a id="4712" class="Symbol">(</a><a id="4713" href="POPL.EquationalSoundness.html#1966" class="Function">sound-c</a><a id="4720" class="Symbol">)</a>

<a id="4723" class="Comment">-- §3.3 Fig. 6 equational logical relation</a>
<a id="4766" class="Keyword">open</a> <a id="4771" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="4794" class="Keyword">using</a> <a id="4800" class="Symbol">(</a><a id="4801" href="POPL.EqLogicalRelation.html#1918" class="Function Operator">𝒱⟦_⟧</a><a id="4805" class="Symbol">;</a> <a id="4807" href="POPL.EqLogicalRelation.html#1951" class="Function Operator">𝒞⟦_⟧</a><a id="4811" class="Symbol">;</a> <a id="4813" href="POPL.EqLogicalRelation.html#1654" class="Datatype">FPred</a><a id="4818" class="Symbol">)</a>

<a id="4821" class="Comment">-- §3.4 Fundamental Theorem</a>
<a id="4849" class="Keyword">open</a> <a id="4854" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="4877" class="Keyword">using</a> <a id="4883" class="Symbol">(</a><a id="4884" href="POPL.EqLogicalRelation.html#4697" class="Function">fundV</a><a id="4889" class="Symbol">;</a> <a id="4891" href="POPL.EqLogicalRelation.html#4729" class="Function">fundC</a><a id="4896" class="Symbol">)</a>

<a id="4899" class="Comment">-- §3.4 Corollary (equational canonicity)</a>
<a id="4941" class="Keyword">open</a> <a id="4946" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="4969" class="Keyword">using</a> <a id="4975" class="Symbol">(</a><a id="4976" href="POPL.EqLogicalRelation.html#8241" class="Function">equational-canonicity</a><a id="4997" class="Symbol">)</a>

<a id="5000" class="Comment">-- §3.4 Corollary (uniqueness; corrected, C3)</a>
<a id="5046" class="Keyword">open</a> <a id="5051" href="POPL.EqCanonicity.html" class="Module">POPL.EqCanonicity</a> <a id="5069" class="Keyword">using</a> <a id="5075" class="Symbol">(</a><a id="5076" href="POPL.EqCanonicity.html#1862" class="Function">canonical-form-unique</a><a id="5097" class="Symbol">)</a>
</pre>
### Tree reduction (§4)

<pre class="Agda"><a id="5137" class="Comment">-- §4.1 Fig. 5 tree reduction</a>
<a id="5167" class="Keyword">open</a> <a id="5172" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a> <a id="5191" class="Keyword">using</a> <a id="5197" class="Symbol">(</a><a id="5198" href="POPL.TreeReduction.html#1982" class="Datatype Operator">_↦red_</a><a id="5204" class="Symbol">;</a> <a id="5206" href="POPL.TreeReduction.html#2948" class="Datatype Operator">_↦h_</a><a id="5210" class="Symbol">;</a> <a id="5212" href="POPL.TreeReduction.html#3204" class="Datatype Operator">_↦_</a><a id="5215" class="Symbol">;</a> <a id="5217" href="POPL.TreeReduction.html#11340" class="Function">det</a><a id="5220" class="Symbol">)</a>

<a id="5223" class="Comment">-- §4.1 Theorem (soundness of ↦tree)</a>
<a id="5260" class="Keyword">open</a> <a id="5265" href="POPL.TreeSoundness.html" class="Module">POPL.TreeSoundness</a> <a id="5284" class="Keyword">using</a> <a id="5290" class="Symbol">(</a><a id="5291" href="POPL.TreeSoundness.html#1747" class="Function">sound↦</a><a id="5297" class="Symbol">)</a>

<a id="5300" class="Comment">-- §4.2 Fig. 7 operational logical relation</a>
<a id="5344" class="Keyword">open</a> <a id="5349" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="5372" class="Keyword">using</a> <a id="5378" class="Symbol">(</a><a id="5379" href="POPL.OpLogicalRelation.html#5256" class="Function Operator">𝒱⟦_⟧</a><a id="5383" class="Symbol">;</a> <a id="5385" href="POPL.OpLogicalRelation.html#5289" class="Function Operator">𝒞⟦_⟧</a><a id="5389" class="Symbol">;</a> <a id="5391" href="POPL.OpLogicalRelation.html#4983" class="Datatype">FPred</a><a id="5396" class="Symbol">)</a>

<a id="5399" class="Comment">-- §4.2 Lemma (anti-reduction; corrected, C5)</a>
<a id="5445" class="Keyword">open</a> <a id="5450" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a> <a id="5469" class="Keyword">using</a> <a id="5475" class="Symbol">(</a><a id="5476" href="POPL.TreeReduction.html#12231" class="Function">hjoin</a><a id="5481" class="Symbol">)</a>
<a id="5483" class="Keyword">open</a> <a id="5488" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="5511" class="Keyword">using</a> <a id="5517" class="Symbol">(</a><a id="5518" href="POPL.OpLogicalRelation.html#5911" class="Function">AR</a><a id="5520" class="Symbol">;</a> <a id="5522" href="POPL.OpLogicalRelation.html#5976" class="Function">FW</a><a id="5524" class="Symbol">)</a>

<a id="5527" class="Comment">-- §4.2 Lemma (congruence)</a>
<a id="5554" class="Keyword">open</a> <a id="5559" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="5582" class="Keyword">using</a> <a id="5588" class="Symbol">(</a><a id="5589" href="POPL.OpLogicalRelation.html#7469" class="Function">𝒞-op</a><a id="5593" class="Symbol">)</a>

<a id="5596" class="Comment">-- §4.3 Fundamental Lemma</a>
<a id="5622" class="Keyword">open</a> <a id="5627" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="5650" class="Keyword">using</a> <a id="5656" class="Symbol">(</a><a id="5657" href="POPL.OpLogicalRelation.html#9896" class="Function">fundV</a><a id="5662" class="Symbol">;</a> <a id="5664" href="POPL.OpLogicalRelation.html#9932" class="Function">fundC</a><a id="5669" class="Symbol">;</a> <a id="5671" href="POPL.OpLogicalRelation.html#11374" class="Function">related</a><a id="5678" class="Symbol">)</a>

<a id="5681" class="Comment">-- §4.3 Corollary (termination)</a>
<a id="5713" class="Keyword">open</a> <a id="5718" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="5741" class="Keyword">using</a> <a id="5747" class="Symbol">(</a><a id="5748" href="POPL.TreeNormalization.html#4103" class="Function">termination</a><a id="5759" class="Symbol">)</a>

<a id="5762" class="Comment">-- §4.3 Corollary (strong normalization)</a>
<a id="5803" class="Keyword">open</a> <a id="5808" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="5831" class="Keyword">using</a> <a id="5837" class="Symbol">(</a><a id="5838" href="POPL.TreeNormalization.html#6686" class="Function">strong-normalization</a><a id="5858" class="Symbol">)</a>

<a id="5861" class="Comment">-- §4.3 Corollary (canonicity; corrected, C8)</a>
<a id="5907" class="Keyword">open</a> <a id="5912" href="POPL.TreeCanonicity.html" class="Module">POPL.TreeCanonicity</a> <a id="5932" class="Keyword">using</a> <a id="5938" class="Symbol">(</a><a id="5939" href="POPL.TreeCanonicity.html#1406" class="Function">tree-canonicity</a><a id="5954" class="Symbol">)</a>
</pre>
### Configuration reduction (§5)

<pre class="Agda"><a id="6003" class="Comment">-- §5.2 polynomials, ∂p, plugging</a>
<a id="6037" class="Keyword">open</a> <a id="6042" href="POPL.Polynomial.html" class="Module">POPL.Polynomial</a> <a id="6058" class="Keyword">using</a> <a id="6064" class="Symbol">(</a><a id="6065" href="POPL.Polynomial.html#1032" class="Record">Poly</a><a id="6069" class="Symbol">;</a> <a id="6071" href="POPL.Polynomial.html#1126" class="Function Operator">⟦_⟧</a><a id="6074" class="Symbol">;</a> <a id="6076" href="POPL.Polynomial.html#1421" class="Function">∂</a><a id="6077" class="Symbol">;</a> <a id="6079" href="POPL.Polynomial.html#1828" class="Function">plug</a><a id="6083" class="Symbol">;</a> <a id="6085" href="POPL.Polynomial.html#2386" class="Function">plug-map</a><a id="6093" class="Symbol">)</a>

<a id="6096" class="Comment">-- §5.2 Def. (Operational Model)</a>
<a id="6129" class="Keyword">open</a> <a id="6134" href="POPL.OperationalModel.html" class="Module">POPL.OperationalModel</a> <a id="6156" class="Keyword">using</a> <a id="6162" class="Symbol">(</a><a id="6163" href="POPL.OperationalModel.html#417" class="Record">OperationalModel</a><a id="6179" class="Symbol">)</a>
<a id="6181" class="Keyword">open</a> <a id="6186" href="POPL.OperationalModel.html#417" class="Module">POPL.OperationalModel.OperationalModel</a> <a id="6225" class="Keyword">using</a> <a id="6231" class="Symbol">(</a><a id="6232" href="POPL.OperationalModel.html#622" class="Field">map-poly</a><a id="6240" class="Symbol">)</a>

<a id="6243" class="Comment">-- §5.3 Fig. &quot;Configuration Reduction&quot; (derivative form)</a>
<a id="6300" class="Keyword">open</a> <a id="6305" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="6326" class="Keyword">using</a> <a id="6332" class="Symbol">(</a><a id="6333" href="POPL.ConfigReduction.html#2128" class="Datatype Operator">_↦T_</a><a id="6337" class="Symbol">)</a>

<a id="6340" class="Comment">-- §5.3 Theorem (soundness of the initial configuration)</a>
<a id="6397" class="Keyword">open</a> <a id="6402" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="6423" class="Keyword">using</a> <a id="6429" class="Symbol">(</a><a id="6430" href="POPL.ConfigReduction.html#2938" class="Function">sound-init</a><a id="6440" class="Symbol">)</a>

<a id="6443" class="Comment">-- §5.3 Theorem (soundness of ↦T)</a>
<a id="6477" class="Keyword">open</a> <a id="6482" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="6503" class="Keyword">using</a> <a id="6509" class="Symbol">(</a><a id="6510" href="POPL.ConfigReduction.html#3612" class="Function">sound-T</a><a id="6517" class="Symbol">)</a>

<a id="6520" class="Comment">-- §5.4 Def. (Affinity), and appendix &quot;Simplification&quot;</a>
<a id="6575" class="Keyword">open</a> <a id="6580" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="6601" class="Keyword">using</a> <a id="6607" class="Symbol">(</a><a id="6608" href="POPL.ConfigReduction.html#4970" class="Function">step</a><a id="6612" class="Symbol">;</a> <a id="6614" href="POPL.ConfigReduction.html#5250" class="Function">ρ</a><a id="6615" class="Symbol">;</a> <a id="6617" href="POPL.ConfigReduction.html#5536" class="Function">Affine</a><a id="6623" class="Symbol">;</a> <a id="6625" href="POPL.ConfigReduction.html#5718" class="Function">simplification</a><a id="6639" class="Symbol">;</a> <a id="6641" href="POPL.ConfigReduction.html#6377" class="Function">effect-via-step</a><a id="6656" class="Symbol">)</a>

<a id="6659" class="Comment">-- §5.4 Lemma (Progress)</a>
<a id="6684" class="Keyword">open</a> <a id="6689" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6714" class="Keyword">using</a> <a id="6720" class="Symbol">(</a><a id="6721" href="POPL.ConfigNormalization.html#8153" class="Function">progress-T</a><a id="6731" class="Symbol">)</a>

<a id="6734" class="Comment">-- §5.4 Def. (Termination Metric; corrected, C7)</a>
<a id="6783" class="Keyword">open</a> <a id="6788" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="6811" class="Keyword">using</a> <a id="6817" class="Symbol">(</a><a id="6818" href="POPL.TreeNormalization.html#4346" class="Function">size</a><a id="6822" class="Symbol">;</a> <a id="6824" href="POPL.TreeNormalization.html#6016" class="Function Operator">‖_‖</a><a id="6827" class="Symbol">)</a>
<a id="6829" class="Keyword">open</a> <a id="6834" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6859" class="Keyword">using</a> <a id="6865" class="Symbol">(</a><a id="6866" href="POPL.ConfigNormalization.html#5205" class="Function Operator">‖_‖T</a><a id="6870" class="Symbol">)</a>

<a id="6873" class="Comment">-- §5.4 Theorem (strong normalization for ↦T)</a>
<a id="6919" class="Keyword">open</a> <a id="6924" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6949" class="Keyword">using</a> <a id="6955" class="Symbol">(</a><a id="6956" href="POPL.ConfigNormalization.html#7236" class="Function">strong-normalization-T</a><a id="6978" class="Symbol">;</a> <a id="6980" href="POPL.ConfigNormalization.html#8949" class="Function">normalize-T</a><a id="6991" class="Symbol">;</a> <a id="6993" href="POPL.ConfigNormalization.html#9367" class="Function">canonicity-T</a><a id="7005" class="Symbol">)</a>

<a id="7008" class="Comment">-- §5.4 Lemma (uniqueness of the result)</a>
<a id="7049" class="Keyword">open</a> <a id="7054" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="7079" class="Keyword">using</a> <a id="7085" class="Symbol">(</a><a id="7086" href="POPL.ConfigNormalization.html#9893" class="Function">final-unique</a><a id="7098" class="Symbol">;</a> <a id="7100" href="POPL.ConfigNormalization.html#11328" class="Function">ground-canonicity</a><a id="7117" class="Symbol">)</a>

<a id="7120" class="Comment">-- §5.2 monad containers (Uustalu), and the equivalence of their two sets of laws (D15)</a>
<a id="7208" class="Keyword">open</a> <a id="7213" href="POPL.MonadContainer.Base.html" class="Module">POPL.MonadContainer.Base</a> <a id="7238" class="Keyword">using</a> <a id="7244" class="Symbol">(</a><a id="7245" href="POPL.MonadContainer.Base.html#1617" class="Record">MCOps</a><a id="7250" class="Symbol">;</a> <a id="7252" href="POPL.MonadContainer.Base.html#2212" class="Record">MonadLaws</a><a id="7261" class="Symbol">;</a> <a id="7263" href="POPL.MonadContainer.Base.html#2486" class="Record">UustaluLaws</a><a id="7274" class="Symbol">;</a> <a id="7276" href="POPL.MonadContainer.Base.html#4731" class="Function">M→U</a><a id="7279" class="Symbol">;</a> <a id="7281" href="POPL.MonadContainer.Base.html#4079" class="Function">U→M</a><a id="7284" class="Symbol">;</a> <a id="7286" href="POPL.MonadContainer.Base.html#5696" class="Record">MonadContainer</a><a id="7300" class="Symbol">)</a>

<a id="7303" class="Comment">-- §5.2 Def. (Operational Model) as a monad container (D15)</a>
<a id="7363" class="Keyword">open</a> <a id="7368" href="POPL.MonadContainer.OperationalModel.html" class="Module">POPL.MonadContainer.OperationalModel</a> <a id="7405" class="Keyword">using</a> <a id="7411" class="Symbol">(</a><a id="7412" href="POPL.MonadContainer.OperationalModel.html#1612" class="Record">OperationalModel</a><a id="7428" class="Symbol">)</a>
<a id="7430" class="Keyword">open</a> <a id="7435" href="POPL.MonadContainer.OperationalModel.html#1612" class="Module">POPL.MonadContainer.OperationalModel.OperationalModel</a> <a id="7489" class="Keyword">using</a> <a id="7495" class="Symbol">(</a><a id="7496" href="POPL.MonadContainer.OperationalModel.html#1811" class="Field">gen</a><a id="7499" class="Symbol">;</a> <a id="7501" href="POPL.MonadContainer.OperationalModel.html#3087" class="Function">μₘ≡μ</a><a id="7505" class="Symbol">;</a> <a id="7507" href="POPL.MonadContainer.OperationalModel.html#3296" class="Function">map-poly</a><a id="7515" class="Symbol">)</a>

<a id="7518" class="Comment">-- §5.3–5.4 for monad-container operational models (D15)</a>
<a id="7575" class="Keyword">open</a> <a id="7580" href="POPL.MonadContainer.ConfigReduction.html" class="Module">POPL.MonadContainer.ConfigReduction</a> <a id="7616" class="Keyword">using</a> <a id="7622" class="Symbol">(</a><a id="7623" href="POPL.MonadContainer.ConfigReduction.html#1604" class="Datatype Operator">_↦T_</a><a id="7627" class="Symbol">;</a> <a id="7629" href="POPL.MonadContainer.ConfigReduction.html#3089" class="Function">sound-T</a><a id="7636" class="Symbol">;</a> <a id="7638" href="POPL.MonadContainer.ConfigReduction.html#5277" class="Function">step-shape</a><a id="7648" class="Symbol">;</a> <a id="7650" href="POPL.MonadContainer.ConfigReduction.html#5354" class="Function">step-pos</a><a id="7658" class="Symbol">;</a> <a id="7660" href="POPL.MonadContainer.ConfigReduction.html#5648" class="Function">Affine</a><a id="7666" class="Symbol">)</a>
<a id="7668" class="Keyword">open</a> <a id="7673" href="POPL.MonadContainer.ConfigNormalization.html" class="Module">POPL.MonadContainer.ConfigNormalization</a> <a id="7713" class="Keyword">using</a> <a id="7719" class="Symbol">(</a><a id="7720" href="POPL.MonadContainer.ConfigNormalization.html#6583" class="Function">strong-normalization-T</a><a id="7742" class="Symbol">;</a> <a id="7744" href="POPL.MonadContainer.ConfigNormalization.html#8714" class="Function">canonicity-T</a><a id="7756" class="Symbol">;</a> <a id="7758" href="POPL.MonadContainer.ConfigNormalization.html#10675" class="Function">ground-canonicity</a><a id="7775" class="Symbol">)</a>
</pre>
### Instances (§2.2, §5.3)

<pre class="Agda"><a id="7818" class="Comment">-- the two definitions of operational model are equivalent (D15)</a>
<a id="7883" class="Keyword">open</a> <a id="7888" href="POPL.MonadContainer.Equiv.html" class="Module">POPL.MonadContainer.Equiv</a> <a id="7914" class="Keyword">using</a> <a id="7920" class="Symbol">(</a><a id="7921" href="POPL.MonadContainer.Equiv.html#1550" class="Function">toPoly</a><a id="7927" class="Symbol">;</a> <a id="7929" href="POPL.MonadContainer.Equiv.html#4784" class="Function">fromPoly</a><a id="7937" class="Symbol">;</a> <a id="7939" href="POPL.MonadContainer.Equiv.html#5121" class="Function">fromPoly-η</a><a id="7949" class="Symbol">;</a> <a id="7951" href="POPL.MonadContainer.Equiv.html#5221" class="Function">fromPoly-μ</a><a id="7961" class="Symbol">;</a> <a id="7963" href="POPL.MonadContainer.Equiv.html#5326" class="Function">fromPoly-ops</a><a id="7975" class="Symbol">;</a> <a id="7977" href="POPL.MonadContainer.Equiv.html#5794" class="Function">roundtrip-•</a><a id="7988" class="Symbol">)</a>

<a id="7991" class="Comment">-- Writer: theory, free model, affinity, derived rule</a>
<a id="8045" class="Keyword">open</a> <a id="8050" href="POPL.Instances.Writer.html" class="Module">POPL.Instances.Writer</a> <a id="8072" class="Keyword">using</a> <a id="8078" class="Symbol">(</a><a id="8079" href="POPL.Instances.Writer.html#1667" class="Function">writerTheory</a><a id="8091" class="Symbol">;</a> <a id="8093" href="POPL.Instances.Writer.html#2989" class="Function">writerFree</a><a id="8103" class="Symbol">;</a> <a id="8105" href="POPL.Instances.Writer.html#3544" class="Function">writerOM</a><a id="8113" class="Symbol">;</a> <a id="8115" href="POPL.Instances.Writer.html#3846" class="Function">writer-affine</a><a id="8128" class="Symbol">;</a> <a id="8130" href="POPL.Instances.Writer.html#4117" class="Function">writer-effect</a><a id="8143" class="Symbol">)</a>

<a id="8146" class="Comment">-- Errors</a>
<a id="8156" class="Keyword">open</a> <a id="8161" href="POPL.Instances.Errors.html" class="Module">POPL.Instances.Errors</a> <a id="8183" class="Keyword">using</a> <a id="8189" class="Symbol">(</a><a id="8190" href="POPL.Instances.Errors.html#957" class="Function">errTheory</a><a id="8199" class="Symbol">;</a> <a id="8201" href="POPL.Instances.Errors.html#2032" class="Function">errFree</a><a id="8208" class="Symbol">;</a> <a id="8210" href="POPL.Instances.Errors.html#2291" class="Function">errOM</a><a id="8215" class="Symbol">;</a> <a id="8217" href="POPL.Instances.Errors.html#2585" class="Function">err-affine</a><a id="8227" class="Symbol">;</a> <a id="8229" href="POPL.Instances.Errors.html#2910" class="Function">err-effect</a><a id="8239" class="Symbol">)</a>

<a id="8242" class="Comment">-- Boolean state, and the get and set rules</a>
<a id="8286" class="Keyword">open</a> <a id="8291" href="POPL.Instances.State.html" class="Module">POPL.Instances.State</a> <a id="8312" class="Keyword">using</a> <a id="8318" class="Symbol">(</a><a id="8319" href="POPL.Instances.State.html#2503" class="Function">stateTheory</a><a id="8330" class="Symbol">;</a> <a id="8332" href="POPL.Instances.State.html#6038" class="Function">stateFree</a><a id="8341" class="Symbol">;</a> <a id="8343" href="POPL.Instances.State.html#6262" class="Function">stateOM</a><a id="8350" class="Symbol">;</a> <a id="8352" href="POPL.Instances.State.html#6843" class="Function">state-affine</a><a id="8364" class="Symbol">;</a> <a id="8366" href="POPL.Instances.State.html#7922" class="Function">state-get</a><a id="8375" class="Symbol">;</a> <a id="8377" href="POPL.Instances.State.html#8287" class="Function">state-set</a><a id="8386" class="Symbol">)</a>

<a id="8389" class="Comment">-- Weighted monoid</a>
<a id="8408" class="Keyword">open</a> <a id="8413" href="POPL.Instances.WeightedMonoid.html" class="Module">POPL.Instances.WeightedMonoid</a> <a id="8443" class="Keyword">using</a> <a id="8449" class="Symbol">(</a><a id="8450" href="POPL.Instances.WeightedMonoid.html#3428" class="Function">wmTheory</a><a id="8458" class="Symbol">;</a> <a id="8460" href="POPL.Instances.WeightedMonoid.html#11826" class="Function">wmFree</a><a id="8466" class="Symbol">;</a> <a id="8468" href="POPL.Instances.WeightedMonoid.html#13605" class="Function">wmOM</a><a id="8472" class="Symbol">)</a>
<a id="8474" class="Keyword">open</a> <a id="8479" href="POPL.Instances.WeightedMonoidAffine.html" class="Module">POPL.Instances.WeightedMonoidAffine</a> <a id="8515" class="Keyword">using</a> <a id="8521" class="Symbol">(</a><a id="8522" href="POPL.Instances.WeightedMonoidAffine.html#5703" class="Function">wm-affine</a><a id="8531" class="Symbol">)</a>
<a id="8533" class="Keyword">open</a> <a id="8538" href="POPL.Instances.WeightedMonoidRules.html" class="Module">POPL.Instances.WeightedMonoidRules</a> <a id="8573" class="Keyword">using</a> <a id="8579" class="Symbol">(</a><a id="8580" href="POPL.Instances.WeightedMonoidRules.html#2226" class="Function">wm-act</a><a id="8586" class="Symbol">;</a> <a id="8588" href="POPL.Instances.WeightedMonoidRules.html#2765" class="Function">wm-unit</a><a id="8595" class="Symbol">;</a> <a id="8597" href="POPL.Instances.WeightedMonoidRules.html#3077" class="Function">wm-mul</a><a id="8603" class="Symbol">)</a>
</pre>
### Future work: combining effects

<pre class="Agda"><a id="8654" class="Comment">-- Future work: combining effects with a distributive law of monadic containers (writer + errors)</a>
<a id="8752" class="Keyword">open</a> <a id="8757" href="POPL.FutureWork.WriterWithErrors.html" class="Module">POPL.FutureWork.WriterWithErrors</a> <a id="8790" class="Keyword">using</a> <a id="8796" class="Symbol">(</a><a id="8797" href="POPL.FutureWork.WriterWithErrors.html#3119" class="Function">γ</a><a id="8798" class="Symbol">;</a> <a id="8800" href="POPL.FutureWork.WriterWithErrors.html#3407" class="Function">γ-μE</a><a id="8804" class="Symbol">;</a> <a id="8806" href="POPL.FutureWork.WriterWithErrors.html#3568" class="Function">γ-μW</a><a id="8810" class="Symbol">;</a> <a id="8812" href="POPL.FutureWork.WriterWithErrors.html#3887" class="Function">μWE</a><a id="8815" class="Symbol">;</a> <a id="8817" href="POPL.FutureWork.WriterWithErrors.html#5860" class="Function">mc</a><a id="8819" class="Symbol">;</a> <a id="8821" href="POPL.FutureWork.WriterWithErrors.html#6652" class="Function">φ-μ</a><a id="8824" class="Symbol">;</a> <a id="8826" href="POPL.FutureWork.WriterWithErrors.html#7397" class="Function">theory</a><a id="8832" class="Symbol">;</a> <a id="8834" href="POPL.FutureWork.WriterWithErrors.html#10052" class="Function">OM</a><a id="8836" class="Symbol">;</a> <a id="8838" href="POPL.FutureWork.WriterWithErrors.html#10421" class="Function">affine</a><a id="8844" class="Symbol">;</a> <a id="8846" href="POPL.FutureWork.WriterWithErrors.html#10898" class="Function">rule-tell</a><a id="8855" class="Symbol">;</a> <a id="8857" href="POPL.FutureWork.WriterWithErrors.html#11237" class="Function">rule-raise</a><a id="8867" class="Symbol">)</a>
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

## Future work

### Combining effects with distributive laws of monadic containers

[`POPL/FutureWork/WriterWithErrors.agda`](POPL.FutureWork.WriterWithErrors.html) is an example, not part of the paper. A distributive law `γ : T S ⇒ S T` makes the composite `S ∘ T` a monad (Beck), and Purdy and Damato ("Distributive Laws of Monadic Containers", arXiv:2503.17191) characterize such laws between monadic containers. Their Example 18 and Lemma 19 show that the exceptions container has exactly one distributive law with every monadic container, giving errors under any effect. The module works this out for writer:
- the distributive law `γ : W X + E → W (X + E)` and Beck's four axioms;
- the composite `X ↦ M × (X + E)` as a monad container, isomorphic to the composite monad given by `γ` (`φ-η`, `φ-μ`);
- the combined theory (`tell_m` and `raise_e`, with only the writer equations), whose free model this container is, so that it is an operational model in the sense of D15;
- affinity, and the derived Effect rules `⟨m, S[tell_n(M)]⟩ ↦T ⟨m ⊗ n, S[M]⟩` and `⟨m, S[raise_e]⟩ ↦T ⟨m, raise e⟩`, in which raising keeps the log.

What remains:
- building the composite operational model from a distributive law in general;
- identifying the combined theory (both signatures, plus the equations induced by the law);
- showing that affinity is preserved.

Distributive laws often do not exist (Zwart and Marsden give no-go theorems), so this covers some combinations of effects, not all.

## Not formalized

- **The CBPV⁺ doctrine (§3.1) and the glued models.** The user asked for no gluing. The results these give are proved directly (D3, D6).
- **The free models of R-semimodules, convex spaces and pre-convex spaces.**
  - Semimodules and convex spaces are not operational models in the paper either.
  - Pre-convex spaces would need real numbers in [0, 1].
- **The syntactic free model `Term_𝒯 X` as a quotient-inductive type (§2.1, Example).** Nothing in the paper's results depends on it. The free model is an input, given by a universal property.

{% endraw %}
