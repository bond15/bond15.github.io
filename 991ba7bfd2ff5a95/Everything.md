---
title: "POPL'27 formalization"
layout: agda
permalink: /991ba7bfd2ff5a95/Everything.html
sitemap: false
---
{% raw %}
<link rel="stylesheet" href="Agda.css">

# POPL'27 formalization

This is an Agda formalization of `popl27/popl27.tex`. It has no postulates, holes or termination pragmas, and it is checked with `--cubical --safe`. Every place where it departs from the paper is listed in [Deviations from the paper](#deviations-from-the-paper) below, with the same `C#` or `D#` tag as the comment in the code.

This page is the literate Agda module `Everything`. Every name in the code blocks links to its definition.

<pre class="Agda"><a id="512" class="Keyword">module</a> <a id="519" href="Everything.html" class="Module">Everything</a> <a id="530" class="Keyword">where</a>

<a id="537" class="Keyword">import</a> <a id="544" href="POPL.Models.html" class="Module">POPL.Models</a>
<a id="556" class="Keyword">import</a> <a id="563" href="POPL.Fin.html" class="Module">POPL.Fin</a>
<a id="572" class="Keyword">import</a> <a id="579" href="POPL.Instances.Common.html" class="Module">POPL.Instances.Common</a>
<a id="601" class="Keyword">import</a> <a id="608" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a>
<a id="633" class="Keyword">import</a> <a id="640" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a>
<a id="661" class="Keyword">import</a> <a id="668" href="POPL.Denotation.html" class="Module">POPL.Denotation</a>
<a id="684" class="Keyword">import</a> <a id="691" href="POPL.DenotationLemmas.html" class="Module">POPL.DenotationLemmas</a>
<a id="713" class="Keyword">import</a> <a id="720" href="POPL.EqCanonicity.html" class="Module">POPL.EqCanonicity</a>
<a id="738" class="Keyword">import</a> <a id="745" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a>
<a id="768" class="Keyword">import</a> <a id="775" href="POPL.Equational.html" class="Module">POPL.Equational</a>
<a id="791" class="Keyword">import</a> <a id="798" href="POPL.EquationalSoundness.html" class="Module">POPL.EquationalSoundness</a>
<a id="823" class="Keyword">import</a> <a id="830" href="POPL.FreeModel.html" class="Module">POPL.FreeModel</a>
<a id="845" class="Keyword">import</a> <a id="852" href="POPL.Instances.Errors.html" class="Module">POPL.Instances.Errors</a>
<a id="874" class="Keyword">import</a> <a id="881" href="POPL.Instances.State.html" class="Module">POPL.Instances.State</a>
<a id="902" class="Keyword">import</a> <a id="909" href="POPL.Instances.WeightedMonoid.html" class="Module">POPL.Instances.WeightedMonoid</a>
<a id="939" class="Keyword">import</a> <a id="946" href="POPL.Instances.WeightedMonoidAffine.html" class="Module">POPL.Instances.WeightedMonoidAffine</a>
<a id="982" class="Keyword">import</a> <a id="989" href="POPL.Instances.WeightedMonoidRules.html" class="Module">POPL.Instances.WeightedMonoidRules</a>
<a id="1024" class="Keyword">import</a> <a id="1031" href="POPL.Instances.Writer.html" class="Module">POPL.Instances.Writer</a>
<a id="1053" class="Keyword">import</a> <a id="1060" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a>
<a id="1083" class="Keyword">import</a> <a id="1090" href="POPL.OperationalModel.html" class="Module">POPL.OperationalModel</a>
<a id="1112" class="Keyword">import</a> <a id="1119" href="POPL.Plug.html" class="Module">POPL.Plug</a>
<a id="1129" class="Keyword">import</a> <a id="1136" href="POPL.Polynomial.html" class="Module">POPL.Polynomial</a>
<a id="1152" class="Keyword">import</a> <a id="1159" href="POPL.Renaming.html" class="Module">POPL.Renaming</a>
<a id="1173" class="Keyword">import</a> <a id="1180" href="POPL.Substitution.html" class="Module">POPL.Substitution</a>
<a id="1198" class="Keyword">import</a> <a id="1205" href="POPL.Syntax.html" class="Module">POPL.Syntax</a>
<a id="1217" class="Keyword">import</a> <a id="1224" href="POPL.Theory.html" class="Module">POPL.Theory</a>
<a id="1236" class="Keyword">import</a> <a id="1243" href="POPL.TreeCanonicity.html" class="Module">POPL.TreeCanonicity</a>
<a id="1263" class="Keyword">import</a> <a id="1270" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a>
<a id="1293" class="Keyword">import</a> <a id="1300" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a>
<a id="1319" class="Keyword">import</a> <a id="1326" href="POPL.TreeSoundness.html" class="Module">POPL.TreeSoundness</a>
<a id="1345" class="Keyword">import</a> <a id="1352" href="POPL.Types.html" class="Module">POPL.Types</a>
</pre>
## Build

The project depends only on the `cubical` library. The file `libraries` is ignored by git and lists the path to `cubical.agda-lib`.

```bash
agda --library-file=libraries Everything.lagda.md
```

For the browsable HTML (this page):

```bash
agda --library-file=libraries --html --html-highlight=auto --html-dir=html Everything.lagda.md
```

`./check.sh FILE` checks a single module with a time and memory cap.

## Design choices

- **Syntax.** One mode-indexed syntax covers both calculi:
  - mode `cbpv` is CBPV(𝒯);
  - mode `cbpv⁺` adds Fig. 1's grey rules (complex values and complex stacks).

  Terms are intrinsically typed, with list contexts (non-unary) and de Bruijn variables. The metatheory is proved once for both modes.
- **Equations.** The equational theory of CBPV⁺ is an inductive relation `≈` on plain terms, not a quotient.
- **Semantics.** The denotational semantics and both logical relations are defined directly, without the CBPV doctrine or gluing. Their fundamental theorems are proved by induction on terms.
- **Effect rule.** Configuration reduction uses the derivative form of the Effect rule, `C⟪S[op M⃗]⟫ ↦T μ((∂η C)⟪⟦op⟧(η(S[M⃗]))⟫)`. Affinity is stated through the generic step.

## Paper → Agda

### Algebraic theories, free model monads, and the syntax (§2)

<pre class="Agda"><a id="2677" class="Comment">-- §2.1 signatures, terms, equations, algebras, models</a>
<a id="2732" class="Keyword">open</a> <a id="2737" href="POPL.Theory.html" class="Module">POPL.Theory</a> <a id="2749" class="Keyword">using</a> <a id="2755" class="Symbol">(</a><a id="2756" href="POPL.Theory.html#839" class="Record">Signature</a><a id="2765" class="Symbol">;</a> <a id="2767" href="POPL.Theory.html#989" class="Datatype">Term</a><a id="2771" class="Symbol">;</a> <a id="2773" href="POPL.Theory.html#2205" class="Record">Theory</a><a id="2779" class="Symbol">;</a> <a id="2781" href="POPL.Theory.html#2566" class="Record">Model</a><a id="2786" class="Symbol">;</a> <a id="2788" href="POPL.Theory.html#1625" class="Record">IsHom</a><a id="2793" class="Symbol">)</a>

<a id="2796" class="Comment">-- §2.1 free model monad</a>
<a id="2821" class="Keyword">open</a> <a id="2826" href="POPL.FreeModel.html" class="Module">POPL.FreeModel</a> <a id="2841" class="Keyword">using</a> <a id="2847" class="Symbol">(</a><a id="2848" href="POPL.FreeModel.html#745" class="Record">FreeModel</a><a id="2857" class="Symbol">)</a>
<a id="2859" class="Keyword">open</a> <a id="2864" href="POPL.FreeModel.html#745" class="Module">FreeModel</a> <a id="2874" class="Keyword">using</a> <a id="2880" class="Symbol">(</a><a id="2881" href="POPL.FreeModel.html#1223" class="Field">ext-uniq</a><a id="2889" class="Symbol">;</a> <a id="2891" href="POPL.FreeModel.html#1632" class="Function">μ</a><a id="2892" class="Symbol">;</a> <a id="2894" href="POPL.FreeModel.html#1555" class="Function">map</a><a id="2897" class="Symbol">)</a>

<a id="2900" class="Comment">-- §2.3 Fig. 1 syntax of CBPV(𝒯) and CBPV⁺(𝒯)</a>
<a id="2946" class="Keyword">open</a> <a id="2951" href="POPL.Types.html" class="Module">POPL.Types</a> <a id="2962" class="Keyword">using</a> <a id="2968" class="Symbol">(</a><a id="2969" href="POPL.Types.html#499" class="Datatype">VTy</a><a id="2972" class="Symbol">;</a> <a id="2974" href="POPL.Types.html#515" class="Datatype">CTy</a><a id="2977" class="Symbol">;</a> <a id="2979" href="POPL.Types.html#1215" class="Datatype">Mode</a><a id="2983" class="Symbol">)</a>
<a id="2985" class="Keyword">open</a> <a id="2990" href="POPL.Syntax.html" class="Module">POPL.Syntax</a> <a id="3002" class="Keyword">using</a> <a id="3008" class="Symbol">(</a><a id="3009" href="POPL.Syntax.html#1048" class="Datatype">Val</a><a id="3012" class="Symbol">;</a> <a id="3014" href="POPL.Syntax.html#1093" class="Datatype">Comp</a><a id="3018" class="Symbol">;</a> <a id="3020" href="POPL.Syntax.html#1138" class="Datatype">Stack</a><a id="3025" class="Symbol">)</a>

<a id="3028" class="Comment">-- §2.3 Fig. 2 operations: V[γ], M[γ], S[γ], δ[γ], S[M], S&#39;[S]</a>
<a id="3091" class="Keyword">open</a> <a id="3096" href="POPL.Renaming.html" class="Module">POPL.Renaming</a> <a id="3110" class="Keyword">using</a> <a id="3116" class="Symbol">(</a><a id="3117" href="POPL.Renaming.html#730" class="Function">renC</a><a id="3121" class="Symbol">)</a>
<a id="3123" class="Keyword">open</a> <a id="3128" href="POPL.Substitution.html" class="Module">POPL.Substitution</a> <a id="3146" class="Keyword">using</a> <a id="3152" class="Symbol">(</a><a id="3153" href="POPL.Substitution.html#762" class="Function">subV</a><a id="3157" class="Symbol">;</a> <a id="3159" href="POPL.Substitution.html#805" class="Function">subC</a><a id="3163" class="Symbol">;</a> <a id="3165" href="POPL.Substitution.html#850" class="Function">subS</a><a id="3169" class="Symbol">;</a> <a id="3171" href="POPL.Substitution.html#2412" class="Function Operator">_⊚_</a><a id="3174" class="Symbol">)</a>
<a id="3176" class="Keyword">open</a> <a id="3181" href="POPL.Plug.html" class="Module">POPL.Plug</a> <a id="3191" class="Keyword">using</a> <a id="3197" class="Symbol">(</a><a id="3198" href="POPL.Plug.html#454" class="Function">plug</a><a id="3202" class="Symbol">;</a> <a id="3204" href="POPL.Plug.html#814" class="Function Operator">_∘ˢ_</a><a id="3208" class="Symbol">;</a> <a id="3210" href="POPL.Plug.html#1893" class="Function">plug-sub</a><a id="3218" class="Symbol">)</a>

<a id="3221" class="Comment">-- §2.3 Fig. 2 equational theory</a>
<a id="3254" class="Keyword">open</a> <a id="3259" href="POPL.Equational.html" class="Module">POPL.Equational</a> <a id="3275" class="Keyword">using</a> <a id="3281" class="Symbol">(</a><a id="3282" href="POPL.Equational.html#3013" class="Datatype Operator">_≈v_</a><a id="3286" class="Symbol">;</a> <a id="3288" href="POPL.Equational.html#3074" class="Datatype Operator">_≈c_</a><a id="3292" class="Symbol">)</a>
</pre>
### Denotational semantics and equational canonicity (§3)

<pre class="Agda"><a id="3366" class="Comment">-- §3.2 Fig. 3 denotational semantics</a>
<a id="3404" class="Keyword">open</a> <a id="3409" href="POPL.Denotation.html" class="Module">POPL.Denotation</a> <a id="3425" class="Keyword">using</a> <a id="3431" class="Symbol">(</a><a id="3432" href="POPL.Denotation.html#1642" class="Function Operator">⟦_⟧v</a><a id="3436" class="Symbol">;</a> <a id="3438" href="POPL.Denotation.html#1660" class="Function Operator">⟦_⟧c</a><a id="3442" class="Symbol">;</a> <a id="3444" href="POPL.Denotation.html#2234" class="Function Operator">⟦_⟧V</a><a id="3448" class="Symbol">;</a> <a id="3450" href="POPL.Denotation.html#2268" class="Function Operator">⟦_⟧C</a><a id="3454" class="Symbol">;</a> <a id="3456" href="POPL.Denotation.html#2302" class="Function Operator">⟦_⟧S</a><a id="3460" class="Symbol">)</a>
<a id="3462" class="Keyword">open</a> <a id="3467" href="POPL.Models.html#350" class="Module">POPL.Models.Models-of</a> <a id="3489" class="Keyword">using</a> <a id="3495" class="Symbol">(</a><a id="3496" href="POPL.Models.html#949" class="Function">powModel</a><a id="3504" class="Symbol">;</a> <a id="3506" href="POPL.Models.html#1889" class="Function">prodModel</a><a id="3515" class="Symbol">)</a>

<a id="3518" class="Comment">-- §3.2 the denotation preserves substitution, plugging and operations</a>
<a id="3589" class="Keyword">open</a> <a id="3594" href="POPL.DenotationLemmas.html" class="Module">POPL.DenotationLemmas</a> <a id="3616" class="Keyword">using</a> <a id="3622" class="Symbol">(</a><a id="3623" href="POPL.DenotationLemmas.html#6656" class="Function">den-subC</a><a id="3631" class="Symbol">;</a> <a id="3633" href="POPL.DenotationLemmas.html#11466" class="Function">den-plug</a><a id="3641" class="Symbol">;</a> <a id="3643" href="POPL.DenotationLemmas.html#12237" class="Function">den-stack-hom</a><a id="3656" class="Symbol">)</a>

<a id="3659" class="Comment">-- §3.2 soundness of ⟦-⟧ for the equations</a>
<a id="3702" class="Keyword">open</a> <a id="3707" href="POPL.EquationalSoundness.html" class="Module">POPL.EquationalSoundness</a> <a id="3732" class="Keyword">using</a> <a id="3738" class="Symbol">(</a><a id="3739" href="POPL.EquationalSoundness.html#1966" class="Function">sound-c</a><a id="3746" class="Symbol">)</a>

<a id="3749" class="Comment">-- §3.3 Fig. 6 equational logical relation</a>
<a id="3792" class="Keyword">open</a> <a id="3797" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="3820" class="Keyword">using</a> <a id="3826" class="Symbol">(</a><a id="3827" href="POPL.EqLogicalRelation.html#1918" class="Function Operator">𝒱⟦_⟧</a><a id="3831" class="Symbol">;</a> <a id="3833" href="POPL.EqLogicalRelation.html#1951" class="Function Operator">𝒞⟦_⟧</a><a id="3837" class="Symbol">;</a> <a id="3839" href="POPL.EqLogicalRelation.html#1654" class="Datatype">FPred</a><a id="3844" class="Symbol">)</a>

<a id="3847" class="Comment">-- §3.4 Fundamental Theorem</a>
<a id="3875" class="Keyword">open</a> <a id="3880" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="3903" class="Keyword">using</a> <a id="3909" class="Symbol">(</a><a id="3910" href="POPL.EqLogicalRelation.html#4697" class="Function">fundV</a><a id="3915" class="Symbol">;</a> <a id="3917" href="POPL.EqLogicalRelation.html#4729" class="Function">fundC</a><a id="3922" class="Symbol">)</a>

<a id="3925" class="Comment">-- §3.4 Corollary (equational canonicity)</a>
<a id="3967" class="Keyword">open</a> <a id="3972" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="3995" class="Keyword">using</a> <a id="4001" class="Symbol">(</a><a id="4002" href="POPL.EqLogicalRelation.html#8241" class="Function">equational-canonicity</a><a id="4023" class="Symbol">)</a>

<a id="4026" class="Comment">-- §3.4 Corollary (uniqueness; corrected, C3)</a>
<a id="4072" class="Keyword">open</a> <a id="4077" href="POPL.EqCanonicity.html" class="Module">POPL.EqCanonicity</a> <a id="4095" class="Keyword">using</a> <a id="4101" class="Symbol">(</a><a id="4102" href="POPL.EqCanonicity.html#1862" class="Function">canonical-form-unique</a><a id="4123" class="Symbol">)</a>
</pre>
### Tree reduction (§4)

<pre class="Agda"><a id="4163" class="Comment">-- §4.1 Fig. 5 tree reduction</a>
<a id="4193" class="Keyword">open</a> <a id="4198" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a> <a id="4217" class="Keyword">using</a> <a id="4223" class="Symbol">(</a><a id="4224" href="POPL.TreeReduction.html#1968" class="Datatype Operator">_↦red_</a><a id="4230" class="Symbol">;</a> <a id="4232" href="POPL.TreeReduction.html#2934" class="Datatype Operator">_↦h_</a><a id="4236" class="Symbol">;</a> <a id="4238" href="POPL.TreeReduction.html#3190" class="Datatype Operator">_↦_</a><a id="4241" class="Symbol">;</a> <a id="4243" href="POPL.TreeReduction.html#11326" class="Function">det</a><a id="4246" class="Symbol">)</a>

<a id="4249" class="Comment">-- §4.1 Theorem (soundness of ↦tree)</a>
<a id="4286" class="Keyword">open</a> <a id="4291" href="POPL.TreeSoundness.html" class="Module">POPL.TreeSoundness</a> <a id="4310" class="Keyword">using</a> <a id="4316" class="Symbol">(</a><a id="4317" href="POPL.TreeSoundness.html#1747" class="Function">sound↦</a><a id="4323" class="Symbol">)</a>

<a id="4326" class="Comment">-- §4.2 Fig. 7 operational logical relation</a>
<a id="4370" class="Keyword">open</a> <a id="4375" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="4398" class="Keyword">using</a> <a id="4404" class="Symbol">(</a><a id="4405" href="POPL.OpLogicalRelation.html#5256" class="Function Operator">𝒱⟦_⟧</a><a id="4409" class="Symbol">;</a> <a id="4411" href="POPL.OpLogicalRelation.html#5289" class="Function Operator">𝒞⟦_⟧</a><a id="4415" class="Symbol">;</a> <a id="4417" href="POPL.OpLogicalRelation.html#4983" class="Datatype">FPred</a><a id="4422" class="Symbol">)</a>

<a id="4425" class="Comment">-- §4.2 Lemma (anti-reduction; corrected, C5)</a>
<a id="4471" class="Keyword">open</a> <a id="4476" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a> <a id="4495" class="Keyword">using</a> <a id="4501" class="Symbol">(</a><a id="4502" href="POPL.TreeReduction.html#12217" class="Function">hjoin</a><a id="4507" class="Symbol">)</a>
<a id="4509" class="Keyword">open</a> <a id="4514" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="4537" class="Keyword">using</a> <a id="4543" class="Symbol">(</a><a id="4544" href="POPL.OpLogicalRelation.html#5911" class="Function">AR</a><a id="4546" class="Symbol">;</a> <a id="4548" href="POPL.OpLogicalRelation.html#5976" class="Function">FW</a><a id="4550" class="Symbol">)</a>

<a id="4553" class="Comment">-- §4.2 Lemma (congruence)</a>
<a id="4580" class="Keyword">open</a> <a id="4585" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="4608" class="Keyword">using</a> <a id="4614" class="Symbol">(</a><a id="4615" href="POPL.OpLogicalRelation.html#7469" class="Function">𝒞-op</a><a id="4619" class="Symbol">)</a>

<a id="4622" class="Comment">-- §4.3 Fundamental Lemma</a>
<a id="4648" class="Keyword">open</a> <a id="4653" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="4676" class="Keyword">using</a> <a id="4682" class="Symbol">(</a><a id="4683" href="POPL.OpLogicalRelation.html#9896" class="Function">fundV</a><a id="4688" class="Symbol">;</a> <a id="4690" href="POPL.OpLogicalRelation.html#9932" class="Function">fundC</a><a id="4695" class="Symbol">;</a> <a id="4697" href="POPL.OpLogicalRelation.html#11374" class="Function">related</a><a id="4704" class="Symbol">)</a>

<a id="4707" class="Comment">-- §4.3 Corollary (termination)</a>
<a id="4739" class="Keyword">open</a> <a id="4744" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="4767" class="Keyword">using</a> <a id="4773" class="Symbol">(</a><a id="4774" href="POPL.TreeNormalization.html#4103" class="Function">termination</a><a id="4785" class="Symbol">)</a>

<a id="4788" class="Comment">-- §4.3 Corollary (strong normalization)</a>
<a id="4829" class="Keyword">open</a> <a id="4834" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="4857" class="Keyword">using</a> <a id="4863" class="Symbol">(</a><a id="4864" href="POPL.TreeNormalization.html#6686" class="Function">strong-normalization</a><a id="4884" class="Symbol">)</a>

<a id="4887" class="Comment">-- §4.3 Corollary (canonicity; corrected, C8)</a>
<a id="4933" class="Keyword">open</a> <a id="4938" href="POPL.TreeCanonicity.html" class="Module">POPL.TreeCanonicity</a> <a id="4958" class="Keyword">using</a> <a id="4964" class="Symbol">(</a><a id="4965" href="POPL.TreeCanonicity.html#1406" class="Function">tree-canonicity</a><a id="4980" class="Symbol">)</a>
</pre>
### Configuration reduction (§5)

<pre class="Agda"><a id="5029" class="Comment">-- §5.2 polynomials, ∂p, plugging</a>
<a id="5063" class="Keyword">open</a> <a id="5068" href="POPL.Polynomial.html" class="Module">POPL.Polynomial</a> <a id="5084" class="Keyword">using</a> <a id="5090" class="Symbol">(</a><a id="5091" href="POPL.Polynomial.html#1102" class="Record">Poly</a><a id="5095" class="Symbol">;</a> <a id="5097" href="POPL.Polynomial.html#1196" class="Function Operator">⟦_⟧</a><a id="5100" class="Symbol">;</a> <a id="5102" href="POPL.Polynomial.html#1491" class="Function">∂</a><a id="5103" class="Symbol">;</a> <a id="5105" href="POPL.Polynomial.html#1898" class="Function">plug</a><a id="5109" class="Symbol">;</a> <a id="5111" href="POPL.Polynomial.html#2456" class="Function">plug-map</a><a id="5119" class="Symbol">)</a>

<a id="5122" class="Comment">-- §5.2 Def. (Operational Model)</a>
<a id="5155" class="Keyword">open</a> <a id="5160" href="POPL.OperationalModel.html" class="Module">POPL.OperationalModel</a> <a id="5182" class="Keyword">using</a> <a id="5188" class="Symbol">(</a><a id="5189" href="POPL.OperationalModel.html#539" class="Record">OperationalModel</a><a id="5205" class="Symbol">)</a>

<a id="5208" class="Comment">-- §5.3 Fig. &quot;Configuration Reduction&quot; (derivative form)</a>
<a id="5265" class="Keyword">open</a> <a id="5270" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="5291" class="Keyword">using</a> <a id="5297" class="Symbol">(</a><a id="5298" href="POPL.ConfigReduction.html#2128" class="Datatype Operator">_↦T_</a><a id="5302" class="Symbol">)</a>

<a id="5305" class="Comment">-- §5.3 Theorem (soundness of the initial configuration)</a>
<a id="5362" class="Keyword">open</a> <a id="5367" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="5388" class="Keyword">using</a> <a id="5394" class="Symbol">(</a><a id="5395" href="POPL.ConfigReduction.html#2938" class="Function">sound-init</a><a id="5405" class="Symbol">)</a>

<a id="5408" class="Comment">-- §5.3 Theorem (soundness of ↦T)</a>
<a id="5442" class="Keyword">open</a> <a id="5447" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="5468" class="Keyword">using</a> <a id="5474" class="Symbol">(</a><a id="5475" href="POPL.ConfigReduction.html#3612" class="Function">sound-T</a><a id="5482" class="Symbol">)</a>

<a id="5485" class="Comment">-- §5.4 Def. (Affinity), and appendix &quot;Simplification&quot;</a>
<a id="5540" class="Keyword">open</a> <a id="5545" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="5566" class="Keyword">using</a> <a id="5572" class="Symbol">(</a><a id="5573" href="POPL.ConfigReduction.html#4970" class="Function">step</a><a id="5577" class="Symbol">;</a> <a id="5579" href="POPL.ConfigReduction.html#5250" class="Function">ρ</a><a id="5580" class="Symbol">;</a> <a id="5582" href="POPL.ConfigReduction.html#5536" class="Function">Affine</a><a id="5588" class="Symbol">;</a> <a id="5590" href="POPL.ConfigReduction.html#5718" class="Function">simplification</a><a id="5604" class="Symbol">;</a> <a id="5606" href="POPL.ConfigReduction.html#6377" class="Function">effect-via-step</a><a id="5621" class="Symbol">)</a>

<a id="5624" class="Comment">-- §5.4 Lemma (Progress)</a>
<a id="5649" class="Keyword">open</a> <a id="5654" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="5679" class="Keyword">using</a> <a id="5685" class="Symbol">(</a><a id="5686" href="POPL.ConfigNormalization.html#8153" class="Function">progress-T</a><a id="5696" class="Symbol">)</a>

<a id="5699" class="Comment">-- §5.4 Def. (Termination Metric; corrected, C7)</a>
<a id="5748" class="Keyword">open</a> <a id="5753" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="5776" class="Keyword">using</a> <a id="5782" class="Symbol">(</a><a id="5783" href="POPL.TreeNormalization.html#4346" class="Function">size</a><a id="5787" class="Symbol">;</a> <a id="5789" href="POPL.TreeNormalization.html#6016" class="Function Operator">‖_‖</a><a id="5792" class="Symbol">)</a>
<a id="5794" class="Keyword">open</a> <a id="5799" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="5824" class="Keyword">using</a> <a id="5830" class="Symbol">(</a><a id="5831" href="POPL.ConfigNormalization.html#5205" class="Function Operator">‖_‖T</a><a id="5835" class="Symbol">)</a>

<a id="5838" class="Comment">-- §5.4 Theorem (strong normalization for ↦T)</a>
<a id="5884" class="Keyword">open</a> <a id="5889" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="5914" class="Keyword">using</a> <a id="5920" class="Symbol">(</a><a id="5921" href="POPL.ConfigNormalization.html#7236" class="Function">strong-normalization-T</a><a id="5943" class="Symbol">;</a> <a id="5945" href="POPL.ConfigNormalization.html#8949" class="Function">normalize-T</a><a id="5956" class="Symbol">;</a> <a id="5958" href="POPL.ConfigNormalization.html#9367" class="Function">canonicity-T</a><a id="5970" class="Symbol">)</a>

<a id="5973" class="Comment">-- §5.4 Lemma (uniqueness of the result)</a>
<a id="6014" class="Keyword">open</a> <a id="6019" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6044" class="Keyword">using</a> <a id="6050" class="Symbol">(</a><a id="6051" href="POPL.ConfigNormalization.html#9893" class="Function">final-unique</a><a id="6063" class="Symbol">;</a> <a id="6065" href="POPL.ConfigNormalization.html#11328" class="Function">ground-canonicity</a><a id="6082" class="Symbol">)</a>
</pre>
### Instances (§2.2, §5.3)

<pre class="Agda"><a id="6125" class="Comment">-- Writer: theory, free model, affinity, derived rule</a>
<a id="6179" class="Keyword">open</a> <a id="6184" href="POPL.Instances.Writer.html" class="Module">POPL.Instances.Writer</a> <a id="6206" class="Keyword">using</a> <a id="6212" class="Symbol">(</a><a id="6213" href="POPL.Instances.Writer.html#1700" class="Function">writerTheory</a><a id="6225" class="Symbol">;</a> <a id="6227" href="POPL.Instances.Writer.html#3022" class="Function">writerFree</a><a id="6237" class="Symbol">;</a> <a id="6239" href="POPL.Instances.Writer.html#3577" class="Function">writerOM</a><a id="6247" class="Symbol">;</a> <a id="6249" href="POPL.Instances.Writer.html#3879" class="Function">writer-affine</a><a id="6262" class="Symbol">;</a> <a id="6264" href="POPL.Instances.Writer.html#4150" class="Function">writer-effect</a><a id="6277" class="Symbol">)</a>

<a id="6280" class="Comment">-- Errors</a>
<a id="6290" class="Keyword">open</a> <a id="6295" href="POPL.Instances.Errors.html" class="Module">POPL.Instances.Errors</a> <a id="6317" class="Keyword">using</a> <a id="6323" class="Symbol">(</a><a id="6324" href="POPL.Instances.Errors.html#957" class="Function">errTheory</a><a id="6333" class="Symbol">;</a> <a id="6335" href="POPL.Instances.Errors.html#2032" class="Function">errFree</a><a id="6342" class="Symbol">;</a> <a id="6344" href="POPL.Instances.Errors.html#2291" class="Function">errOM</a><a id="6349" class="Symbol">;</a> <a id="6351" href="POPL.Instances.Errors.html#2585" class="Function">err-affine</a><a id="6361" class="Symbol">;</a> <a id="6363" href="POPL.Instances.Errors.html#2910" class="Function">err-effect</a><a id="6373" class="Symbol">)</a>

<a id="6376" class="Comment">-- Boolean state, and the get and set rules</a>
<a id="6420" class="Keyword">open</a> <a id="6425" href="POPL.Instances.State.html" class="Module">POPL.Instances.State</a> <a id="6446" class="Keyword">using</a> <a id="6452" class="Symbol">(</a><a id="6453" href="POPL.Instances.State.html#2624" class="Function">stateTheory</a><a id="6464" class="Symbol">;</a> <a id="6466" href="POPL.Instances.State.html#6159" class="Function">stateFree</a><a id="6475" class="Symbol">;</a> <a id="6477" href="POPL.Instances.State.html#6383" class="Function">stateOM</a><a id="6484" class="Symbol">;</a> <a id="6486" href="POPL.Instances.State.html#6964" class="Function">state-affine</a><a id="6498" class="Symbol">;</a> <a id="6500" href="POPL.Instances.State.html#8043" class="Function">state-get</a><a id="6509" class="Symbol">;</a> <a id="6511" href="POPL.Instances.State.html#8408" class="Function">state-set</a><a id="6520" class="Symbol">)</a>

<a id="6523" class="Comment">-- Weighted monoid</a>
<a id="6542" class="Keyword">open</a> <a id="6547" href="POPL.Instances.WeightedMonoid.html" class="Module">POPL.Instances.WeightedMonoid</a> <a id="6577" class="Keyword">using</a> <a id="6583" class="Symbol">(</a><a id="6584" href="POPL.Instances.WeightedMonoid.html#3589" class="Function">wmTheory</a><a id="6592" class="Symbol">;</a> <a id="6594" href="POPL.Instances.WeightedMonoid.html#11987" class="Function">wmFree</a><a id="6600" class="Symbol">;</a> <a id="6602" href="POPL.Instances.WeightedMonoid.html#13766" class="Function">wmOM</a><a id="6606" class="Symbol">)</a>
<a id="6608" class="Keyword">open</a> <a id="6613" href="POPL.Instances.WeightedMonoidAffine.html" class="Module">POPL.Instances.WeightedMonoidAffine</a> <a id="6649" class="Keyword">using</a> <a id="6655" class="Symbol">(</a><a id="6656" href="POPL.Instances.WeightedMonoidAffine.html#5703" class="Function">wm-affine</a><a id="6665" class="Symbol">)</a>
<a id="6667" class="Keyword">open</a> <a id="6672" href="POPL.Instances.WeightedMonoidRules.html" class="Module">POPL.Instances.WeightedMonoidRules</a> <a id="6707" class="Keyword">using</a> <a id="6713" class="Symbol">(</a><a id="6714" href="POPL.Instances.WeightedMonoidRules.html#2226" class="Function">wm-act</a><a id="6720" class="Symbol">;</a> <a id="6722" href="POPL.Instances.WeightedMonoidRules.html#2765" class="Function">wm-unit</a><a id="6729" class="Symbol">;</a> <a id="6731" href="POPL.Instances.WeightedMonoidRules.html#3077" class="Function">wm-mul</a><a id="6737" class="Symbol">)</a>
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
| C1 | Def. "Operational Model": "T(X) is the free model of 𝒯 generated by T". | "…generated by X". | [`OperationalModel.agda`](POPL.OperationalModel.html) |
| C2 | Fig. 3: `⟦tt⟧(γ) = {⋆}`. | `⟦⋆⟧(γ) = ⋆`: an element, not a set. | [`Denotation.agda`](POPL.Denotation.html) |
| C3 | §3.4, uniqueness corollary: if `Val(A) ≅ ⟦A⟧` then `∃! t : Term_Σ(Val A). M = reify(t)`. | False when the theory has equations. For writer, `tell_e(ret V) = ret V`, so `tell_e(var V)` and `var V` both reify to `M`. What holds is uniqueness of the canonical form's image `⌊t⌋` in the free model `T⟦A⟧`, and `⌊t⌋ = ⟦M⟧`. | [`EqCanonicity.agda`](POPL.EqCanonicity.html) |
| C4 | Fig. 5 lists the `case×` redex twice and has no rule for `π₁⟨M,N⟩`. | Adds `π₁⟨M,N⟩ ↦ M`. | [`TreeReduction.agda`](POPL.TreeReduction.html) |
| C6 | Fig. 7 defines `𝒱[1]` only at `⋆`, and `𝒱[A+A']`, `𝒱[A×A']` only at `σᵢ W` and pairs. | Every undefined clause is read as `⊥`. In CBPV(𝒯) the only other closed values of these types have the form `absurd V`, and no closed values of type `0` exist. | [`OpLogicalRelation.agda`](POPL.OpLogicalRelation.html) |
| C7 | §5.4, Def. "Termination Metric": `\|M\| = max_{M↦N} \|N\|` for `M ≠ op`. Under this definition a pure step does not decrease the metric. | `\|M\| = 1 + \|N\|` for the unique `N`, which is unique by determinism. The metric is defined on derivations of `𝒞⟦FA⟧` and shown not to depend on the derivation. | [`TreeNormalization.agda`](POPL.TreeNormalization.html) |
| C8 | §4.3, last corollary: if `⟦·⟧_A` is a bijection, then `M ↦* reify(⟦M⟧)`. This is ill-typed: `⟦M⟧ ∈ T⟦A⟧`, but `reify` takes a `Term_Σ`. | For every `A`: there is a `t` with `M ↦* reify t` and `⌊t⌋ = ⟦M⟧` in `T⟦A⟧`. No bijection is needed. | [`TreeCanonicity.agda`](POPL.TreeCanonicity.html) |
| C9 | §5.3, state example: the get rule's right-hand side has `(b_f, N_f)`. | The position that is not reduced keeps its term: `(b_f, N)`. | [`Instances/State.agda`](POPL.Instances.State.html) |
| C10 | §2.1–2.2, weighted monoid: `act_m` for `m : M`, and `η(x) = [(e, x)]`. | `act_r` for `r : R`, and `η(x) = [(1_R, x)]`. | [`Instances/WeightedMonoid.agda`](POPL.Instances.WeightedMonoid.html) |

### Deviations

| Tag | Paper | Formalization | Code |
|---|---|---|---|
| D1 | Carriers of algebras and models are sets. | Carriers are arbitrary types. No result uses set-ness, and every concrete carrier is a set. | [`Theory.agda`](POPL.Theory.html) |
| D2 | `∂p(X) = Σ s. Σ i. X^{P(s)∖{i}}`. The derivative is commented out of the paper and appears in the `results.tex` appendix. | Same definition. The remaining positions are `Fin∖ n i = Σ j. j ≢ i`, and `plug` decides `j ≡ i`, so it computes without transport. As requested, the Effect rule uses this derivative form throughout. | [`Polynomial.agda`](POPL.Polynomial.html) |
| D3 | `⟦-⟧` comes from initiality of the CBPV⁺ doctrine (§3.1). | `⟦-⟧` is defined directly by the recursive equations of Fig. 3. The facts initiality would provide are proved by induction: the substitution and plugging lemmas, algebraicity of stacks, and soundness for `≈`. The doctrine itself is not formalized. | [`Denotation.agda`](POPL.Denotation.html), [`DenotationLemmas.agda`](POPL.DenotationLemmas.html), [`EquationalSoundness.agda`](POPL.EquationalSoundness.html) |
| D4 | CBPV⁺ terms are a quotient by the equational theory. | Terms are plain inductive data, and the equational theory is an inductive relation `≈`. CBPV(𝒯) and CBPV⁺(𝒯) share one mode-indexed syntax (`Types.agda`); the grey rules of Fig. 1 exist only in mode `cbpv⁺`. Computations and stacks are separate types rather than one judgement with a stoup. | [`Equational.agda`](POPL.Equational.html), [`Syntax.agda`](POPL.Syntax.html) |
| D5 | Fig. 2 gives a "fragment" of the β/η laws. | The standard full set (Levy). The η laws for `+`, `×` and `0` are in substitution form. F-η is the general stack form `S[M] = x ← M; S[ret x]`. | [`Equational.agda`](POPL.Equational.html) |
| D6 | The logical relations are glued models; the fundamental theorems follow from initiality. | Relations defined by hand by recursion on types, with `𝒞⟦FA⟧` inductive. Fundamental theorems proved by induction on terms. | [`EqLogicalRelation.agda`](POPL.EqLogicalRelation.html), [`OpLogicalRelation.agda`](POPL.OpLogicalRelation.html) |
| D7 | Fig. 6 says "V = σᵢ W", "(V,V')", and so on; these presume the quotient. | The equational predicates are closed under `≈` by construction: `𝒱⟦A+A'⟧ V` asks for `V ≈ σᵢ W`, and `𝒞⟦FA⟧` has a `conv` clause. This follows from D4. | [`EqLogicalRelation.agda`](POPL.EqLogicalRelation.html) |
| D8 | Fig. 5 has the redex rules plus `S[M] ↦ S[M']` for `S ≠ •`. | A single rule `S[M] ↦ S[M']` for every `S`, including `•`. The relation is the same, without overlap. | [`TreeReduction.agda`](POPL.TreeReduction.html) |
| D9 | Strong normalization (§4.3 for `↦tree`, §5.4 for `↦T`) is proved by a classical argument on infinite sequences. | Stated constructively as accessibility (`Acc`) for converse reduction, and derived from the decreasing metric. | [`TreeNormalization.agda`](POPL.TreeNormalization.html), [`ConfigNormalization.agda`](POPL.ConfigNormalization.html) |
| D10 | The Effect rule is written in substitution notation: `⟨s, γ, S[op M⃗]/xᵢ⟩ ↦T T(γ ⊎ S[M⃗])(T(ρ)(s ∘ᵢ op))`. | As requested, the derivative form from the appendix: `C⟪S[op M⃗]⟫ ↦T μ((∂η C)⟪⟦op⟧(η(S[M⃗]))⟫)`. Affinity is stated through the generic step `step(s,i,op) = μ(∂(η∘σ₁)(Cₛⁱ)⟪T(σ₂)⌈op⌉⟫)`, whose shape is `s ∘ᵢ op` and whose positions are `ρ`. The appendix's "Simplification" lemma, `effect-via-step`, shows that the derivative form equals the paper's form. | [`ConfigReduction.agda`](POPL.ConfigReduction.html) |
| D11 | Progress (§5.4) is stated for closed computations, by inspecting the term. | Proved from the logical relation (a derivation is `ret`, `op`, or a step) and stated for configurations: a configuration is `T(ret)(ṽ)` or it steps. | [`ConfigNormalization.agda`](POPL.ConfigNormalization.html) |
| D12 | The uniqueness lemma (§5.4) assumes `⟦·⟧ : Val(A) ≅ ⟦A⟧`. | Assumes only a left inverse. `Ground` types (built from 0, 1, +, ×) have one. Uniqueness does not use affinity. | [`ConfigNormalization.agda`](POPL.ConfigNormalization.html) |
| D13 | §2.1 lists the lens laws for state only as "including" two of them. | The standard complete set (Plotkin–Power): get-set, set-get, set-set, get-get. | [`Instances/State.agda`](POPL.Instances.State.html) |
| D14 | Weighted monoid: shapes `List(R)` with `P(l) = len(l)`. | The isomorphic shapes `Σ n. (Fin n → R)` with `P = n`, so that positions are definitionally `Fin n`. The operations are computed on lists through a bijection. | [`Instances/WeightedMonoid.agda`](POPL.Instances.WeightedMonoid.html) |

## Not formalized

- **The CBPV⁺ doctrine (§3.1) and the glued models.** The user asked for no gluing. The results these give are proved directly (D3, D6).
- **The free models of R-semimodules, convex spaces and pre-convex spaces.**
  - Semimodules and convex spaces are not operational models in the paper either.
  - Pre-convex spaces would need real numbers in [0, 1].
- **The syntactic free model `Term_𝒯 X` as a quotient-inductive type (§2.1, Example).** Nothing in the paper's results depends on it. The free model is an input, given by a universal property.

{% endraw %}
