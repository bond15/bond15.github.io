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

<a id="635" class="Keyword">import</a> <a id="642" href="POPL.Models.html" class="Module">POPL.Models</a>
<a id="654" class="Keyword">import</a> <a id="661" href="POPL.Fin.html" class="Module">POPL.Fin</a>
<a id="670" class="Keyword">import</a> <a id="677" href="POPL.Instances.Common.html" class="Module">POPL.Instances.Common</a>
<a id="699" class="Keyword">import</a> <a id="706" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a>
<a id="731" class="Keyword">import</a> <a id="738" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a>
<a id="759" class="Keyword">import</a> <a id="766" href="POPL.Denotation.html" class="Module">POPL.Denotation</a>
<a id="782" class="Keyword">import</a> <a id="789" href="POPL.DenotationLemmas.html" class="Module">POPL.DenotationLemmas</a>
<a id="811" class="Keyword">import</a> <a id="818" href="POPL.EqCanonicity.html" class="Module">POPL.EqCanonicity</a>
<a id="836" class="Keyword">import</a> <a id="843" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a>
<a id="866" class="Keyword">import</a> <a id="873" href="POPL.Equational.html" class="Module">POPL.Equational</a>
<a id="889" class="Keyword">import</a> <a id="896" href="POPL.EquationalSoundness.html" class="Module">POPL.EquationalSoundness</a>
<a id="921" class="Keyword">import</a> <a id="928" href="POPL.FreeModel.html" class="Module">POPL.FreeModel</a>
<a id="943" class="Keyword">import</a> <a id="950" href="POPL.Instances.Errors.html" class="Module">POPL.Instances.Errors</a>
<a id="972" class="Keyword">import</a> <a id="979" href="POPL.Instances.State.html" class="Module">POPL.Instances.State</a>
<a id="1000" class="Keyword">import</a> <a id="1007" href="POPL.Instances.WeightedMonoid.html" class="Module">POPL.Instances.WeightedMonoid</a>
<a id="1037" class="Keyword">import</a> <a id="1044" href="POPL.Instances.WeightedMonoidAffine.html" class="Module">POPL.Instances.WeightedMonoidAffine</a>
<a id="1080" class="Keyword">import</a> <a id="1087" href="POPL.Instances.WeightedMonoidRules.html" class="Module">POPL.Instances.WeightedMonoidRules</a>
<a id="1122" class="Keyword">import</a> <a id="1129" href="POPL.Instances.Writer.html" class="Module">POPL.Instances.Writer</a>
<a id="1151" class="Keyword">import</a> <a id="1158" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a>
<a id="1181" class="Keyword">import</a> <a id="1188" href="POPL.OperationalModel.html" class="Module">POPL.OperationalModel</a>
<a id="1210" class="Keyword">import</a> <a id="1217" href="POPL.Plug.html" class="Module">POPL.Plug</a>
<a id="1227" class="Keyword">import</a> <a id="1234" href="POPL.Polynomial.html" class="Module">POPL.Polynomial</a>
<a id="1250" class="Keyword">import</a> <a id="1257" href="POPL.Renaming.html" class="Module">POPL.Renaming</a>
<a id="1271" class="Keyword">import</a> <a id="1278" href="POPL.Substitution.html" class="Module">POPL.Substitution</a>
<a id="1296" class="Keyword">import</a> <a id="1303" href="POPL.Syntax.html" class="Module">POPL.Syntax</a>
<a id="1315" class="Keyword">import</a> <a id="1322" href="POPL.Theory.html" class="Module">POPL.Theory</a>
<a id="1334" class="Keyword">import</a> <a id="1341" href="POPL.TreeCanonicity.html" class="Module">POPL.TreeCanonicity</a>
<a id="1361" class="Keyword">import</a> <a id="1368" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a>
<a id="1391" class="Keyword">import</a> <a id="1398" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a>
<a id="1417" class="Keyword">import</a> <a id="1424" href="POPL.TreeSoundness.html" class="Module">POPL.TreeSoundness</a>
<a id="1443" class="Keyword">import</a> <a id="1450" href="POPL.Types.html" class="Module">POPL.Types</a>
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

<pre class="Agda"><a id="2775" class="Comment">-- §2.1 signatures, terms, equations, algebras, models</a>
<a id="2830" class="Keyword">open</a> <a id="2835" href="POPL.Theory.html" class="Module">POPL.Theory</a> <a id="2847" class="Keyword">using</a> <a id="2853" class="Symbol">(</a><a id="2854" href="POPL.Theory.html#675" class="Record">Signature</a><a id="2863" class="Symbol">;</a> <a id="2865" href="POPL.Theory.html#825" class="Datatype">Term</a><a id="2869" class="Symbol">;</a> <a id="2871" href="POPL.Theory.html#2041" class="Record">Theory</a><a id="2877" class="Symbol">;</a> <a id="2879" href="POPL.Theory.html#2402" class="Record">Model</a><a id="2884" class="Symbol">;</a> <a id="2886" href="POPL.Theory.html#1461" class="Record">IsHom</a><a id="2891" class="Symbol">)</a>

<a id="2894" class="Comment">-- §2.1 free model monad</a>
<a id="2919" class="Keyword">open</a> <a id="2924" href="POPL.FreeModel.html" class="Module">POPL.FreeModel</a> <a id="2939" class="Keyword">using</a> <a id="2945" class="Symbol">(</a><a id="2946" href="POPL.FreeModel.html#745" class="Record">FreeModel</a><a id="2955" class="Symbol">)</a>
<a id="2957" class="Keyword">open</a> <a id="2962" href="POPL.FreeModel.html#745" class="Module">FreeModel</a> <a id="2972" class="Keyword">using</a> <a id="2978" class="Symbol">(</a><a id="2979" href="POPL.FreeModel.html#1223" class="Field">ext-uniq</a><a id="2987" class="Symbol">;</a> <a id="2989" href="POPL.FreeModel.html#1632" class="Function">μ</a><a id="2990" class="Symbol">;</a> <a id="2992" href="POPL.FreeModel.html#1555" class="Function">map</a><a id="2995" class="Symbol">)</a>

<a id="2998" class="Comment">-- §2.3 Fig. 1 syntax of CBPV(𝒯) and CBPV⁺(𝒯)</a>
<a id="3044" class="Keyword">open</a> <a id="3049" href="POPL.Types.html" class="Module">POPL.Types</a> <a id="3060" class="Keyword">using</a> <a id="3066" class="Symbol">(</a><a id="3067" href="POPL.Types.html#499" class="Datatype">VTy</a><a id="3070" class="Symbol">;</a> <a id="3072" href="POPL.Types.html#515" class="Datatype">CTy</a><a id="3075" class="Symbol">;</a> <a id="3077" href="POPL.Types.html#1215" class="Datatype">Mode</a><a id="3081" class="Symbol">)</a>
<a id="3083" class="Keyword">open</a> <a id="3088" href="POPL.Syntax.html" class="Module">POPL.Syntax</a> <a id="3100" class="Keyword">using</a> <a id="3106" class="Symbol">(</a><a id="3107" href="POPL.Syntax.html#1048" class="Datatype">Val</a><a id="3110" class="Symbol">;</a> <a id="3112" href="POPL.Syntax.html#1093" class="Datatype">Comp</a><a id="3116" class="Symbol">;</a> <a id="3118" href="POPL.Syntax.html#1138" class="Datatype">Stack</a><a id="3123" class="Symbol">)</a>

<a id="3126" class="Comment">-- §2.3 Fig. 2 operations: V[γ], M[γ], S[γ], δ[γ], S[M], S&#39;[S]</a>
<a id="3189" class="Keyword">open</a> <a id="3194" href="POPL.Renaming.html" class="Module">POPL.Renaming</a> <a id="3208" class="Keyword">using</a> <a id="3214" class="Symbol">(</a><a id="3215" href="POPL.Renaming.html#730" class="Function">renC</a><a id="3219" class="Symbol">)</a>
<a id="3221" class="Keyword">open</a> <a id="3226" href="POPL.Substitution.html" class="Module">POPL.Substitution</a> <a id="3244" class="Keyword">using</a> <a id="3250" class="Symbol">(</a><a id="3251" href="POPL.Substitution.html#762" class="Function">subV</a><a id="3255" class="Symbol">;</a> <a id="3257" href="POPL.Substitution.html#805" class="Function">subC</a><a id="3261" class="Symbol">;</a> <a id="3263" href="POPL.Substitution.html#850" class="Function">subS</a><a id="3267" class="Symbol">;</a> <a id="3269" href="POPL.Substitution.html#2412" class="Function Operator">_⊚_</a><a id="3272" class="Symbol">)</a>
<a id="3274" class="Keyword">open</a> <a id="3279" href="POPL.Plug.html" class="Module">POPL.Plug</a> <a id="3289" class="Keyword">using</a> <a id="3295" class="Symbol">(</a><a id="3296" href="POPL.Plug.html#454" class="Function">plug</a><a id="3300" class="Symbol">;</a> <a id="3302" href="POPL.Plug.html#814" class="Function Operator">_∘ˢ_</a><a id="3306" class="Symbol">;</a> <a id="3308" href="POPL.Plug.html#1893" class="Function">plug-sub</a><a id="3316" class="Symbol">)</a>

<a id="3319" class="Comment">-- §2.3 Fig. 2 equational theory</a>
<a id="3352" class="Keyword">open</a> <a id="3357" href="POPL.Equational.html" class="Module">POPL.Equational</a> <a id="3373" class="Keyword">using</a> <a id="3379" class="Symbol">(</a><a id="3380" href="POPL.Equational.html#3013" class="Datatype Operator">_≈v_</a><a id="3384" class="Symbol">;</a> <a id="3386" href="POPL.Equational.html#3074" class="Datatype Operator">_≈c_</a><a id="3390" class="Symbol">)</a>
</pre>
### Denotational semantics and equational canonicity (§3)

<pre class="Agda"><a id="3464" class="Comment">-- §3.2 Fig. 3 denotational semantics</a>
<a id="3502" class="Keyword">open</a> <a id="3507" href="POPL.Denotation.html" class="Module">POPL.Denotation</a> <a id="3523" class="Keyword">using</a> <a id="3529" class="Symbol">(</a><a id="3530" href="POPL.Denotation.html#1525" class="Function Operator">⟦_⟧v</a><a id="3534" class="Symbol">;</a> <a id="3536" href="POPL.Denotation.html#1543" class="Function Operator">⟦_⟧c</a><a id="3540" class="Symbol">;</a> <a id="3542" href="POPL.Denotation.html#2117" class="Function Operator">⟦_⟧V</a><a id="3546" class="Symbol">;</a> <a id="3548" href="POPL.Denotation.html#2151" class="Function Operator">⟦_⟧C</a><a id="3552" class="Symbol">;</a> <a id="3554" href="POPL.Denotation.html#2185" class="Function Operator">⟦_⟧S</a><a id="3558" class="Symbol">)</a>
<a id="3560" class="Keyword">open</a> <a id="3565" href="POPL.Models.html#350" class="Module">POPL.Models.Models-of</a> <a id="3587" class="Keyword">using</a> <a id="3593" class="Symbol">(</a><a id="3594" href="POPL.Models.html#949" class="Function">powModel</a><a id="3602" class="Symbol">;</a> <a id="3604" href="POPL.Models.html#1889" class="Function">prodModel</a><a id="3613" class="Symbol">)</a>

<a id="3616" class="Comment">-- §3.2 the denotation preserves substitution, plugging and operations</a>
<a id="3687" class="Keyword">open</a> <a id="3692" href="POPL.DenotationLemmas.html" class="Module">POPL.DenotationLemmas</a> <a id="3714" class="Keyword">using</a> <a id="3720" class="Symbol">(</a><a id="3721" href="POPL.DenotationLemmas.html#6656" class="Function">den-subC</a><a id="3729" class="Symbol">;</a> <a id="3731" href="POPL.DenotationLemmas.html#11466" class="Function">den-plug</a><a id="3739" class="Symbol">;</a> <a id="3741" href="POPL.DenotationLemmas.html#12237" class="Function">den-stack-hom</a><a id="3754" class="Symbol">)</a>

<a id="3757" class="Comment">-- §3.2 soundness of ⟦-⟧ for the equations</a>
<a id="3800" class="Keyword">open</a> <a id="3805" href="POPL.EquationalSoundness.html" class="Module">POPL.EquationalSoundness</a> <a id="3830" class="Keyword">using</a> <a id="3836" class="Symbol">(</a><a id="3837" href="POPL.EquationalSoundness.html#1966" class="Function">sound-c</a><a id="3844" class="Symbol">)</a>

<a id="3847" class="Comment">-- §3.3 Fig. 6 equational logical relation</a>
<a id="3890" class="Keyword">open</a> <a id="3895" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="3918" class="Keyword">using</a> <a id="3924" class="Symbol">(</a><a id="3925" href="POPL.EqLogicalRelation.html#1918" class="Function Operator">𝒱⟦_⟧</a><a id="3929" class="Symbol">;</a> <a id="3931" href="POPL.EqLogicalRelation.html#1951" class="Function Operator">𝒞⟦_⟧</a><a id="3935" class="Symbol">;</a> <a id="3937" href="POPL.EqLogicalRelation.html#1654" class="Datatype">FPred</a><a id="3942" class="Symbol">)</a>

<a id="3945" class="Comment">-- §3.4 Fundamental Theorem</a>
<a id="3973" class="Keyword">open</a> <a id="3978" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="4001" class="Keyword">using</a> <a id="4007" class="Symbol">(</a><a id="4008" href="POPL.EqLogicalRelation.html#4697" class="Function">fundV</a><a id="4013" class="Symbol">;</a> <a id="4015" href="POPL.EqLogicalRelation.html#4729" class="Function">fundC</a><a id="4020" class="Symbol">)</a>

<a id="4023" class="Comment">-- §3.4 Corollary (equational canonicity)</a>
<a id="4065" class="Keyword">open</a> <a id="4070" href="POPL.EqLogicalRelation.html" class="Module">POPL.EqLogicalRelation</a> <a id="4093" class="Keyword">using</a> <a id="4099" class="Symbol">(</a><a id="4100" href="POPL.EqLogicalRelation.html#8241" class="Function">equational-canonicity</a><a id="4121" class="Symbol">)</a>

<a id="4124" class="Comment">-- §3.4 Corollary (uniqueness; corrected, C3)</a>
<a id="4170" class="Keyword">open</a> <a id="4175" href="POPL.EqCanonicity.html" class="Module">POPL.EqCanonicity</a> <a id="4193" class="Keyword">using</a> <a id="4199" class="Symbol">(</a><a id="4200" href="POPL.EqCanonicity.html#1862" class="Function">canonical-form-unique</a><a id="4221" class="Symbol">)</a>
</pre>
### Tree reduction (§4)

<pre class="Agda"><a id="4261" class="Comment">-- §4.1 Fig. 5 tree reduction</a>
<a id="4291" class="Keyword">open</a> <a id="4296" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a> <a id="4315" class="Keyword">using</a> <a id="4321" class="Symbol">(</a><a id="4322" href="POPL.TreeReduction.html#1982" class="Datatype Operator">_↦red_</a><a id="4328" class="Symbol">;</a> <a id="4330" href="POPL.TreeReduction.html#2948" class="Datatype Operator">_↦h_</a><a id="4334" class="Symbol">;</a> <a id="4336" href="POPL.TreeReduction.html#3204" class="Datatype Operator">_↦_</a><a id="4339" class="Symbol">;</a> <a id="4341" href="POPL.TreeReduction.html#11340" class="Function">det</a><a id="4344" class="Symbol">)</a>

<a id="4347" class="Comment">-- §4.1 Theorem (soundness of ↦tree)</a>
<a id="4384" class="Keyword">open</a> <a id="4389" href="POPL.TreeSoundness.html" class="Module">POPL.TreeSoundness</a> <a id="4408" class="Keyword">using</a> <a id="4414" class="Symbol">(</a><a id="4415" href="POPL.TreeSoundness.html#1747" class="Function">sound↦</a><a id="4421" class="Symbol">)</a>

<a id="4424" class="Comment">-- §4.2 Fig. 7 operational logical relation</a>
<a id="4468" class="Keyword">open</a> <a id="4473" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="4496" class="Keyword">using</a> <a id="4502" class="Symbol">(</a><a id="4503" href="POPL.OpLogicalRelation.html#5256" class="Function Operator">𝒱⟦_⟧</a><a id="4507" class="Symbol">;</a> <a id="4509" href="POPL.OpLogicalRelation.html#5289" class="Function Operator">𝒞⟦_⟧</a><a id="4513" class="Symbol">;</a> <a id="4515" href="POPL.OpLogicalRelation.html#4983" class="Datatype">FPred</a><a id="4520" class="Symbol">)</a>

<a id="4523" class="Comment">-- §4.2 Lemma (anti-reduction; corrected, C5)</a>
<a id="4569" class="Keyword">open</a> <a id="4574" href="POPL.TreeReduction.html" class="Module">POPL.TreeReduction</a> <a id="4593" class="Keyword">using</a> <a id="4599" class="Symbol">(</a><a id="4600" href="POPL.TreeReduction.html#12231" class="Function">hjoin</a><a id="4605" class="Symbol">)</a>
<a id="4607" class="Keyword">open</a> <a id="4612" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="4635" class="Keyword">using</a> <a id="4641" class="Symbol">(</a><a id="4642" href="POPL.OpLogicalRelation.html#5911" class="Function">AR</a><a id="4644" class="Symbol">;</a> <a id="4646" href="POPL.OpLogicalRelation.html#5976" class="Function">FW</a><a id="4648" class="Symbol">)</a>

<a id="4651" class="Comment">-- §4.2 Lemma (congruence)</a>
<a id="4678" class="Keyword">open</a> <a id="4683" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="4706" class="Keyword">using</a> <a id="4712" class="Symbol">(</a><a id="4713" href="POPL.OpLogicalRelation.html#7469" class="Function">𝒞-op</a><a id="4717" class="Symbol">)</a>

<a id="4720" class="Comment">-- §4.3 Fundamental Lemma</a>
<a id="4746" class="Keyword">open</a> <a id="4751" href="POPL.OpLogicalRelation.html" class="Module">POPL.OpLogicalRelation</a> <a id="4774" class="Keyword">using</a> <a id="4780" class="Symbol">(</a><a id="4781" href="POPL.OpLogicalRelation.html#9896" class="Function">fundV</a><a id="4786" class="Symbol">;</a> <a id="4788" href="POPL.OpLogicalRelation.html#9932" class="Function">fundC</a><a id="4793" class="Symbol">;</a> <a id="4795" href="POPL.OpLogicalRelation.html#11374" class="Function">related</a><a id="4802" class="Symbol">)</a>

<a id="4805" class="Comment">-- §4.3 Corollary (termination)</a>
<a id="4837" class="Keyword">open</a> <a id="4842" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="4865" class="Keyword">using</a> <a id="4871" class="Symbol">(</a><a id="4872" href="POPL.TreeNormalization.html#4103" class="Function">termination</a><a id="4883" class="Symbol">)</a>

<a id="4886" class="Comment">-- §4.3 Corollary (strong normalization)</a>
<a id="4927" class="Keyword">open</a> <a id="4932" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="4955" class="Keyword">using</a> <a id="4961" class="Symbol">(</a><a id="4962" href="POPL.TreeNormalization.html#6686" class="Function">strong-normalization</a><a id="4982" class="Symbol">)</a>

<a id="4985" class="Comment">-- §4.3 Corollary (canonicity; corrected, C8)</a>
<a id="5031" class="Keyword">open</a> <a id="5036" href="POPL.TreeCanonicity.html" class="Module">POPL.TreeCanonicity</a> <a id="5056" class="Keyword">using</a> <a id="5062" class="Symbol">(</a><a id="5063" href="POPL.TreeCanonicity.html#1406" class="Function">tree-canonicity</a><a id="5078" class="Symbol">)</a>
</pre>
### Configuration reduction (§5)

<pre class="Agda"><a id="5127" class="Comment">-- §5.2 polynomials, ∂p, plugging</a>
<a id="5161" class="Keyword">open</a> <a id="5166" href="POPL.Polynomial.html" class="Module">POPL.Polynomial</a> <a id="5182" class="Keyword">using</a> <a id="5188" class="Symbol">(</a><a id="5189" href="POPL.Polynomial.html#1032" class="Record">Poly</a><a id="5193" class="Symbol">;</a> <a id="5195" href="POPL.Polynomial.html#1126" class="Function Operator">⟦_⟧</a><a id="5198" class="Symbol">;</a> <a id="5200" href="POPL.Polynomial.html#1421" class="Function">∂</a><a id="5201" class="Symbol">;</a> <a id="5203" href="POPL.Polynomial.html#1828" class="Function">plug</a><a id="5207" class="Symbol">;</a> <a id="5209" href="POPL.Polynomial.html#2386" class="Function">plug-map</a><a id="5217" class="Symbol">)</a>

<a id="5220" class="Comment">-- §5.2 Def. (Operational Model)</a>
<a id="5253" class="Keyword">open</a> <a id="5258" href="POPL.OperationalModel.html" class="Module">POPL.OperationalModel</a> <a id="5280" class="Keyword">using</a> <a id="5286" class="Symbol">(</a><a id="5287" href="POPL.OperationalModel.html#417" class="Record">OperationalModel</a><a id="5303" class="Symbol">)</a>

<a id="5306" class="Comment">-- §5.3 Fig. &quot;Configuration Reduction&quot; (derivative form)</a>
<a id="5363" class="Keyword">open</a> <a id="5368" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="5389" class="Keyword">using</a> <a id="5395" class="Symbol">(</a><a id="5396" href="POPL.ConfigReduction.html#2128" class="Datatype Operator">_↦T_</a><a id="5400" class="Symbol">)</a>

<a id="5403" class="Comment">-- §5.3 Theorem (soundness of the initial configuration)</a>
<a id="5460" class="Keyword">open</a> <a id="5465" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="5486" class="Keyword">using</a> <a id="5492" class="Symbol">(</a><a id="5493" href="POPL.ConfigReduction.html#2938" class="Function">sound-init</a><a id="5503" class="Symbol">)</a>

<a id="5506" class="Comment">-- §5.3 Theorem (soundness of ↦T)</a>
<a id="5540" class="Keyword">open</a> <a id="5545" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="5566" class="Keyword">using</a> <a id="5572" class="Symbol">(</a><a id="5573" href="POPL.ConfigReduction.html#3612" class="Function">sound-T</a><a id="5580" class="Symbol">)</a>

<a id="5583" class="Comment">-- §5.4 Def. (Affinity), and appendix &quot;Simplification&quot;</a>
<a id="5638" class="Keyword">open</a> <a id="5643" href="POPL.ConfigReduction.html" class="Module">POPL.ConfigReduction</a> <a id="5664" class="Keyword">using</a> <a id="5670" class="Symbol">(</a><a id="5671" href="POPL.ConfigReduction.html#4970" class="Function">step</a><a id="5675" class="Symbol">;</a> <a id="5677" href="POPL.ConfigReduction.html#5250" class="Function">ρ</a><a id="5678" class="Symbol">;</a> <a id="5680" href="POPL.ConfigReduction.html#5536" class="Function">Affine</a><a id="5686" class="Symbol">;</a> <a id="5688" href="POPL.ConfigReduction.html#5718" class="Function">simplification</a><a id="5702" class="Symbol">;</a> <a id="5704" href="POPL.ConfigReduction.html#6377" class="Function">effect-via-step</a><a id="5719" class="Symbol">)</a>

<a id="5722" class="Comment">-- §5.4 Lemma (Progress)</a>
<a id="5747" class="Keyword">open</a> <a id="5752" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="5777" class="Keyword">using</a> <a id="5783" class="Symbol">(</a><a id="5784" href="POPL.ConfigNormalization.html#8153" class="Function">progress-T</a><a id="5794" class="Symbol">)</a>

<a id="5797" class="Comment">-- §5.4 Def. (Termination Metric; corrected, C7)</a>
<a id="5846" class="Keyword">open</a> <a id="5851" href="POPL.TreeNormalization.html" class="Module">POPL.TreeNormalization</a> <a id="5874" class="Keyword">using</a> <a id="5880" class="Symbol">(</a><a id="5881" href="POPL.TreeNormalization.html#4346" class="Function">size</a><a id="5885" class="Symbol">;</a> <a id="5887" href="POPL.TreeNormalization.html#6016" class="Function Operator">‖_‖</a><a id="5890" class="Symbol">)</a>
<a id="5892" class="Keyword">open</a> <a id="5897" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="5922" class="Keyword">using</a> <a id="5928" class="Symbol">(</a><a id="5929" href="POPL.ConfigNormalization.html#5205" class="Function Operator">‖_‖T</a><a id="5933" class="Symbol">)</a>

<a id="5936" class="Comment">-- §5.4 Theorem (strong normalization for ↦T)</a>
<a id="5982" class="Keyword">open</a> <a id="5987" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6012" class="Keyword">using</a> <a id="6018" class="Symbol">(</a><a id="6019" href="POPL.ConfigNormalization.html#7236" class="Function">strong-normalization-T</a><a id="6041" class="Symbol">;</a> <a id="6043" href="POPL.ConfigNormalization.html#8949" class="Function">normalize-T</a><a id="6054" class="Symbol">;</a> <a id="6056" href="POPL.ConfigNormalization.html#9367" class="Function">canonicity-T</a><a id="6068" class="Symbol">)</a>

<a id="6071" class="Comment">-- §5.4 Lemma (uniqueness of the result)</a>
<a id="6112" class="Keyword">open</a> <a id="6117" href="POPL.ConfigNormalization.html" class="Module">POPL.ConfigNormalization</a> <a id="6142" class="Keyword">using</a> <a id="6148" class="Symbol">(</a><a id="6149" href="POPL.ConfigNormalization.html#9893" class="Function">final-unique</a><a id="6161" class="Symbol">;</a> <a id="6163" href="POPL.ConfigNormalization.html#11328" class="Function">ground-canonicity</a><a id="6180" class="Symbol">)</a>
</pre>
### Instances (§2.2, §5.3)

<pre class="Agda"><a id="6223" class="Comment">-- Writer: theory, free model, affinity, derived rule</a>
<a id="6277" class="Keyword">open</a> <a id="6282" href="POPL.Instances.Writer.html" class="Module">POPL.Instances.Writer</a> <a id="6304" class="Keyword">using</a> <a id="6310" class="Symbol">(</a><a id="6311" href="POPL.Instances.Writer.html#1667" class="Function">writerTheory</a><a id="6323" class="Symbol">;</a> <a id="6325" href="POPL.Instances.Writer.html#2989" class="Function">writerFree</a><a id="6335" class="Symbol">;</a> <a id="6337" href="POPL.Instances.Writer.html#3544" class="Function">writerOM</a><a id="6345" class="Symbol">;</a> <a id="6347" href="POPL.Instances.Writer.html#3846" class="Function">writer-affine</a><a id="6360" class="Symbol">;</a> <a id="6362" href="POPL.Instances.Writer.html#4117" class="Function">writer-effect</a><a id="6375" class="Symbol">)</a>

<a id="6378" class="Comment">-- Errors</a>
<a id="6388" class="Keyword">open</a> <a id="6393" href="POPL.Instances.Errors.html" class="Module">POPL.Instances.Errors</a> <a id="6415" class="Keyword">using</a> <a id="6421" class="Symbol">(</a><a id="6422" href="POPL.Instances.Errors.html#957" class="Function">errTheory</a><a id="6431" class="Symbol">;</a> <a id="6433" href="POPL.Instances.Errors.html#2032" class="Function">errFree</a><a id="6440" class="Symbol">;</a> <a id="6442" href="POPL.Instances.Errors.html#2291" class="Function">errOM</a><a id="6447" class="Symbol">;</a> <a id="6449" href="POPL.Instances.Errors.html#2585" class="Function">err-affine</a><a id="6459" class="Symbol">;</a> <a id="6461" href="POPL.Instances.Errors.html#2910" class="Function">err-effect</a><a id="6471" class="Symbol">)</a>

<a id="6474" class="Comment">-- Boolean state, and the get and set rules</a>
<a id="6518" class="Keyword">open</a> <a id="6523" href="POPL.Instances.State.html" class="Module">POPL.Instances.State</a> <a id="6544" class="Keyword">using</a> <a id="6550" class="Symbol">(</a><a id="6551" href="POPL.Instances.State.html#2503" class="Function">stateTheory</a><a id="6562" class="Symbol">;</a> <a id="6564" href="POPL.Instances.State.html#6038" class="Function">stateFree</a><a id="6573" class="Symbol">;</a> <a id="6575" href="POPL.Instances.State.html#6262" class="Function">stateOM</a><a id="6582" class="Symbol">;</a> <a id="6584" href="POPL.Instances.State.html#6843" class="Function">state-affine</a><a id="6596" class="Symbol">;</a> <a id="6598" href="POPL.Instances.State.html#7922" class="Function">state-get</a><a id="6607" class="Symbol">;</a> <a id="6609" href="POPL.Instances.State.html#8287" class="Function">state-set</a><a id="6618" class="Symbol">)</a>

<a id="6621" class="Comment">-- Weighted monoid</a>
<a id="6640" class="Keyword">open</a> <a id="6645" href="POPL.Instances.WeightedMonoid.html" class="Module">POPL.Instances.WeightedMonoid</a> <a id="6675" class="Keyword">using</a> <a id="6681" class="Symbol">(</a><a id="6682" href="POPL.Instances.WeightedMonoid.html#3428" class="Function">wmTheory</a><a id="6690" class="Symbol">;</a> <a id="6692" href="POPL.Instances.WeightedMonoid.html#11826" class="Function">wmFree</a><a id="6698" class="Symbol">;</a> <a id="6700" href="POPL.Instances.WeightedMonoid.html#13605" class="Function">wmOM</a><a id="6704" class="Symbol">)</a>
<a id="6706" class="Keyword">open</a> <a id="6711" href="POPL.Instances.WeightedMonoidAffine.html" class="Module">POPL.Instances.WeightedMonoidAffine</a> <a id="6747" class="Keyword">using</a> <a id="6753" class="Symbol">(</a><a id="6754" href="POPL.Instances.WeightedMonoidAffine.html#5703" class="Function">wm-affine</a><a id="6763" class="Symbol">)</a>
<a id="6765" class="Keyword">open</a> <a id="6770" href="POPL.Instances.WeightedMonoidRules.html" class="Module">POPL.Instances.WeightedMonoidRules</a> <a id="6805" class="Keyword">using</a> <a id="6811" class="Symbol">(</a><a id="6812" href="POPL.Instances.WeightedMonoidRules.html#2226" class="Function">wm-act</a><a id="6818" class="Symbol">;</a> <a id="6820" href="POPL.Instances.WeightedMonoidRules.html#2765" class="Function">wm-unit</a><a id="6827" class="Symbol">;</a> <a id="6829" href="POPL.Instances.WeightedMonoidRules.html#3077" class="Function">wm-mul</a><a id="6835" class="Symbol">)</a>
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

#### Other deviations

| Tag | Paper | Formalization | Code |
|---|---|---|---|
| D3 | `⟦-⟧` comes from initiality of the CBPV⁺ doctrine (§3.1). | `⟦-⟧` is defined directly by the recursive equations of Fig. 3. The facts initiality would provide are proved by induction: the substitution and plugging lemmas, algebraicity of stacks, and soundness for `≈`. The doctrine itself is not formalized. | [`Denotation.agda`](POPL.Denotation.html), [`DenotationLemmas.agda`](POPL.DenotationLemmas.html), [`EquationalSoundness.agda`](POPL.EquationalSoundness.html) |
| D4 | CBPV⁺ terms are a quotient by the equational theory. | Terms are plain inductive data, and the equational theory is an inductive relation `≈`. CBPV(𝒯) and CBPV⁺(𝒯) share one mode-indexed syntax (`Types.agda`); the grey rules of Fig. 1 exist only in mode `cbpv⁺`. Computations and stacks are separate types rather than one judgement with a stoup. | [`Equational.agda`](POPL.Equational.html), [`Syntax.agda`](POPL.Syntax.html) |
| D5 | Fig. 2 gives a "fragment" of the β/η laws. | The standard full set (Levy). The η laws for `+`, `×` and `0` are in substitution form. F-η is the general stack form `S[M] = x ← M; S[ret x]`. | [`Equational.agda`](POPL.Equational.html) |
| D6 | The logical relations are glued models; the fundamental theorems follow from initiality. | Relations defined by hand by recursion on types, with `𝒞⟦FA⟧` inductive. Fundamental theorems proved by induction on terms. | [`EqLogicalRelation.agda`](POPL.EqLogicalRelation.html), [`OpLogicalRelation.agda`](POPL.OpLogicalRelation.html) |
| D7 | Fig. 6 says "V = σᵢ W", "(V,V')", and so on; these presume the quotient. | The equational predicates are closed under `≈` by construction: `𝒱⟦A+A'⟧ V` asks for `V ≈ σᵢ W`, and `𝒞⟦FA⟧` has a `conv` clause. This follows from D4. | [`EqLogicalRelation.agda`](POPL.EqLogicalRelation.html) |
| D9 | Strong normalization (§4.3 for `↦tree`, §5.4 for `↦T`) is proved by a classical argument on infinite sequences. | Stated constructively as accessibility (`Acc`) for converse reduction, and derived from the decreasing metric. | [`TreeNormalization.agda`](POPL.TreeNormalization.html), [`ConfigNormalization.agda`](POPL.ConfigNormalization.html) |
| D10 | The Effect rule is written in substitution notation: `⟨s, γ, S[op M⃗]/xᵢ⟩ ↦T T(γ ⊎ S[M⃗])(T(ρ)(s ∘ᵢ op))`. | As requested, the derivative form from the appendix: `C⟪S[op M⃗]⟫ ↦T μ((∂η C)⟪⟦op⟧(η(S[M⃗]))⟫)`. Affinity is stated through the generic step `step(s,i,op) = μ(∂(η∘σ₁)(Cₛⁱ)⟪T(σ₂)⌈op⌉⟫)`, whose shape is `s ∘ᵢ op` and whose positions are `ρ`. The appendix's "Simplification" lemma, `effect-via-step`, shows that the derivative form equals the paper's form. | [`ConfigReduction.agda`](POPL.ConfigReduction.html) |
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
