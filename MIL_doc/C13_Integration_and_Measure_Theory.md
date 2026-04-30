<span id="integration-and-measure-theory"></span><span id="id1"></span>

# <span class="section-number">13. </span>Integration and Measure Theory<a href="#index-0" class="headerlink" title="Link to this heading"></a>

<span id="index-1"></span><span id="id2"></span>

## <span class="section-number">13.1. </span>Elementary Integration<a href="#elementary-integration" class="headerlink" title="Link to this heading"></a>

We first focus on integration of functions on finite intervals in <span class="pre">`ℝ`</span>. We can integrate elementary functions.

    open MeasureTheory intervalIntegral

    open Interval
    -- this introduces the notation `[[a, b]]` for the segment from `min a b` to `max a b`

    example (a b : ℝ) : (∫ x in a..b, x) = (b ^ 2 - a ^ 2) / 2 :=
      integral_id

    example {a b : ℝ} (h : (0 : ℝ) ∉ [[a, b]]) : (∫ x in a..b, 1 / x) = Real.log (b / a) :=
      integral_one_div h

The fundamental theorem of calculus relates integration and differentiation. Below we give simplified statements of the two parts of this theorem. The first part says that integration provides an inverse to differentiation and the second one specifies how to compute integrals of derivatives. (These two parts are very closely related, but their optimal versions, which are not shown here, are not equivalent.)

    example (f : ℝ → ℝ) (hf : Continuous f) (a b : ℝ) : deriv (fun u ↦ ∫ x : ℝ in a..u, f x) b = f b :=
      (integral_hasStrictDerivAt_right (hf.intervalIntegrable _ _) (hf.stronglyMeasurableAtFilter _ _)
            hf.continuousAt).hasDerivAt.deriv

    example {f : ℝ → ℝ} {a b : ℝ} {f' : ℝ → ℝ} (h : ∀ x ∈ [[a, b]], HasDerivAt f (f' x) x)
        (h' : IntervalIntegrable f' volume a b) : (∫ y in a..b, f' y) = f b - f a :=
      integral_eq_sub_of_hasDerivAt h h'

Convolution is also defined in Mathlib and its basic properties are proved.

    open Convolution

    example (f : ℝ → ℝ) (g : ℝ → ℝ) : f ⋆ g = fun x ↦ ∫ t, f t * g (x - t) :=
      rfl

<span id="index-2"></span><span id="id3"></span>

## <span class="section-number">13.2. </span>Measure Theory<a href="#measure-theory" class="headerlink" title="Link to this heading"></a>

The general context for integration in Mathlib is measure theory. Even the elementary integrals of the previous section are in fact Bochner integrals. Bochner integration is a generalization of Lebesgue integration where the target space can be any Banach space, not necessarily finite dimensional.

The first component in the development of measure theory is the notion of a <span class="math notranslate nohighlight">\\\sigma\\</span>-algebra of sets, which are called the *measurable* sets. The type class <span class="pre">`MeasurableSpace`</span> serves to equip a type with such a structure. The sets <span class="pre">`empty`</span> and <span class="pre">`univ`</span> are measurable, the complement of a measurable set is measurable, and a countable union or intersection of measurable sets is measurable. Note that these axioms are redundant; if you <span class="pre">`#print`</span>` `<span class="pre">`MeasurableSpace`</span>, you will see the ones that Mathlib uses. As the examples below show, countability assumptions can be expressed using the <span class="pre">`Encodable`</span> type class.

    variable {α : Type*} [MeasurableSpace α]

    example : MeasurableSet (∅ : Set α) :=
      MeasurableSet.empty

    example : MeasurableSet (univ : Set α) :=
      MeasurableSet.univ

    example {s : Set α} (hs : MeasurableSet s) : MeasurableSet (sᶜ) :=
      hs.compl

    example : Encodable ℕ := by infer_instance

    example (n : ℕ) : Encodable (Fin n) := by infer_instance

    variable {ι : Type*} [Encodable ι]

    example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋃ b, f b) :=
      MeasurableSet.iUnion h

    example {f : ι → Set α} (h : ∀ b, MeasurableSet (f b)) : MeasurableSet (⋂ b, f b) :=
      MeasurableSet.iInter h

Once a type is measurable, we can measure it. On paper, a measure on a set (or type) equipped with a <span class="math notranslate nohighlight">\\\sigma\\</span>-algebra is a function from the measurable sets to the extended non-negative reals that is additive on countable disjoint unions. In Mathlib, we don’t want to carry around measurability assumptions every time we write an application of the measure to a set. So we extend the measure to any set <span class="pre">`s`</span> as the infimum of measures of measurable sets containing <span class="pre">`s`</span>. Of course, many lemmas still require measurability assumptions, but not all.

    open MeasureTheory Function
    variable {μ : Measure α}

    example (s : Set α) : μ s = ⨅ (t : Set α) (_ : s ⊆ t) (_ : MeasurableSet t), μ t :=
      measure_eq_iInf s

    example (s : ι → Set α) : μ (⋃ i, s i) ≤ ∑' i, μ (s i) :=
      measure_iUnion_le s

    example {f : ℕ → Set α} (hmeas : ∀ i, MeasurableSet (f i)) (hdis : Pairwise (Disjoint on f)) :
        μ (⋃ i, f i) = ∑' i, μ (f i) :=
      μ.m_iUnion hmeas hdis

Once a type has a measure associated with it, we say that a property <span class="pre">`P`</span> holds *almost everywhere* if the set of elements where the property fails has measure 0. The collection of properties that hold almost everywhere form a filter, but Mathlib introduces special notation for saying that a property holds almost everywhere.

    example {P : α → Prop} : (∀ᵐ x ∂μ, P x) ↔ ∀ᶠ x in ae μ, P x :=
      Iff.rfl

<span id="id4"></span>

## <span class="section-number">13.3. </span>Integration<a href="#integration" class="headerlink" title="Link to this heading"></a>

Now that we have measurable spaces and measures we can consider integrals. As explained above, Mathlib uses a very general notion of integration that allows any Banach space as the target. As usual, we don’t want our notation to carry around assumptions, so we define integration in such a way that an integral is equal to zero if the function in question is not integrable. Most lemmas having to do with integrals have integrability assumptions.

    section
    variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] {f : α → E}

    example {f g : α → E} (hf : Integrable f μ) (hg : Integrable g μ) :
        ∫ a, f a + g a ∂μ = ∫ a, f a ∂μ + ∫ a, g a ∂μ :=
      integral_add hf hg

As an example of the complex interactions between our various conventions, let us see how to integrate constant functions. Recall that a measure <span class="pre">`μ`</span> takes values in <span class="pre">`ℝ≥0∞`</span>, the type of extended non-negative reals. There is a function <span class="pre">`ENNReal.toReal`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ≥0∞`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> which sends <span class="pre">`⊤`</span>, the point at infinity, to zero. For any <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`α`</span>, if <span class="pre">`μ`</span>` `<span class="pre">`s`</span>` `<span class="pre">`=`</span>` `<span class="pre">`⊤`</span>, then nonzero constant functions are not integrable on <span class="pre">`s`</span>. In that case, their integrals are equal to zero by definition, as is <span class="pre">`(μ`</span>` `<span class="pre">`s).toReal`</span>. So in all cases we have the following lemma.

    example {s : Set α} (c : E) : ∫ x in s, c ∂μ = (μ s).toReal • c :=
      setIntegral_const c

We now quickly explain how to access the most important theorems in integration theory, starting with the dominated convergence theorem. There are several versions in Mathlib, and here we only show the most basic one.

    open Filter

    example {F : ℕ → α → E} {f : α → E} (bound : α → ℝ) (hmeas : ∀ n, AEStronglyMeasurable (F n) μ)
        (hint : Integrable bound μ) (hbound : ∀ n, ∀ᵐ a ∂μ, ‖F n a‖ ≤ bound a)
        (hlim : ∀ᵐ a ∂μ, Tendsto (fun n : ℕ ↦ F n a) atTop (𝓝 (f a))) :
        Tendsto (fun n ↦ ∫ a, F n a ∂μ) atTop (𝓝 (∫ a, f a ∂μ)) :=
      tendsto_integral_of_dominated_convergence bound hmeas hint hbound hlim

Then we have Fubini’s theorem for integrals on product type.

    example {α : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ] {β : Type*}
        [MeasurableSpace β] {ν : Measure β} [SigmaFinite ν] (f : α × β → E)
        (hf : Integrable f (μ.prod ν)) : ∫ z, f z ∂ μ.prod ν = ∫ x, ∫ y, f (x, y) ∂ν ∂μ :=
      integral_prod f hf

There is a very general version of convolution that applies to any continuous bilinear form.

    open Convolution

    variable {𝕜 : Type*} {G : Type*} {E : Type*} {E' : Type*} {F : Type*} [NormedAddCommGroup E]
      [NormedAddCommGroup E'] [NormedAddCommGroup F] [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E]
      [NormedSpace 𝕜 E'] [NormedSpace 𝕜 F] [MeasurableSpace G] [NormedSpace ℝ F] [CompleteSpace F]
      [Sub G]

    example (f : G → E) (g : G → E') (L : E →L[𝕜] E' →L[𝕜] F) (μ : Measure G) :
        f ⋆[L, μ] g = fun x ↦ ∫ t, L (f t) (g (x - t)) ∂μ :=
      rfl

Finally, Mathlib has a very general version of the change-of-variables formula. In the statement below, <span class="pre">`BorelSpace`</span>` `<span class="pre">`E`</span> means the <span class="math notranslate nohighlight">\\\sigma\\</span>-algebra on <span class="pre">`E`</span> is generated by the open sets of <span class="pre">`E`</span>, and <span class="pre">`IsAddHaarMeasure`</span>` `<span class="pre">`μ`</span> means that the measure <span class="pre">`μ`</span> is left-invariant, gives finite mass to compact sets, and give positive mass to open sets.

    example {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
        [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {F : Type*}
        [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] {s : Set E} {f : E → E}
        {f' : E → E →L[ℝ] E} (hs : MeasurableSet s)
        (hf : ∀ x : E, x ∈ s → HasFDerivWithinAt f (f' x) s x) (h_inj : InjOn f s) (g : E → F) :
        ∫ x in f '' s, g x ∂μ = ∫ x in s, |(f' x).det| • g (f x) ∂μ :=
      integral_image_eq_integral_abs_det_fderiv_smul μ hs hf h_inj g
