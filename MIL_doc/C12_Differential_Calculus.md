<span id="differential-calculus"></span><span id="id1"></span>

# <span class="section-number">12. </span>Differential Calculus<a href="#index-0" class="headerlink" title="Link to this heading"></a>

We now consider the formalization of notions from *analysis*, starting with differentiation in this chapter and turning integration and measure theory in the next. In <a href="#elementary-differential-calculus" class="reference internal"><span class="std std-numref">Section 12.1</span></a>, we stick with the setting of functions from the real numbers to the real numbers, which is familiar from any introductory calculus class. In <a href="#normed-spaces" class="reference internal"><span class="std std-numref">Section 12.2</span></a>, we then consider the notion of a derivative in a much broader setting.

<span id="index-1"></span><span id="id2"></span>

## <span class="section-number">12.1. </span>Elementary Differential Calculus<a href="#elementary-differential-calculus" class="headerlink" title="Link to this heading"></a>

Let <span class="pre">`f`</span> be a function from the reals to the reals. There is a difference between talking about the derivative of <span class="pre">`f`</span> at a single point and talking about the derivative function. In Mathlib, the first notion is represented as follows.

    open Real

    /-- The sin function has derivative 1 at 0. -/
    example : HasDerivAt sin 1 0 := by simpa using hasDerivAt_sin 0

We can also express that <span class="pre">`f`</span> is differentiable at a point without specifying its derivative there by writing <span class="pre">`DifferentiableAt`</span>` `<span class="pre">`ℝ`</span>. We specify <span class="pre">`ℝ`</span> explicitly because in a slightly more general context, when talking about functions from <span class="pre">`ℂ`</span> to <span class="pre">`ℂ`</span>, we want to be able to distinguish between being differentiable in the real sense and being differentiable in the sense of the complex derivative.

    example (x : ℝ) : DifferentiableAt ℝ sin x :=
      (hasDerivAt_sin x).differentiableAt

It would be inconvenient to have to provide a proof of differentiability every time we want to refer to a derivative. So Mathlib provides a function <span class="pre">`deriv`</span>` `<span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> that is defined for any function <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> but is defined to take the value <span class="pre">`0`</span> at any point where <span class="pre">`f`</span> is not differentiable.

    example {f : ℝ → ℝ} {x a : ℝ} (h : HasDerivAt f a x) : deriv f x = a :=
      h.deriv

    example {f : ℝ → ℝ} {x : ℝ} (h : ¬DifferentiableAt ℝ f x) : deriv f x = 0 :=
      deriv_zero_of_not_differentiableAt h

Of course there are many lemmas about <span class="pre">`deriv`</span> that do require differentiability assumptions. For instance, you should think about a counterexample to the next lemma without the differentiability assumptions.

    example {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
        deriv (f + g) x = deriv f x + deriv g x :=
      deriv_add hf hg

Interestingly, however, there are statements that can avoid differentiability assumptions by taking advantage of the fact that the value of <span class="pre">`deriv`</span> defaults to zero when the function is not differentiable. So making sense of the following statement requires knowing the precise definition of <span class="pre">`deriv`</span>.

    example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
      h.deriv_eq_zero

We can even state Rolle’s theorem without any differentiability assumptions, which seems even weirder.

    open Set

    example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
        ∃ c ∈ Ioo a b, deriv f c = 0 :=
      exists_deriv_eq_zero hab hfc hfI

Of course, this trick does not work for the general mean value theorem.

    example (f : ℝ → ℝ) {a b : ℝ} (hab : a < b) (hf : ContinuousOn f (Icc a b))
        (hf' : DifferentiableOn ℝ f (Ioo a b)) : ∃ c ∈ Ioo a b, deriv f c = (f b - f a) / (b - a) :=
      exists_deriv_eq_slope f hab hf hf'

Lean can automatically compute some simple derivatives using the <span class="pre">`simp`</span> tactic.

    example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

    example : deriv sin π = -1 := by simp

<span id="normed-spaces"></span><span id="index-2"></span>

## <span class="section-number">12.2. </span>Differential Calculus in Normed Spaces<a href="#differential-calculus-in-normed-spaces" class="headerlink" title="Link to this heading"></a>

### <span class="section-number">12.2.1. </span>Normed spaces<a href="#id3" class="headerlink" title="Link to this heading"></a>

Differentiation can be generalized beyond <span class="pre">`ℝ`</span> using the notion of a *normed vector space*, which encapsulates both direction and distance. We start with the notion of a *normed group*, which is an additive commutative group equipped with a real-valued norm function satisfying the following conditions.

    variable {E : Type*} [NormedAddCommGroup E]

    example (x : E) : 0 ≤ ‖x‖ :=
      norm_nonneg x

    example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
      norm_eq_zero

    example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
      norm_add_le x y

Every normed space is a metric space with distance function <span class="math notranslate nohighlight">\\d(x, y) = \\ x - y \\\\</span>, and hence it is also a topological space. Lean and Mathlib know this.

    example : MetricSpace E := by infer_instance

    example {X : Type*} [TopologicalSpace X] {f : X → E} (hf : Continuous f) :
        Continuous fun x ↦ ‖f x‖ :=
      hf.norm

In order to use the notion of a norm with concepts from linear algebra, we add the assumption <span class="pre">`NormedSpace`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`E`</span> on top of <span class="pre">`NormedAddGroup`</span>` `<span class="pre">`E`</span>. This stipulates that <span class="pre">`E`</span> is a vector space over <span class="pre">`ℝ`</span> and that scalar multiplication satisfies the following condition.

    variable [NormedSpace ℝ E]

    example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
      norm_smul a x

A complete normed space is known as a *Banach space*. Every finite-dimensional vector space is complete.

    example [FiniteDimensional ℝ E] : CompleteSpace E := by infer_instance

In all the previous examples, we used the real numbers as the base field. More generally, we can make sense of calculus with a vector space over any *nontrivially normed field*. These are fields that are equipped with a real-valued norm that is multiplicative and has the property that not every element has norm zero or one (equivalently, there is an element whose norm is bigger than one).

    example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (x y : 𝕜) : ‖x * y‖ = ‖x‖ * ‖y‖ :=
      norm_mul x y

    example (𝕜 : Type*) [NontriviallyNormedField 𝕜] : ∃ x : 𝕜, 1 < ‖x‖ :=
      NormedField.exists_one_lt_norm 𝕜

A finite-dimensional vector space over a nontrivially normed field is complete as long as the field itself is complete.

    example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
        [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
      FiniteDimensional.complete 𝕜 E

### <span class="section-number">12.2.2. </span>Continuous linear maps<a href="#continuous-linear-maps" class="headerlink" title="Link to this heading"></a>

We now turn to the morphisms in the category of normed spaces, namely, continuous linear maps. In Mathlib, the type of <span class="pre">`𝕜`</span>-linear continuous maps between normed spaces <span class="pre">`E`</span> and <span class="pre">`F`</span> is written <span class="pre">`E`</span>` `<span class="pre">`→L[𝕜]`</span>` `<span class="pre">`F`</span>. They are implemented as *bundled maps*, which means that an element of this type a structure that that includes the function itself and the properties of being linear and continuous. Lean will insert a coercion so that a continuous linear map can be treated as a function.

    variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
      [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

    example : E →L[𝕜] E :=
      ContinuousLinearMap.id 𝕜 E

    example (f : E →L[𝕜] F) : E → F :=
      f

    example (f : E →L[𝕜] F) : Continuous f :=
      f.cont

    example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
      f.map_add x y

    example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
      f.map_smul a x

Continuous linear maps have an operator norm that is characterized by the following properties.

    variable (f : E →L[𝕜] F)

    example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
      f.le_opNorm x

    example {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
      f.opNorm_le_bound hMp hM

There is also a notion of bundled continuous linear *isomorphism*. Their type of such isomorphisms is <span class="pre">`E`</span>` `<span class="pre">`≃L[𝕜]`</span>` `<span class="pre">`F`</span>.

As a challenging exercise, you can prove the Banach-Steinhaus theorem, also known as the Uniform Boundedness Principle. The principle states that a family of continuous linear maps from a Banach space into a normed space is pointwise bounded, then the norms of these linear maps are uniformly bounded. The main ingredient is Baire’s theorem <span class="pre">`nonempty_interior_of_iUnion_of_closed`</span>. (You proved a version of this in the topology chapter.) Minor ingredients include <span class="pre">`continuous_linear_map.opNorm_le_of_shell`</span>, <span class="pre">`interior_subset`</span> and <span class="pre">`interior_iInter_subset`</span> and <span class="pre">`isClosed_le`</span>.

    variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
      [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

    open Metric

    example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
        ∃ C', ∀ i, ‖g i‖ ≤ C' := by
      -- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n`
      let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
      -- each of these sets is closed
      have hc : ∀ n : ℕ, IsClosed (e n)
      sorry
      -- the union is the entire space; this is where we use `h`
      have hU : (⋃ n : ℕ, e n) = univ
      sorry
      /- apply the Baire category theorem to conclude that for some `m : ℕ`,
           `e m` contains some `x` -/
      obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry
      obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry
      obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry
      -- show all elements in the ball have norm bounded by `m` after applying any `g i`
      have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m
      sorry
      have εk_pos : 0 < ε / ‖k‖ := sorry
      refine ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.opNorm_le_of_shell ε_pos ?_ hk ?_⟩
      sorry
      sorry

### <span class="section-number">12.2.3. </span>Asymptotic comparisons<a href="#asymptotic-comparisons" class="headerlink" title="Link to this heading"></a>

Defining differentiability also requires asymptotic comparisons. Mathlib has an extensive library covering the big O and little o relations, whose definitions are shown below. Opening the <span class="pre">`asymptotics`</span> locale allows us to use the corresponding notation. Here we will only use little o to define differentiability.

    open Asymptotics

    example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F] (c : ℝ)
        (l : Filter α) (f : α → E) (g : α → F) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
      isBigOWith_iff

    example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
        (l : Filter α) (f : α → E) (g : α → F) : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
      isBigO_iff_isBigOWith

    example {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
        (l : Filter α) (f : α → E) (g : α → F) : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
      isLittleO_iff_forall_isBigOWith

    example {α : Type*} {E : Type*} [NormedAddCommGroup E] (l : Filter α) (f g : α → E) :
        f ~[l] g ↔ (f - g) =o[l] g :=
      Iff.rfl

### <span class="section-number">12.2.4. </span>Differentiability<a href="#differentiability" class="headerlink" title="Link to this heading"></a>

We are now ready to discuss differentiable functions between normed spaces. In analogy the elementary one-dimensional, Mathlib defines a predicate <span class="pre">`HasFDerivAt`</span> and a function <span class="pre">`fderiv`</span>. Here the letter “f” stands for *Fréchet*.

    open Topology

    variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
      [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

    example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
        HasFDerivAt f f' x₀ ↔ (fun x ↦ f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] fun x ↦ x - x₀ :=
      hasFDerivAtFilter_iff_isLittleO ..

    example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) : fderiv 𝕜 f x₀ = f' :=
      hff'.fderiv

We also have iterated derivatives that take values in the type of multilinear maps <span class="pre">`E`</span>` `<span class="pre">`[×n]→L[𝕜]`</span>` `<span class="pre">`F`</span>, and we have continuously differential functions. The type <span class="pre">`ℕ∞`</span> is <span class="pre">`ℕ`</span> with an additional element <span class="pre">`∞`</span> that is bigger than every natural number. So <span class="math notranslate nohighlight">\\\mathcal{C}^\infty\\</span> functions are functions <span class="pre">`f`</span> that satisfy <span class="pre">`ContDiff`</span>` `<span class="pre">`𝕜`</span>` `<span class="pre">`⊤`</span>` `<span class="pre">`f`</span>.

    example (n : ℕ) (f : E → F) : E → E[×n]→L[𝕜] F :=
      iteratedFDeriv 𝕜 n f

    example (n : ℕ∞) {f : E → F} :
        ContDiff 𝕜 n f ↔
          (∀ m : ℕ, (m : WithTop ℕ) ≤ n → Continuous fun x ↦ iteratedFDeriv 𝕜 m f x) ∧
            ∀ m : ℕ, (m : WithTop ℕ) < n → Differentiable 𝕜 fun x ↦ iteratedFDeriv 𝕜 m f x :=
      contDiff_iff_continuous_differentiable

The differentiability parameter in <span class="pre">`ContDiff`</span> can also take value <span class="pre">`ω`</span>` `<span class="pre">`:`</span>` `<span class="pre">`WithTop`</span>` `<span class="pre">`ℕ∞`</span> to denote analytic functions.

There is a stricter notion of differentiability called <span class="pre">`HasStrictFDerivAt`</span>, which is used in the statement of the inverse function theorem and the statement of the implicit function theorem, both of which are in Mathlib. Over <span class="pre">`ℝ`</span> or <span class="pre">`ℂ`</span>, continuously differentiable functions are strictly differentiable.

    example {𝕂 : Type*} [RCLike 𝕂] {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕂 E] {F : Type*}
        [NormedAddCommGroup F] [NormedSpace 𝕂 F] {f : E → F} {x : E} {n : WithTop ℕ∞}
        (hf : ContDiffAt 𝕂 n f x) (hn : 1 ≤ n) : HasStrictFDerivAt f (fderiv 𝕂 f x) x :=
      hf.hasStrictFDerivAt hn

The local inverse theorem is stated using an operation that produces an inverse function from a function and the assumptions that the function is strictly differentiable at a point <span class="pre">`a`</span> and that its derivative is an isomorphism.

The first example below gets this local inverse. The next one states that it is indeed a local inverse from the left and from the right, and that it is strictly differentiable.

    section LocalInverse
    variable [CompleteSpace E] {f : E → F} {f' : E ≃L[𝕜] F} {a : E}

    example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) : F → E :=
      HasStrictFDerivAt.localInverse f f' a hf

    example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
        ∀ᶠ x in 𝓝 a, hf.localInverse f f' a (f x) = x :=
      hf.eventually_left_inverse

    example (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
        ∀ᶠ x in 𝓝 (f a), f (hf.localInverse f f' a x) = x :=
      hf.eventually_right_inverse

    example {f : E → F} {f' : E ≃L[𝕜] F} {a : E}
      (hf : HasStrictFDerivAt f (f' : E →L[𝕜] F) a) :
        HasStrictFDerivAt (HasStrictFDerivAt.localInverse f f' a hf) (f'.symm : F →L[𝕜] E) (f a) :=
      HasStrictFDerivAt.to_localInverse hf

    end LocalInverse

This has been only a quick tour of the differential calculus in Mathlib. The library contains many variations that we have not discussed. For example, you may want to use one-sided derivatives in the one-dimensional setting. The means to do so are found in Mathlib in a more general context; see <span class="pre">`HasFDerivWithinAt`</span> or the even more general <span class="pre">`HasFDerivAtFilter`</span>.
