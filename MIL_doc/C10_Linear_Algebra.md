<span id="id1"></span>

# <span class="section-number">10. </span>Linear algebra<a href="#linear-algebra" class="headerlink" title="Link to this heading"></a>

## <span class="section-number">10.1. </span>Vector spaces and linear maps<a href="#vector-spaces-and-linear-maps" class="headerlink" title="Link to this heading"></a>

### <span class="section-number">10.1.1. </span>Vector spaces<a href="#vector-spaces" class="headerlink" title="Link to this heading"></a>

We will start directly abstract linear algebra, taking place in a vector space over any field. However you can find information about matrices in <a href="#matrices" class="reference internal"><span class="std std-numref">Section 10.4.1</span></a> which does not logically depend on this abstract theory. Mathlib actually deals with a more general version of linear algebra involving the word module, but for now we will pretend this is only an eccentric spelling habit.

The way to say “let <span class="math notranslate nohighlight">\\K\\</span> be a field and let <span class="math notranslate nohighlight">\\V\\</span> be a vector space over <span class="math notranslate nohighlight">\\K\\</span>” (and make them implicit arguments to later results) is:

    variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

We explained in <a href="C08_Hierarchies.html#hierarchies" class="reference internal"><span class="std std-numref">Chapter 8</span></a> why we need two separate typeclasses <span class="pre">`[AddCommGroup`</span>` `<span class="pre">`V]`</span>` `<span class="pre">`[Module`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V]`</span>. The short version is the following. Mathematically we want to say that having a <span class="math notranslate nohighlight">\\K\\</span>-vector space structure implies having an additive commutative group structure. We could tell this to Lean. But then whenever Lean would need to find such a group structure on a type <span class="math notranslate nohighlight">\\V\\</span>, it would go hunting for vector space structures using a *completely unspecified* field <span class="math notranslate nohighlight">\\K\\</span> that cannot be inferred from <span class="math notranslate nohighlight">\\V\\</span>. This would be very bad for the type class synthesis system.

The multiplication of a vector v by a scalar a is denoted by a • v. We list a couple of algebraic rules about the interaction of this operation with addition in the following examples. Of course simp or apply? would find those proofs. There is also a module tactic that solves goals following from the axioms of vector spaces and fields, in the same way the ring tactic is used in commutative rings or the group tactic is used in groups. But it is still useful to remember that scalar multiplication is abbreviated smul in lemma names.

    example (a : K) (u v : V) : a • (u + v) = a • u + a • v :=
      smul_add a u v

    example (a b : K) (u : V) : (a + b) • u = a • u + b • u :=
      add_smul a b u

    example (a b : K) (u : V) : a • b • u = b • a • u :=
      smul_comm a b u

As a quick note for more advanced readers, let us point out that, as suggested by terminology, Mathlib’s linear algebra also covers modules over (not necessarily commutative) rings. In fact it even covers semi-modules over semi-rings. If you think you do not need this level of generality, you can meditate the following example that nicely captures a lot of algebraic rules about ideals acting on submodules:

    example {R M : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] :
        Module (Ideal R) (Submodule R M) :=
      inferInstance

### <span class="section-number">10.1.2. </span>Linear maps<a href="#linear-maps" class="headerlink" title="Link to this heading"></a>

Next we need linear maps. Like group morphisms, linear maps in Mathlib are bundled maps, i.e. packages made of a map and proofs of its linearity properties. Those bundled maps are converted to ordinary functions when applied. See <a href="C08_Hierarchies.html#hierarchies" class="reference internal"><span class="std std-numref">Chapter 8</span></a> for more information about this design.

The type of linear maps between two <span class="pre">`K`</span>-vector spaces <span class="pre">`V`</span> and <span class="pre">`W`</span> is denoted by <span class="pre">`V`</span>` `<span class="pre">`→ₗ[K]`</span>` `<span class="pre">`W`</span>. The subscript l stands for linear. At first it may feel odd to specify <span class="pre">`K`</span> in this notation. But this is crucial when several fields come into play. For instance real-linear maps from <span class="math notranslate nohighlight">\\ℂ\\</span> to <span class="math notranslate nohighlight">\\ℂ\\</span> are every map <span class="math notranslate nohighlight">\\z ↦ az + b\bar{z}\\</span> while only the maps <span class="math notranslate nohighlight">\\z ↦ az\\</span> are complex linear, and this difference is crucial in complex analysis.

    variable {W : Type*} [AddCommGroup W] [Module K W]

    variable (φ : V →ₗ[K] W)

    example (a : K) (v : V) : φ (a • v) = a • φ v :=
      map_smul φ a v

    example (v w : V) : φ (v + w) = φ v + φ w :=
      map_add φ v w

Note that <span class="pre">`V`</span>` `<span class="pre">`→ₗ[K]`</span>` `<span class="pre">`W`</span> itself carries interesting algebraic structures (this is part of the motivation for bundling those maps). It is a <span class="pre">`K`</span>-vector space so we can add linear maps and multiply them by scalars.

    variable (ψ : V →ₗ[K] W)

    #check (2 • φ + ψ : V →ₗ[K] W)

One downside of using bundled maps is that we cannot use ordinary function composition. We need to use <span class="pre">`LinearMap.comp`</span> or the notation <span class="pre">`∘ₗ`</span>.

    variable (θ : W →ₗ[K] V)

    #check (φ.comp θ : W →ₗ[K] W)
    #check (φ ∘ₗ θ : W →ₗ[K] W)

There are two main ways to construct linear maps. First we can build the structure by providing the function and the linearity proof. As usual, this is facilitated by the structure code action: you can type <span class="pre">`example`</span>` `<span class="pre">`:`</span>` `<span class="pre">`V`</span>` `<span class="pre">`→ₗ[K]`</span>` `<span class="pre">`V`</span>` `<span class="pre">`:=`</span>` `<span class="pre">`_`</span> and use the code action “Generate a skeleton” attached to the underscore.

    example : V →ₗ[K] V where
      toFun v := 3 • v
      map_add' _ _ := smul_add ..
      map_smul' _ _ := smul_comm ..

You may wonder why the proof fields of <span class="pre">`LinearMap`</span> have names ending with a prime. This is because they are defined before the coercion to functions is defined, hence they are phrased in terms of <span class="pre">`LinearMap.toFun`</span>. Then they are restated as <span class="pre">`LinearMap.map_add`</span> and <span class="pre">`LinearMap.map_smul`</span> in terms of the coercion to function. This is not yet the end of the story. One also wants a version of <span class="pre">`map_add`</span> that applies to any (bundled) map preserving addition, such as additive group morphisms, linear maps, continuous linear maps, <span class="pre">`K`</span>-algebra maps etc… This one is <span class="pre">`map_add`</span> (in the root namespace). The intermediate version, <span class="pre">`LinearMap.map_add`</span> is a bit redundant but allows to use dot notation, which can be nice sometimes. A similar story exists for <span class="pre">`map_smul`</span>, and the general framework is explained in <a href="C08_Hierarchies.html#hierarchies" class="reference internal"><span class="std std-numref">Chapter 8</span></a>.

    #check (φ.map_add' : ∀ x y : V, φ.toFun (x + y) = φ.toFun x + φ.toFun y)
    #check (φ.map_add : ∀ x y : V, φ (x + y) = φ x + φ y)
    #check (map_add φ : ∀ x y : V, φ (x + y) = φ x + φ y)

One can also build linear maps from the ones that are already defined in Mathlib using various combinators. For instance the above example is already known as <span class="pre">`LinearMap.lsmul`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span>` `<span class="pre">`3`</span>. There are several reason why <span class="pre">`K`</span> and <span class="pre">`V`</span> are explicit arguments here. The most pressing one is that from a bare <span class="pre">`LinearMap.lsmul`</span>` `<span class="pre">`3`</span> there would be no way for Lean to infer <span class="pre">`V`</span> or even <span class="pre">`K`</span>. But also <span class="pre">`LinearMap.lsmul`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span> is an interesting object by itself: it has type <span class="pre">`K`</span>` `<span class="pre">`→ₗ[K]`</span>` `<span class="pre">`V`</span>` `<span class="pre">`→ₗ[K]`</span>` `<span class="pre">`V`</span>, meaning it is a <span class="pre">`K`</span>-linear map from <span class="pre">`K`</span> —seen as a vector space over itself— to the space of <span class="pre">`K`</span>-linear maps from <span class="pre">`V`</span> to <span class="pre">`V`</span>.

    #check (LinearMap.lsmul K V 3 : V →ₗ[K] V)
    #check (LinearMap.lsmul K V : K →ₗ[K] V →ₗ[K] V)

There is also a type <span class="pre">`LinearEquiv`</span> of linear isomorphisms denoted by <span class="pre">`V`</span>` `<span class="pre">`≃ₗ[K]`</span>` `<span class="pre">`W`</span>. The inverse of <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`V`</span>` `<span class="pre">`≃ₗ[K]`</span>` `<span class="pre">`W`</span> is <span class="pre">`f.symm`</span>` `<span class="pre">`:`</span>` `<span class="pre">`W`</span>` `<span class="pre">`≃ₗ[K]`</span>` `<span class="pre">`V`</span>, composition of <span class="pre">`f`</span> and <span class="pre">`g`</span> is <span class="pre">`f.trans`</span>` `<span class="pre">`g`</span> also denoted by <span class="pre">`f`</span>` `<span class="pre">`≪≫ₗ`</span>` `<span class="pre">`g`</span>, and the identity isomorphism of <span class="pre">`V`</span> is <span class="pre">`LinearEquiv.refl`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span>. Elements of this type are automatically coerced to morphisms and functions when necessary.

    example (f : V ≃ₗ[K] W) : f ≪≫ₗ f.symm = LinearEquiv.refl K V :=
      f.self_trans_symm

One can use <span class="pre">`LinearEquiv.ofBijective`</span> to build an isomorphism from a bijective morphism. Doing so makes the inverse function noncomputable.

    noncomputable example (f : V →ₗ[K] W) (h : Function.Bijective f) : V ≃ₗ[K] W :=
      .ofBijective f h

Note that in the above example, Lean uses the announced type to understand that <span class="pre">`.ofBijective`</span> refers to <span class="pre">`LinearEquiv.ofBijective`</span> (without needing to open any namespace).

### <span class="section-number">10.1.3. </span>Sums and products of vector spaces<a href="#sums-and-products-of-vector-spaces" class="headerlink" title="Link to this heading"></a>

We can build new vector spaces out of old ones using direct sums and direct products. Let us start with two vectors spaces. In this case there is no difference between sum and product, and we can simply use the product type. In the following snippet of code we simply show how to get all the structure maps (inclusions and projections) as linear maps, as well as the universal properties constructing linear maps into products and out of sums (if you are not familiar with the category-theoretic distinction between sums and products, you can simply ignore the universal property vocabulary and focus on the types of the following examples).

    section binary_product

    variable {W : Type*} [AddCommGroup W] [Module K W]
    variable {U : Type*} [AddCommGroup U] [Module K U]
    variable {T : Type*} [AddCommGroup T] [Module K T]

    -- First projection map
    example : V × W →ₗ[K] V := LinearMap.fst K V W

    -- Second projection map
    example : V × W →ₗ[K] W := LinearMap.snd K V W

    -- Universal property of the product
    example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : U →ₗ[K]  V × W := LinearMap.prod φ ψ

    -- The product map does the expected thing, first component
    example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.fst K V W ∘ₗ LinearMap.prod φ ψ = φ := rfl

    -- The product map does the expected thing, second component
    example (φ : U →ₗ[K] V) (ψ : U →ₗ[K] W) : LinearMap.snd K V W ∘ₗ LinearMap.prod φ ψ = ψ := rfl

    -- We can also combine maps in parallel
    example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) : (V × W) →ₗ[K] (U × T) := φ.prodMap ψ

    -- This is simply done by combining the projections with the universal property
    example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] T) :
      φ.prodMap ψ = (φ ∘ₗ .fst K V W).prod (ψ ∘ₗ .snd K V W) := rfl

    -- First inclusion map
    example : V →ₗ[K] V × W := LinearMap.inl K V W

    -- Second inclusion map
    example : W →ₗ[K] V × W := LinearMap.inr K V W

    -- Universal property of the sum (aka coproduct)
    example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : V × W →ₗ[K] U := φ.coprod ψ

    -- The coproduct map does the expected thing, first component
    example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inl K V W = φ :=
      LinearMap.coprod_inl φ ψ

    -- The coproduct map does the expected thing, second component
    example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) : φ.coprod ψ ∘ₗ LinearMap.inr K V W = ψ :=
      LinearMap.coprod_inr φ ψ

    -- The coproduct map is defined in the expected way
    example (φ : V →ₗ[K] U) (ψ : W →ₗ[K] U) (v : V) (w : W) :
        φ.coprod ψ (v, w) = φ v + ψ w :=
      rfl

    end binary_product

Let us now turn to sums and products of arbitrary families of vector spaces. Here we will simply see how to define a family of vector spaces and access the universal properties of sums and products. Note that the direct sum notation is scoped to the <span class="pre">`DirectSum`</span> namespace, and that the universal property of direct sums requires decidable equality on the indexing type (this is somehow an implementation accident).

    section families
    open DirectSum

    variable {ι : Type*} [DecidableEq ι]
             (V : ι → Type*) [∀ i, AddCommGroup (V i)] [∀ i, Module K (V i)]

    -- The universal property of the direct sum assembles maps from the summands to build
    -- a map from the direct sum
    example (φ : Π i, (V i →ₗ[K] W)) : (⨁ i, V i) →ₗ[K] W :=
      DirectSum.toModule K ι W φ

    -- The universal property of the direct product assembles maps into the factors
    -- to build a map into the direct product
    example (φ : Π i, (W →ₗ[K] V i)) : W →ₗ[K] (Π i, V i) :=
      LinearMap.pi φ

    -- The projection maps from the product
    example (i : ι) : (Π j, V j) →ₗ[K] V i := LinearMap.proj i

    -- The inclusion maps into the sum
    example (i : ι) : V i →ₗ[K] (⨁ i, V i) := DirectSum.lof K ι V i

    -- The inclusion maps into the product
    example (i : ι) : V i →ₗ[K] (Π i, V i) := LinearMap.single K V i

    -- In case `ι` is a finite type, there is an isomorphism between the sum and product.
    example [Fintype ι] : (⨁ i, V i) ≃ₗ[K] (Π i, V i) :=
      linearEquivFunOnFintype K ι V

    end families

<span id="index-2"></span>

## <span class="section-number">10.2. </span>Subspaces and quotients<a href="#subspaces-and-quotients" class="headerlink" title="Link to this heading"></a>

### <span class="section-number">10.2.1. </span>Subspaces<a href="#subspaces" class="headerlink" title="Link to this heading"></a>

Just as linear maps are bundled, a linear subspace of <span class="pre">`V`</span> is also a bundled structure consisting of a set in <span class="pre">`V`</span>, called the carrier of the subspace, with the relevant closure properties. Again the word module appears instead of vector space because of the more general context that Mathlib actually uses for linear algebra.

    variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

    example (U : Submodule K V) {x y : V} (hx : x ∈ U) (hy : y ∈ U) :
        x + y ∈ U :=
      U.add_mem hx hy

    example (U : Submodule K V) {x : V} (hx : x ∈ U) (a : K) :
        a • x ∈ U :=
      U.smul_mem a hx

In the example above, it is important to understand that <span class="pre">`Submodule`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span> is the type of <span class="pre">`K`</span>-linear subspaces of <span class="pre">`V`</span>, rather than a predicate <span class="pre">`IsSubmodule`</span>` `<span class="pre">`U`</span> where <span class="pre">`U`</span> is an element of <span class="pre">`Set`</span>` `<span class="pre">`V`</span>. <span class="pre">`Submodule`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span> is endowed with a coercion to <span class="pre">`Set`</span>` `<span class="pre">`V`</span> and a membership predicate on <span class="pre">`V`</span>. See <a href="C08_Hierarchies.html#section-hierarchies-subobjects" class="reference internal"><span class="std std-numref">Section 8.3</span></a> for an explanation of how and why this is done.

Of course, two subspaces are the same if and only if they have the same elements. This fact is registered for use with the <span class="pre">`ext`</span> tactic, which can be used to prove two subspaces are equal in the same way it is used to prove that two sets are equal.

To state and prove, for example, that <span class="pre">`ℝ`</span> is a <span class="pre">`ℝ`</span>-linear subspace of <span class="pre">`ℂ`</span>, what we really want is to construct a term of type <span class="pre">`Submodule`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`ℂ`</span> whose projection to <span class="pre">`Set`</span>` `<span class="pre">`ℂ`</span> is <span class="pre">`ℝ`</span>, or, more precisely, the image of <span class="pre">`ℝ`</span> in <span class="pre">`ℂ`</span>.

    noncomputable example : Submodule ℝ ℂ where
      carrier := Set.range ((↑) : ℝ → ℂ)
      add_mem' := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        use n + m
        simp
      zero_mem' := by
        use 0
        simp
      smul_mem' := by
        rintro c - ⟨a, rfl⟩
        use c*a
        simp

The prime at the end of proof fields in <span class="pre">`Submodule`</span> are analogous to the one in <span class="pre">`LinearMap`</span>. Those fields are stated in terms of the <span class="pre">`carrier`</span> field because they are defined before the <span class="pre">`MemberShip`</span> instance. They are then superseded by <span class="pre">`Submodule.add_mem`</span>, <span class="pre">`Submodule.zero_mem`</span> and <span class="pre">`Submodule.smul_mem`</span> that we saw above.

As an exercise in manipulating subspaces and linear maps, you will define the pre-image of a subspace by a linear map (of course we will see below that Mathlib already knows about this). Remember that <span class="pre">`Set.mem_preimage`</span> can be used to rewrite a statement involving membership and preimage. This is the only lemma you will need in addition to the lemmas discussed above about <span class="pre">`LinearMap`</span> and <span class="pre">`Submodule`</span>.

    def preimage {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W) (H : Submodule K W) :
        Submodule K V where
      carrier := φ ⁻¹' H
      zero_mem' := by
        sorry
      add_mem' := by
        sorry
      smul_mem' := by
        sorry

Using type classes, Mathlib knows that a subspace of a vector space inherits a vector space structure.

    example (U : Submodule K V) : Module K U := inferInstance

This example is subtle. The object <span class="pre">`U`</span> is not a type, but Lean automatically coerces it to a type by interpreting it as a subtype of <span class="pre">`V`</span>. So the above example can be restated more explicitly as:

    example (U : Submodule K V) : Module K {x : V // x ∈ U} := inferInstance

### <span class="section-number">10.2.2. </span>Complete lattice structure and internal direct sums<a href="#complete-lattice-structure-and-internal-direct-sums" class="headerlink" title="Link to this heading"></a>

An important benefit of having a type <span class="pre">`Submodule`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span> instead of a predicate <span class="pre">`IsSubmodule`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`V`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Prop`</span> is that one can easily endow <span class="pre">`Submodule`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span> with additional structure. Importantly, it has the structure of a complete lattice structure with respect to inclusion. For instance, instead of having a lemma stating that an intersection of two subspaces of <span class="pre">`V`</span> is again a subspace, we use the lattice operation <span class="pre">`⊓`</span> to construct the intersection. We can then apply arbitrary lemmas about lattices to the construction.

Let us check that the set underlying the infimum of two subspaces is indeed, by definition, their intersection.

    example (H H' : Submodule K V) :
        ((H ⊓ H' : Submodule K V) : Set V) = (H : Set V) ∩ (H' : Set V) := rfl

It may look strange to have a different notation for what amounts to the intersection of the underlying sets, but the correspondence does not carry over to the supremum operation and set union, since a union of subspaces is not, in general, a subspace. Instead one needs to use the subspace generated by the union, which is done using <span class="pre">`Submodule.span`</span>.

    example (H H' : Submodule K V) :
        ((H ⊔ H' : Submodule K V) : Set V) = Submodule.span K ((H : Set V) ∪ (H' : Set V)) := by
      simp [Submodule.span_union]

Another subtlety is that <span class="pre">`V`</span> itself does not have type <span class="pre">`Submodule`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span>, so we need a way to talk about <span class="pre">`V`</span> seen as a subspace of <span class="pre">`V`</span>. This is also provided by the lattice structure: the full subspace is the top element of this lattice.

    example (x : V) : x ∈ (⊤ : Submodule K V) := trivial

Similarly the bottom element of this lattice is the subspace whose only element is the zero element.

    example (x : V) : x ∈ (⊥ : Submodule K V) ↔ x = 0 := Submodule.mem_bot K

In particular we can discuss the case of subspaces that are in (internal) direct sum. In the case of two subspaces, we use the general purpose predicate <span class="pre">`IsCompl`</span> which makes sense for any bounded partially ordered type. In the case of general families of subspaces we use <span class="pre">`DirectSum.IsInternal`</span>.

    -- If two subspaces are in direct sum then they span the whole space.
    example (U V : Submodule K V) (h : IsCompl U V) :
      U ⊔ V = ⊤ := h.sup_eq_top

    -- If two subspaces are in direct sum then they intersect only at zero.
    example (U V : Submodule K V) (h : IsCompl U V) :
      U ⊓ V = ⊥ := h.inf_eq_bot

    section
    open DirectSum
    variable {ι : Type*} [DecidableEq ι]

    -- If subspaces are in direct sum then they span the whole space.
    example (U : ι → Submodule K V) (h : DirectSum.IsInternal U) :
      ⨆ i, U i = ⊤ := h.submodule_iSup_eq_top

    -- If subspaces are in direct sum then they pairwise intersect only at zero.
    example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V) (h : DirectSum.IsInternal U)
        {i j : ι} (hij : i ≠ j) : U i ⊓ U j = ⊥ :=
      (h.submodule_iSupIndep.pairwiseDisjoint hij).eq_bot

    -- Those conditions characterize direct sums.
    #check DirectSum.isInternal_submodule_iff_independent_and_iSup_eq_top

    -- The relation with external direct sums: if a family of subspaces is
    -- in internal direct sum then the map from their external direct sum into `V`
    -- is a linear isomorphism.
    noncomputable example {ι : Type*} [DecidableEq ι] (U : ι → Submodule K V)
        (h : DirectSum.IsInternal U) : (⨁ i, U i) ≃ₗ[K] V :=
      LinearEquiv.ofBijective (coeLinearMap U) h
    end

### <span class="section-number">10.2.3. </span>Subspace spanned by a set<a href="#subspace-spanned-by-a-set" class="headerlink" title="Link to this heading"></a>

In addition to building subspaces out of existing subspaces, we can build them out of any set <span class="pre">`s`</span> using <span class="pre">`Submodule.span`</span>` `<span class="pre">`K`</span>` `<span class="pre">`s`</span> which builds the smallest subspace containing <span class="pre">`s`</span>. On paper it is common to use that this space is made of all linear combinations of elements of <span class="pre">`s`</span>. But it is often more efficient to use its universal property expressed by <span class="pre">`Submodule.span_le`</span>, and the whole theory of Galois connections.

    example {s : Set V} (E : Submodule K V) : Submodule.span K s ≤ E ↔ s ⊆ E :=
      Submodule.span_le

    example : GaloisInsertion (Submodule.span K) ((↑) : Submodule K V → Set V) :=
      Submodule.gi K V

When those are not enough, one can use the relevant induction principle <span class="pre">`Submodule.span_induction`</span> which ensures a property holds for every element of the span of <span class="pre">`s`</span> as long as it holds on <span class="pre">`zero`</span> and elements of <span class="pre">`s`</span> and is stable under sum and scalar multiplication.

As an exercise, let us reprove one implication of <span class="pre">`Submodule.mem_sup`</span>. Remember that you can use the module tactic to close goals that follow from the axioms relating the various algebraic operations on <span class="pre">`V`</span>.

    example {S T : Submodule K V} {x : V} (h : x ∈ S ⊔ T) :
        ∃ s ∈ S, ∃ t ∈ T, x = s + t  := by
      rw [← S.span_eq, ← T.span_eq, ← Submodule.span_union] at h
      induction h using Submodule.span_induction with
      | mem y h =>
          sorry
      | zero =>
          sorry
      | add x y hx hy hx' hy' =>
          sorry
      | smul a x hx hx' =>
          sorry

### <span class="section-number">10.2.4. </span>Pushing and pulling subspaces<a href="#pushing-and-pulling-subspaces" class="headerlink" title="Link to this heading"></a>

As promised earlier, we now describe how to push and pull subspaces by linear maps. As usual in Mathlib, the first operation is called <span class="pre">`map`</span> and the second one is called <span class="pre">`comap`</span>.

    section

    variable {W : Type*} [AddCommGroup W] [Module K W] (φ : V →ₗ[K] W)

    variable (E : Submodule K V) in
    #check (Submodule.map φ E : Submodule K W)

    variable (F : Submodule K W) in
    #check (Submodule.comap φ F : Submodule K V)

Note those live in the <span class="pre">`Submodule`</span> namespace so one can use dot notation and write <span class="pre">`E.map`</span>` `<span class="pre">`φ`</span> instead of <span class="pre">`Submodule.map`</span>` `<span class="pre">`φ`</span>` `<span class="pre">`E`</span>, but this is pretty awkward to read (although some Mathlib contributors use this spelling).

In particular the range and kernel of a linear map are subspaces. Those special cases are important enough to get declarations.

    example : LinearMap.range φ = .map φ ⊤ := LinearMap.range_eq_map φ

    example : LinearMap.ker φ = .comap φ ⊥ := Submodule.comap_bot φ -- or `rfl`

Note that we cannot write <span class="pre">`φ.ker`</span> instead of <span class="pre">`LinearMap.ker`</span>` `<span class="pre">`φ`</span> because <span class="pre">`LinearMap.ker`</span> also applies to classes of maps preserving more structure, hence it does not expect an argument whose type starts with <span class="pre">`LinearMap`</span>, hence dot notation doesn’t work here. However we were able to use the other flavor of dot notation in the right-hand side. Because Lean expects a term with type <span class="pre">`Submodule`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span> after elaborating the left-hand side, it interprets <span class="pre">`.comap`</span> as <span class="pre">`Submodule.comap`</span>.

The following lemmas give the key relations between those submodule and the properties of <span class="pre">`φ`</span>.

    open Function LinearMap

    example : Injective φ ↔ ker φ = ⊥ := ker_eq_bot.symm

    example : Surjective φ ↔ range φ = ⊤ := range_eq_top.symm

As an exercise, let us prove the Galois connection property for <span class="pre">`map`</span> and <span class="pre">`comap`</span>. One can use the following lemmas but this is not required since they are true by definition.

    #check Submodule.mem_map_of_mem
    #check Submodule.mem_map
    #check Submodule.mem_comap

    example (E : Submodule K V) (F : Submodule K W) :
        Submodule.map φ E ≤ F ↔ E ≤ Submodule.comap φ F := by
      sorry

### <span class="section-number">10.2.5. </span>Quotient spaces<a href="#quotient-spaces" class="headerlink" title="Link to this heading"></a>

Quotient vector spaces use the general quotient notation (typed with <span class="pre">`\quot`</span>, not the ordinary <span class="pre">`/`</span>). The projection onto a quotient space is <span class="pre">`Submodule.mkQ`</span> and the universal property is <span class="pre">`Submodule.liftQ`</span>.

    variable (E : Submodule K V)

    example : Module K (V ⧸ E) := inferInstance

    example : V →ₗ[K] V ⧸ E := E.mkQ

    example : ker E.mkQ = E := E.ker_mkQ

    example : range E.mkQ = ⊤ := E.range_mkQ

    example (hφ : E ≤ ker φ) : V ⧸ E →ₗ[K] W := E.liftQ φ hφ

    example (F : Submodule K W) (hφ : E ≤ .comap φ F) : V ⧸ E →ₗ[K] W ⧸ F := E.mapQ F φ hφ

    noncomputable example : (V ⧸ LinearMap.ker φ) ≃ₗ[K] range φ := φ.quotKerEquivRange

As an exercise, let us prove the correspondence theorem for subspaces of quotient spaces. Mathlib knows a slightly more precise version as <span class="pre">`Submodule.comapMkQRelIso`</span>.

    open Submodule

    #check Submodule.map_comap_eq
    #check Submodule.comap_map_eq

    example : Submodule K (V ⧸ E) ≃ { F : Submodule K V // E ≤ F } where
      toFun := sorry
      invFun := sorry
      left_inv := sorry
      right_inv := sorry

## <span class="section-number">10.3. </span>Endomorphisms<a href="#endomorphisms" class="headerlink" title="Link to this heading"></a>

An important special case of linear maps are endomorphisms: linear maps from a vector space to itself. They are interesting because they form a <span class="pre">`K`</span>-algebra. In particular we can evaluate polynomials with coefficients in <span class="pre">`K`</span> on them, and they can have eigenvalues and eigenvectors.

Mathlib uses the abbreviation <span class="pre">`Module.End`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span>` `<span class="pre">`:=`</span>` `<span class="pre">`V`</span>` `<span class="pre">`→ₗ[K]`</span>` `<span class="pre">`V`</span> which is convenient when using a lot of these (especially after opening the <span class="pre">`Module`</span> namespace).

    variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

    variable {W : Type*} [AddCommGroup W] [Module K W]


    open Polynomial Module LinearMap End

    example (φ ψ : End K V) : φ * ψ = φ ∘ₗ ψ :=
      End.mul_eq_comp φ ψ -- `rfl` would also work

    -- evaluating `P` on `φ`
    example (P : K[X]) (φ : End K V) : V →ₗ[K] V :=
      aeval φ P

    -- evaluating `X` on `φ` gives back `φ`
    example (φ : End K V) : aeval φ (X : K[X]) = φ :=
      aeval_X φ

As an exercise manipulating endomorphisms, subspaces and polynomials, let us prove the (binary) kernels lemma: for any endomorphism <span class="math notranslate nohighlight">\\φ\\</span> and any two relatively prime polynomials <span class="math notranslate nohighlight">\\P\\</span> and <span class="math notranslate nohighlight">\\Q\\</span>, we have <span class="math notranslate nohighlight">\\\ker P(φ) ⊕ \ker Q(φ) = \ker \big(PQ(φ)\big)\\</span>.

Note that <span class="pre">`IsCoprime`</span>` `<span class="pre">`x`</span>` `<span class="pre">`y`</span> is defined as <span class="pre">`∃`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b,`</span>` `<span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`1`</span>.

    #check Submodule.eq_bot_iff
    #check Submodule.mem_inf
    #check LinearMap.mem_ker

    example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) : ker (aeval φ P) ⊓ ker (aeval φ Q) = ⊥ := by
      sorry

    #check Submodule.add_mem_sup
    #check map_mul
    #check End.mul_apply
    #check LinearMap.ker_le_ker_comp

    example (P Q : K[X]) (h : IsCoprime P Q) (φ : End K V) :
        ker (aeval φ P) ⊔ ker (aeval φ Q) = ker (aeval φ (P*Q)) := by
      sorry

We now move to the discussions of eigenspaces and eigenvalues. The eigenspace associated to an endomorphism <span class="math notranslate nohighlight">\\φ\\</span> and a scalar <span class="math notranslate nohighlight">\\a\\</span> is the kernel of <span class="math notranslate nohighlight">\\φ - aId\\</span>. Eigenspaces are defined for all values of <span class="pre">`a`</span>, although they are interesting only when they are non-zero. However an eigenvector is, by definition, a non-zero element of an eigenspace. The corresponding predicate is <span class="pre">`End.HasEigenvector`</span>.

    example (φ : End K V) (a : K) : φ.eigenspace a = LinearMap.ker (φ - a • 1) :=
      End.eigenspace_def

Then there is a predicate <span class="pre">`End.HasEigenvalue`</span> and the corresponding subtype <span class="pre">`End.Eigenvalues`</span>.

    example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ φ.eigenspace a ≠ ⊥ :=
      Iff.rfl

    example (φ : End K V) (a : K) : φ.HasEigenvalue a ↔ ∃ v, φ.HasEigenvector a v  :=
      ⟨End.HasEigenvalue.exists_hasEigenvector, fun ⟨_, hv⟩ ↦ φ.hasEigenvalue_of_hasEigenvector hv⟩

    example (φ : End K V) : φ.Eigenvalues = {a // φ.HasEigenvalue a} :=
      rfl

    -- Eigenvalue are roots of the minimal polynomial
    example (φ : End K V) (a : K) : φ.HasEigenvalue a → (minpoly K φ).IsRoot a :=
      φ.isRoot_of_hasEigenvalue

    -- In finite dimension, the converse is also true (we will discuss dimension below)
    example [FiniteDimensional K V] (φ : End K V) (a : K) :
        φ.HasEigenvalue a ↔ (minpoly K φ).IsRoot a :=
      φ.hasEigenvalue_iff_isRoot

    -- Cayley-Hamilton
    example [FiniteDimensional K V] (φ : End K V) : aeval φ φ.charpoly = 0 :=
      φ.aeval_self_charpoly

<span id="matrices-bases-dimension"></span>

## <span class="section-number">10.4. </span>Matrices, bases and dimension<a href="#matrices-bases-and-dimension" class="headerlink" title="Link to this heading"></a>

<span id="id2"></span>

### <span class="section-number">10.4.1. </span>Matrices<a href="#matrices" class="headerlink" title="Link to this heading"></a>

Before introducing bases for abstract vector spaces, we go back to the much more elementary setup of linear algebra in <span class="math notranslate nohighlight">\\K^n\\</span> for some field <span class="math notranslate nohighlight">\\K\\</span>. Here the main objects are vectors and matrices. For concrete vectors, one can use the <span class="pre">`![…]`</span> notation, where components are separated by commas. For concrete matrices we can use the <span class="pre">`!![…]`</span> notation, lines are separated by semi-colons and components of lines are separated by colons. When entries have a computable type such as <span class="pre">`ℕ`</span> or <span class="pre">`ℚ`</span>, we can use the <span class="pre">`eval`</span> command to play with basic operations.

    section matrices

    -- Adding vectors
    #eval ![1, 2] + ![3, 4]  -- ![4, 6]

    -- Adding matrices
    #eval !![1, 2; 3, 4] + !![3, 4; 5, 6]  -- !![4, 6; 8, 10]

    -- Multiplying matrices
    #eval !![1, 2; 3, 4] * !![3, 4; 5, 6]  -- !![13, 16; 29, 36]

It is important to understand that this use of <span class="pre">`#eval`</span> is interesting only for exploration, it is not meant to replace a computer algebra system such as Sage. The data representation used here for matrices is *not* computationally efficient in any way. It uses functions instead of arrays and is optimized for proving, not computing. The virtual machine used by <span class="pre">`#eval`</span> is also not optimized for this use.

Beware the matrix notation list rows but the vector notation is neither a row vector nor a column vector. Multiplication of a matrix with a vector from the left (resp. right) interprets the vector as a row (resp. column) vector. This corresponds to operations <span class="pre">`Matrix.vecMul`</span>, with notation <span class="pre">`ᵥ*`</span> and <span class="pre">`Matrix.mulVec`</span>, with notation \` \*ᵥ\`. Those notations are scoped in the <span class="pre">`Matrix`</span> namespace that we therefore need to open.

    open Matrix

    -- matrices acting on vectors on the left
    #eval !![1, 2; 3, 4] *ᵥ ![1, 1] -- ![3, 7]

    -- matrices acting on vectors on the left, resulting in a size one matrix
    #eval !![1, 2] *ᵥ ![1, 1]  -- ![3]

    -- matrices acting on vectors on the right
    #eval  ![1, 1, 1] ᵥ* !![1, 2; 3, 4; 5, 6] -- ![9, 12]

In order to generate matrices with identical rows or columns specified by a vector, we use <span class="pre">`Matrix.replicateRow`</span> and <span class="pre">`Matrix.replicateCol`</span>, with arguments the type indexing the rows or columns and the vector. For instance one can get single row or single column matrixes (more precisely matrices whose rows or columns are indexed by <span class="pre">`Fin`</span>` `<span class="pre">`1`</span>).

    #eval replicateRow (Fin 1) ![1, 2] -- !![1, 2]

    #eval replicateCol (Fin 1) ![1, 2] -- !![1; 2]

Other familiar operations include the vector dot product, matrix transpose, and, for square matrices, determinant and trace.

    -- vector dot product
    #eval ![1, 2] ⬝ᵥ ![3, 4] -- `11`

    -- matrix transpose
    #eval !![1, 2; 3, 4]ᵀ -- `!![1, 3; 2, 4]`

    -- determinant
    #eval !![(1 : ℤ), 2; 3, 4].det -- `-2`

    -- trace
    #eval !![(1 : ℤ), 2; 3, 4].trace -- `5`

When entries do not have a computable type, for instance if they are real numbers, we cannot hope that <span class="pre">`#eval`</span> can help. Also this kind of evaluation cannot be used in proofs without considerably expanding the trusted code base (i.e. the part of Lean that you need to trust when checking proofs).

So it is good to also use the <span class="pre">`simp`</span> and <span class="pre">`norm_num`</span> tactics in proofs, or their command counter-part for quick exploration.

    #simp !![(1 : ℝ), 2; 3, 4].det -- `4 - 2*3`

    #norm_num !![(1 : ℝ), 2; 3, 4].det -- `-2`

    #norm_num !![(1 : ℝ), 2; 3, 4].trace -- `5`

    variable (a b c d : ℝ) in
    #simp !![a, b; c, d].det -- `a * d – b * c`

The next important operation on square matrices is inversion. In the same way as division of numbers is always defined and returns the artificial value zero for division by zero, the inversion operation is defined on all matrices and returns the zero matrix for non-invertible matrices.

More precisely, there is general function <span class="pre">`Ring.inverse`</span> that does this in any ring, and, for any matrix <span class="pre">`A`</span>, <span class="pre">`A⁻¹`</span> is defined as <span class="pre">`Ring.inverse`</span>` `<span class="pre">`A.det`</span>` `<span class="pre">`•`</span>` `<span class="pre">`A.adjugate`</span>. According to Cramer’s rule, this is indeed the inverse of <span class="pre">`A`</span> when the determinant of <span class="pre">`A`</span> is not zero.

    #norm_num [Matrix.inv_def] !![(1 : ℝ), 2; 3, 4]⁻¹ -- !![-2, 1; 3 / 2, -(1 / 2)]

Of course this definition is really useful only for invertible matrices. There is a general type class <span class="pre">`Invertible`</span> that helps recording this. For instance, the <span class="pre">`simp`</span> call in the next example will use the <span class="pre">`inv_mul_of_invertible`</span> lemma which has an <span class="pre">`Invertible`</span> type-class assumption, so it will trigger only if this can be found by the type-class synthesis system. Here we make this fact available using a <span class="pre">`have`</span> statement.

    example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
      have : Invertible !![(1 : ℝ), 2; 3, 4] := by
        apply Matrix.invertibleOfIsUnitDet
        norm_num
      simp

In this fully concrete case, we could also use the <span class="pre">`norm_num`</span> machinery, and <span class="pre">`apply?`</span> to find the final line:

    example : !![(1 : ℝ), 2; 3, 4]⁻¹ * !![(1 : ℝ), 2; 3, 4] = 1 := by
      norm_num [Matrix.inv_def]
      exact one_fin_two.symm

All the concrete matrices above have their rows and columns indexed by <span class="pre">`Fin`</span>` `<span class="pre">`n`</span> for some <span class="pre">`n`</span> (not necessarily the same for rows and columns). But sometimes it is more convenient to index matrices using arbitrary finite types. For instance the adjacency matrix of a finite graph has rows and columns naturally indexed by the vertices of the graph.

In fact when simply wants to define matrices without defining any operation on them, finiteness of the indexing types are not even needed, and coefficients can have any type, without any algebraic structure. So Mathlib simply defines <span class="pre">`Matrix`</span>` `<span class="pre">`m`</span>` `<span class="pre">`n`</span>` `<span class="pre">`α`</span> to be <span class="pre">`m`</span>` `<span class="pre">`→`</span>` `<span class="pre">`n`</span>` `<span class="pre">`→`</span>` `<span class="pre">`α`</span> for any types <span class="pre">`m`</span>, <span class="pre">`n`</span> and <span class="pre">`α`</span>, and the matrices we have been using so far had types such as <span class="pre">`Matrix`</span>` `<span class="pre">`(Fin`</span>` `<span class="pre">`2)`</span>` `<span class="pre">`(Fin`</span>` `<span class="pre">`2)`</span>` `<span class="pre">`ℝ`</span>. Of course algebraic operations require more assumptions on <span class="pre">`m`</span>, <span class="pre">`n`</span> and <span class="pre">`α`</span>.

Note the main reason why we do not use <span class="pre">`m`</span>` `<span class="pre">`→`</span>` `<span class="pre">`n`</span>` `<span class="pre">`→`</span>` `<span class="pre">`α`</span> directly is to allow the type class system to understand what we want. For instance, for a ring <span class="pre">`R`</span>, the type <span class="pre">`n`</span>` `<span class="pre">`→`</span>` `<span class="pre">`R`</span> is endowed with the point-wise multiplication operation, and similarly <span class="pre">`m`</span>` `<span class="pre">`→`</span>` `<span class="pre">`n`</span>` `<span class="pre">`→`</span>` `<span class="pre">`R`</span> has this operation which is *not* the multiplication we want on matrices.

In the first example below, we force Lean to see through the definition of <span class="pre">`Matrix`</span> and accept the statement as meaningful, and then prove it by checking all entries.

But then the next two examples reveal that Lean uses the point-wise multiplication on <span class="pre">`Fin`</span>` `<span class="pre">`2`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Fin`</span>` `<span class="pre">`2`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℤ`</span> but the matrix multiplication on <span class="pre">`Matrix`</span>` `<span class="pre">`(Fin`</span>` `<span class="pre">`2)`</span>` `<span class="pre">`(Fin`</span>` `<span class="pre">`2)`</span>` `<span class="pre">`ℤ`</span>.

    section

    example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl

    example : (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) * (fun _ ↦ 1 : Fin 2 → Fin 2 → ℤ) = !![1, 1; 1, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> rfl

    example : !![1, 1; 1, 1] * !![1, 1; 1, 1] = !![2, 2; 2, 2] := by
      norm_num

In order to define matrices as functions without losing the benefits of <span class="pre">`Matrix`</span> for type class synthesis, we can use the equivalence <span class="pre">`Matrix.of`</span> between functions and matrices. This equivalence is secretly defined using <span class="pre">`Equiv.refl`</span>.

For instance we can define Vandermonde matrices corresponding to a vector <span class="pre">`v`</span>.

    example {n : ℕ} (v : Fin n → ℝ) :
        Matrix.vandermonde v = Matrix.of (fun i j : Fin n ↦ v i ^ (j : ℕ)) :=
      rfl
    end
    end matrices

### <span class="section-number">10.4.2. </span>Bases<a href="#bases" class="headerlink" title="Link to this heading"></a>

We now want to discuss bases of vector spaces. Informally there are many ways to define this notion. One can use a universal property. One can say a basis is a family of vectors that is linearly independent and spanning. Or one can combine those properties and directly say that a basis is a family of vectors such that every vectors can be written uniquely as a linear combination of bases vectors. Yet another way to say it is that a basis provides a linear isomorphism with a power of the base field <span class="pre">`K`</span>, seen as a vector space over <span class="pre">`K`</span>.

This isomorphism version is actually the one that Mathlib uses as a definition under the hood, and other characterizations are proven from it. One must be slightly careful with the “power of <span class="pre">`K`</span>” idea in the case of infinite bases. Indeed only finite linear combinations make sense in this algebraic context. So what we need as a reference vector space is not a direct product of copies of <span class="pre">`K`</span> but a direct sum. We could use <span class="pre">`⨁`</span>` `<span class="pre">`i`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ι,`</span>` `<span class="pre">`K`</span> for some type <span class="pre">`ι`</span> indexing the basis But we rather use the more specialized spelling <span class="pre">`ι`</span>` `<span class="pre">`→₀`</span>` `<span class="pre">`K`</span> which means “functions from <span class="pre">`ι`</span> to <span class="pre">`K`</span> with finite support”, i.e. functions which vanish outside a finite set in <span class="pre">`ι`</span> (this finite set is not fixed, it depends on the function). Evaluating such a function coming from a basis <span class="pre">`B`</span> at a vector <span class="pre">`v`</span> and <span class="pre">`i`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ι`</span> returns the component (or coordinate) of <span class="pre">`v`</span> on the <span class="pre">`i`</span>-th basis vector.

The type of bases indexed by a type <span class="pre">`ι`</span> of <span class="pre">`V`</span> as a <span class="pre">`K`</span> vector space is <span class="pre">`Basis`</span>` `<span class="pre">`ι`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span>. The isomorphism is called <span class="pre">`Basis.repr`</span>.

    variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

    section

    variable {ι : Type*} (B : Basis ι K V) (v : V) (i : ι)

    -- The basis vector with index ``i``
    #check (B i : V)

    -- the linear isomorphism with the model space given by ``B``
    #check (B.repr : V ≃ₗ[K] ι →₀ K)

    -- the component function of ``v``
    #check (B.repr v : ι →₀ K)

    -- the component of ``v`` with index ``i``
    #check (B.repr v i : K)

Instead of starting with such an isomorphism, one can start with a family <span class="pre">`b`</span> of vectors that is linearly independent and spanning, this is <span class="pre">`Basis.mk`</span>.

The assumption that the family is spanning is spelled out as <span class="pre">`⊤`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`Submodule.span`</span>` `<span class="pre">`K`</span>` `<span class="pre">`(Set.range`</span>` `<span class="pre">`b)`</span>. Here <span class="pre">`⊤`</span> is the top submodule of <span class="pre">`V`</span>, i.e. <span class="pre">`V`</span> seen as submodule of itself. This spelling looks a bit tortuous, but we will see below that it is almost equivalent by definition to the more readable <span class="pre">`∀`</span>` `<span class="pre">`v,`</span>` `<span class="pre">`v`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`Submodule.span`</span>` `<span class="pre">`K`</span>` `<span class="pre">`(Set.range`</span>` `<span class="pre">`b)`</span> (the underscores in the snippet below refers to the useless information <span class="pre">`v`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`⊤`</span>).

    noncomputable example (b : ι → V) (b_indep : LinearIndependent K b)
        (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) : Basis ι K V :=
      Basis.mk b_indep (fun v _ ↦ b_spans v)

    -- The family of vectors underlying the above basis is indeed ``b``.
    example (b : ι → V) (b_indep : LinearIndependent K b)
        (b_spans : ∀ v, v ∈ Submodule.span K (Set.range b)) (i : ι) :
        Basis.mk b_indep (fun v _ ↦ b_spans v) i = b i :=
      Basis.mk_apply b_indep (fun v _ ↦ b_spans v) i

In particular the model vector space <span class="pre">`ι`</span>` `<span class="pre">`→₀`</span>` `<span class="pre">`K`</span> has a so-called canonical basis whose <span class="pre">`repr`</span> function evaluated on any vector is the identity isomorphism. It is called <span class="pre">`Finsupp.basisSingleOne`</span> where <span class="pre">`Finsupp`</span> means function with finite support and <span class="pre">`basisSingleOne`</span> refers to the fact that basis vectors are functions which vanish expect for a single input value. More precisely the basis vector indexed by <span class="pre">`i`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ι`</span> is <span class="pre">`Finsupp.single`</span>` `<span class="pre">`i`</span>` `<span class="pre">`1`</span> which is the finitely supported function taking value <span class="pre">`1`</span> at <span class="pre">`i`</span> and <span class="pre">`0`</span> everywhere else.

    variable [DecidableEq ι]

    example : Finsupp.basisSingleOne.repr = LinearEquiv.refl K (ι →₀ K) :=
      rfl

    example (i : ι) : Finsupp.basisSingleOne i = Finsupp.single i 1 :=
      rfl

The story of finitely supported functions is unneeded when the indexing type is finite. In this case we can use the simpler <span class="pre">`Pi.basisFun`</span> which gives a basis of the whole <span class="pre">`ι`</span>` `<span class="pre">`→`</span>` `<span class="pre">`K`</span>.

    example [Finite ι] (x : ι → K) (i : ι) : (Pi.basisFun K ι).repr x i = x i := by
      simp

Going back to the general case of bases of abstract vector spaces, we can express any vector as a linear combination of basis vectors. Let us first see the easy case of finite bases.

    example [Fintype ι] : ∑ i : ι, B.repr v i • (B i) = v :=
      B.sum_repr v

When <span class="pre">`ι`</span> is not finite, the above statement makes no sense a priori: we cannot take a sum over <span class="pre">`ι`</span>. However the support of the function being summed is finite (it is the support of <span class="pre">`B.repr`</span>` `<span class="pre">`v`</span>). But we need to apply a construction that takes this into account. Here Mathlib uses a special purpose function that requires some time to get used to: <span class="pre">`Finsupp.linearCombination`</span> (which is built on top of the more general <span class="pre">`Finsupp.sum`</span>). Given a finitely supported function <span class="pre">`c`</span> from a type <span class="pre">`ι`</span> to the base field <span class="pre">`K`</span> and any function <span class="pre">`f`</span> from <span class="pre">`ι`</span> to <span class="pre">`V`</span>, <span class="pre">`Finsupp.linearCombination`</span>` `<span class="pre">`K`</span>` `<span class="pre">`f`</span>` `<span class="pre">`c`</span> is the sum over the support of <span class="pre">`c`</span> of the scalar multiplication <span class="pre">`c`</span>` `<span class="pre">`•`</span>` `<span class="pre">`f`</span>. In particular, we can replace it by a sum over any finite set containing the support of <span class="pre">`c`</span>.

    example (c : ι →₀ K) (f : ι → V) (s : Finset ι) (h : c.support ⊆ s) :
        Finsupp.linearCombination K f c = ∑ i ∈ s, c i • f i :=
      Finsupp.linearCombination_apply_of_mem_supported K h

One could also assume that <span class="pre">`f`</span> is finitely supported and still get a well defined sum. But the choice made by <span class="pre">`Finsupp.linearCombination`</span> is the one relevant to our basis discussion since it allows to state the generalization of <span class="pre">`Basis.sum_repr`</span>.

    example : Finsupp.linearCombination K B (B.repr v) = v :=
      B.linearCombination_repr v

One could wonder why <span class="pre">`K`</span> is an explicit argument here, despite the fact it can be inferred from the type of <span class="pre">`c`</span>. The point is that the partially applied <span class="pre">`Finsupp.linearCombination`</span>` `<span class="pre">`K`</span>` `<span class="pre">`f`</span> is interesting in itself. It is not a bare function from <span class="pre">`ι`</span>` `<span class="pre">`→₀`</span>` `<span class="pre">`K`</span> to <span class="pre">`V`</span> but a <span class="pre">`K`</span>-linear map.

    variable (f : ι → V) in
    #check (Finsupp.linearCombination K f : (ι →₀ K) →ₗ[K] V)

Returning to the mathematical discussion, it is important to understand that the representation of vectors in a basis is less useful in formalized mathematics than you may think. Indeed it is very often more efficient to directly use more abstract properties of bases. In particular the universal property of bases connecting them to other free objects in algebra allows to construct linear maps by specifying the images of basis vectors. This is <span class="pre">`Basis.constr`</span>. For any <span class="pre">`K`</span>-vector space <span class="pre">`W`</span>, our basis <span class="pre">`B`</span> gives a linear isomorphism <span class="pre">`Basis.constr`</span>` `<span class="pre">`B`</span>` `<span class="pre">`K`</span> from <span class="pre">`ι`</span>` `<span class="pre">`→`</span>` `<span class="pre">`W`</span> to <span class="pre">`V`</span>` `<span class="pre">`→ₗ[K]`</span>` `<span class="pre">`W`</span>. This isomorphism is characterized by the fact that it sends any function <span class="pre">`u`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ι`</span>` `<span class="pre">`→`</span>` `<span class="pre">`W`</span> to a linear map sending the basis vector <span class="pre">`B`</span>` `<span class="pre">`i`</span> to <span class="pre">`u`</span>` `<span class="pre">`i`</span>, for every <span class="pre">`i`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ι`</span>.

    section

    variable {W : Type*} [AddCommGroup W] [Module K W]
             (φ : V →ₗ[K] W) (u : ι → W)

    #check (B.constr K : (ι → W) ≃ₗ[K] (V →ₗ[K] W))

    #check (B.constr K u : V →ₗ[K] W)

    example (i : ι) : B.constr K u (B i) = u i :=
      B.constr_basis K u i

This property is indeed characteristic because linear maps are determined by their values on bases:

    example (φ ψ : V →ₗ[K] W) (h : ∀ i, φ (B i) = ψ (B i)) : φ = ψ :=
      B.ext h

If we also have a basis <span class="pre">`B'`</span> on the target space then we can identify linear maps with matrices. This identification is a <span class="pre">`K`</span>-linear isomorphism.

    variable {ι' : Type*} (B' : Basis ι' K W) [Fintype ι] [DecidableEq ι] [Fintype ι'] [DecidableEq ι']

    open LinearMap

    #check (toMatrix B B' : (V →ₗ[K] W) ≃ₗ[K] Matrix ι' ι K)

    open Matrix -- get access to the ``*ᵥ`` notation for multiplication between matrices and vectors.

    example (φ : V →ₗ[K] W) (v : V) : (toMatrix B B' φ) *ᵥ (B.repr v) = B'.repr (φ v) :=
      toMatrix_mulVec_repr B B' φ v


    variable {ι'' : Type*} (B'' : Basis ι'' K W) [Fintype ι''] [DecidableEq ι'']

    example (φ : V →ₗ[K] W) : (toMatrix B B'' φ) = (toMatrix B' B'' .id) * (toMatrix B B' φ) := by
      simp

    end

As an exercise on this topic, we will prove part of the theorem which guarantees that endomorphisms have a well-defined determinant. Namely we want to prove that when two bases are indexed by the same type, the matrices they attach to any endomorphism have the same determinant. This would then need to be complemented using that bases all have isomorphic indexing types to get the full result.

Of course Mathlib already knows this, and <span class="pre">`simp`</span> can close the goal immediately, so you shouldn’t use it too soon, but rather use the provided lemmas.

    open Module LinearMap Matrix

    -- Some lemmas coming from the fact that `LinearMap.toMatrix` is an algebra morphism.
    #check toMatrix_comp
    #check id_comp
    #check comp_id
    #check toMatrix_id

    -- Some lemmas coming from the fact that ``Matrix.det`` is a multiplicative monoid morphism.
    #check Matrix.det_mul
    #check Matrix.det_one

    example [Fintype ι] (B' : Basis ι K V) (φ : End K V) :
        (toMatrix B B φ).det = (toMatrix B' B' φ).det := by
      set M := toMatrix B B φ
      set M' := toMatrix B' B' φ
      set P := (toMatrix B B') LinearMap.id
      set P' := (toMatrix B' B) LinearMap.id
      sorry
    end

### <span class="section-number">10.4.3. </span>Dimension<a href="#dimension" class="headerlink" title="Link to this heading"></a>

Returning to the case of a single vector space, bases are also useful to define the concept of dimension. Here again, there is the elementary case of finite-dimensional vector spaces. For such spaces we expect a dimension which is a natural number. This is <span class="pre">`Module.finrank`</span>. It takes the base field as an explicit argument since a given abelian group can be a vector space over different fields.

    section
    #check (Module.finrank K V : ℕ)

    -- `Fin n → K` is the archetypical space with dimension `n` over `K`.
    example (n : ℕ) : Module.finrank K (Fin n → K) = n :=
      Module.finrank_fin_fun K

    -- Seen as a vector space over itself, `ℂ` has dimension one.
    example : Module.finrank ℂ ℂ = 1 :=
      Module.finrank_self ℂ

    -- But as a real vector space it has dimension two.
    example : Module.finrank ℝ ℂ = 2 :=
      Complex.finrank_real_complex

Note that <span class="pre">`Module.finrank`</span> is defined for any vector space. It returns zero for infinite dimensional vector spaces, just as division by zero returns zero.

Of course many lemmas require a finite dimension assumption. This is the role of the <span class="pre">`FiniteDimensional`</span> typeclass. For instance, think about how the next example fails without this assumption.

    example [FiniteDimensional K V] : 0 < Module.finrank K V ↔ Nontrivial V  :=
      Module.finrank_pos_iff

In the above statement, <span class="pre">`Nontrivial`</span>` `<span class="pre">`V`</span> means <span class="pre">`V`</span> has at least two different elements. Note that <span class="pre">`Module.finrank_pos_iff`</span> has no explicit argument. This is fine when using it from left to right, but not when using it from right to left because Lean has no way to guess <span class="pre">`K`</span> from the statement <span class="pre">`Nontrivial`</span>` `<span class="pre">`V`</span>. In that case it is useful to use the name argument syntax, after checking that the lemma is stated over a ring named <span class="pre">`R`</span>. So we can write:

    example [FiniteDimensional K V] (h : 0 < Module.finrank K V) : Nontrivial V := by
      apply (Module.finrank_pos_iff (R := K)).1
      exact h

The above spelling is strange because we already have <span class="pre">`h`</span> as an assumption, so we could just as well give the full proof <span class="pre">`Module.finrank_pos_iff.1`</span>` `<span class="pre">`h`</span> but it is good to know for more complicated cases.

By definition, <span class="pre">`FiniteDimensional`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span> can be read from any basis.

    variable {ι : Type*} (B : Basis ι K V)

    example [Finite ι] : FiniteDimensional K V := FiniteDimensional.of_fintype_basis B

    example [FiniteDimensional K V] : Finite ι :=
      (FiniteDimensional.fintypeBasisIndex B).finite
    end

Using that the subtype corresponding to a linear subspace has a vector space structure, we can talk about the dimension of a subspace.

    section
    variable (E F : Submodule K V) [FiniteDimensional K V]

    open Module

    example : finrank K (E ⊔ F : Submodule K V) + finrank K (E ⊓ F : Submodule K V) =
        finrank K E + finrank K F :=
      Submodule.finrank_sup_add_finrank_inf_eq E F

    example : finrank K E ≤ finrank K V := Submodule.finrank_le E

In the first statement above, the purpose of the type ascriptions is to make sure that coercion to <span class="pre">`Type*`</span> does not trigger too early.

We are now ready for an exercise about <span class="pre">`finrank`</span> and subspaces.

    example (h : finrank K V < finrank K E + finrank K F) :
        Nontrivial (E ⊓ F : Submodule K V) := by
      sorry
    end

Let us now move to the general case of dimension theory. In this case <span class="pre">`finrank`</span> is useless, but we still have that, for any two bases of the same vector space, there is a bijection between the types indexing those bases. So we can still hope to define the rank as a cardinal, i.e. an element of the “quotient of the collection of types under the existence of a bijection equivalence relation”.

When discussing cardinal, it gets harder to ignore foundational issues around Russel’s paradox like we do everywhere else in this book. There is no type of all types because it would lead to logical inconsistencies. This issue is solved by the hierarchy of universes that we usually try to ignore.

Each type has a universe level, and those levels behave similarly to natural numbers. In particular there is zeroth level, and the corresponding universe <span class="pre">`Type`</span>` `<span class="pre">`0`</span> is simply denoted by <span class="pre">`Type`</span>. This universe is enough to hold almost all of classical mathematics. For instance <span class="pre">`ℕ`</span> and <span class="pre">`ℝ`</span> have type <span class="pre">`Type`</span>. Each level <span class="pre">`u`</span> has a successor denoted by <span class="pre">`u`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1`</span>, and <span class="pre">`Type`</span>` `<span class="pre">`u`</span> has type <span class="pre">`Type`</span>` `<span class="pre">`(u+1)`</span>.

But universe levels are not natural numbers, they have a really different nature and don’t have a type. In particular you cannot state in Lean something like <span class="pre">`u`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`u`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1`</span>. There is simply no type where this would take place. Even stating <span class="pre">`Type`</span>` `<span class="pre">`u`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`Type`</span>` `<span class="pre">`(u+1)`</span> does not make any sense since <span class="pre">`Type`</span>` `<span class="pre">`u`</span> and <span class="pre">`Type`</span>` `<span class="pre">`(u+1)`</span> have different types.

Whenever we write <span class="pre">`Type*`</span>, Lean inserts a universe level variable named <span class="pre">`u_n`</span> where <span class="pre">`n`</span> is a number. This allows definitions and statements to live in all universes.

Given a universe level <span class="pre">`u`</span>, we can define an equivalence relation on <span class="pre">`Type`</span>` `<span class="pre">`u`</span> saying two types <span class="pre">`α`</span> and <span class="pre">`β`</span> are equivalent if there is a bijection between them. The quotient type <span class="pre">`Cardinal.{u}`</span> lives in <span class="pre">`Type`</span>` `<span class="pre">`(u+1)`</span>. The curly braces denote a universe variable. The image of <span class="pre">`α`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type`</span>` `<span class="pre">`u`</span> in this quotient is <span class="pre">`Cardinal.mk`</span>` `<span class="pre">`α`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Cardinal.{u}`</span>.

But we cannot directly compare cardinals in different universes. So technically we cannot define the rank of a vector space <span class="pre">`V`</span> as the cardinal of all types indexing a basis of <span class="pre">`V`</span>. So instead it is defined as the supremum <span class="pre">`Module.rank`</span>` `<span class="pre">`K`</span>` `<span class="pre">`V`</span> of cardinals of all linearly independent sets in <span class="pre">`V`</span>. If <span class="pre">`V`</span> has universe level <span class="pre">`u`</span> then its rank has type <span class="pre">`Cardinal.{u}`</span>.

    #check V -- Type u_2
    #check Module.rank K V -- Cardinal.{u_2}

One can still relate this definition to bases. Indeed there is also a commutative <span class="pre">`max`</span> operation on universe levels, and given two universe levels <span class="pre">`u`</span> and <span class="pre">`v`</span> there is an operation <span class="pre">`Cardinal.lift.{u,`</span>` `<span class="pre">`v}`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Cardinal.{v}`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Cardinal.{max`</span>` `<span class="pre">`v`</span>` `<span class="pre">`u}`</span> that allows to put cardinals in a common universe and state the dimension theorem.

    universe u v -- `u` and `v` will denote universe levels

    variable {ι : Type u} (B : Basis ι K V)
             {ι' : Type v} (B' : Basis ι' K V)

    example : Cardinal.lift.{v, u} (.mk ι) = Cardinal.lift.{u, v} (.mk ι') :=
      mk_eq_mk_of_basis B B'

We can relate the finite dimensional case to this discussion using the coercion from natural numbers to finite cardinals (or more precisely the finite cardinals which live in <span class="pre">`Cardinal.{v}`</span> where <span class="pre">`v`</span> is the universe level of <span class="pre">`V`</span>).

    example [FiniteDimensional K V] :
        (Module.finrank K V : Cardinal) = Module.rank K V :=
      Module.finrank_eq_rank K V
