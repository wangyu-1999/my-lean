<span id="groups-and-ring"></span>

# <span class="section-number">9. </span>Groups and Rings<a href="#groups-and-rings" class="headerlink" title="Link to this heading"></a>

We saw in <a href="C02_Basics.html#proving-identities-in-algebraic-structures" class="reference internal"><span class="std std-numref">Section 2.2</span></a> how to reason about operations in groups and rings. Later, in <a href="C07_Structures.html#section-algebraic-structures" class="reference internal"><span class="std std-numref">Section 7.2</span></a>, we saw how to define abstract algebraic structures, such as group structures, as well as concrete instances such as the ring structure on the Gaussian integers. <a href="C08_Hierarchies.html#hierarchies" class="reference internal"><span class="std std-numref">Chapter 8</span></a> explained how hierarchies of abstract structures are handled in Mathlib.

In this chapter we work with groups and rings in more detail. We won’t be able to cover every aspect of the treatment of these topics in Mathlib, especially since Mathlib is constantly growing. But we will provide entry points to the library and show how the essential concepts are used. There is some overlap with the discussion of <a href="C08_Hierarchies.html#hierarchies" class="reference internal"><span class="std std-numref">Chapter 8</span></a>, but here we will focus on how to use Mathlib instead of the design decisions behind the way the topics are treated. So making sense of some of the examples may require reviewing the background from <a href="C08_Hierarchies.html#hierarchies" class="reference internal"><span class="std std-numref">Chapter 8</span></a>.

<span id="groups"></span>

## <span class="section-number">9.1. </span>Monoids and Groups<a href="#monoids-and-groups" class="headerlink" title="Link to this heading"></a>

<span id="index-1"></span><span id="index-0"></span>

### <span class="section-number">9.1.1. </span>Monoids and their morphisms<a href="#monoids-and-their-morphisms" class="headerlink" title="Link to this heading"></a>

Courses in abstract algebra often start with groups and then progress to rings, fields, and vector spaces. This involves some contortions when discussing multiplication on rings since the multiplication operation does not come from a group structure but many of the proofs carry over verbatim from group theory to this new setting. The most common fix, when doing mathematics with pen and paper, is to leave those proofs as exercises. A less efficient but safer and more formalization-friendly way of proceeding is to use monoids. A *monoid* structure on a type M is an internal composition law that is associative and has a neutral element. Monoids are used primarily to accommodate both groups and the multiplicative structure of rings. But there are also a number of natural examples; for instance, the set of natural numbers equipped with addition forms a monoid.

From a practical point of view, you can mostly ignore monoids when using Mathlib. But you need to know they exist when you are looking for a lemma by browsing Mathlib files. Otherwise, you might end up looking for a statement in the group theory files when it is actually in the found with monoids because it does not require elements to be invertible.

The type of monoid structures on a type <span class="pre">`M`</span> is written <span class="pre">`Monoid`</span>` `<span class="pre">`M`</span>. The function <span class="pre">`Monoid`</span> is a type class so it will almost always appear as an instance implicit argument (in other words, in square brackets). By default, <span class="pre">`Monoid`</span> uses multiplicative notation for the operation; for additive notation use <span class="pre">`AddMonoid`</span> instead. The commutative versions of these structures add the prefix <span class="pre">`Comm`</span> before <span class="pre">`Monoid`</span>.

    example {M : Type*} [Monoid M] (x : M) : x * 1 = x := mul_one x

    example {M : Type*} [AddCommMonoid M] (x y : M) : x + y = y + x := add_comm x y

Note that although <span class="pre">`AddMonoid`</span> is found in the library, it is generally confusing to use additive notation with a non-commutative operation.

The type of morphisms between monoids <span class="pre">`M`</span> and <span class="pre">`N`</span> is called <span class="pre">`MonoidHom`</span>` `<span class="pre">`M`</span>` `<span class="pre">`N`</span> and written <span class="pre">`M`</span>` `<span class="pre">`→*`</span>` `<span class="pre">`N`</span>. Lean will automatically see such a morphism as a function from <span class="pre">`M`</span> to <span class="pre">`N`</span> when we apply it to elements of <span class="pre">`M`</span>. The additive version is called <span class="pre">`AddMonoidHom`</span> and written <span class="pre">`M`</span>` `<span class="pre">`→+`</span>` `<span class="pre">`N`</span>.

    example {M N : Type*} [Monoid M] [Monoid N] (x y : M) (f : M →* N) : f (x * y) = f x * f y :=
      f.map_mul x y

    example {M N : Type*} [AddMonoid M] [AddMonoid N] (f : M →+ N) : f 0 = 0 :=
      f.map_zero

These morphisms are bundled maps, i.e. they package together a map and some of its properties. Remember that <a href="C08_Hierarchies.html#section-hierarchies-morphisms" class="reference internal"><span class="std std-numref">Section 8.2</span></a> explains bundled maps; here we simply note the slightly unfortunate consequence that we cannot use ordinary function composition to compose maps. Instead, we need to use <span class="pre">`MonoidHom.comp`</span> and <span class="pre">`AddMonoidHom.comp`</span>.

    example {M N P : Type*} [AddMonoid M] [AddMonoid N] [AddMonoid P]
        (f : M →+ N) (g : N →+ P) : M →+ P := g.comp f

### <span class="section-number">9.1.2. </span>Groups and their morphisms<a href="#groups-and-their-morphisms" class="headerlink" title="Link to this heading"></a>

We will have much more to say about groups, which are monoids with the extra property that every element has an inverse.

    example {G : Type*} [Group G] (x : G) : x * x⁻¹ = 1 := mul_inv_cancel x

Similar to the <span class="pre">`ring`</span> tactic that we saw earlier, there is a <span class="pre">`group`</span> tactic that proves any identity that holds in any group. (Equivalently, it proves the identities that hold in free groups.)

    example {G : Type*} [Group G] (x y z : G) : x * (y * z) * (x * z)⁻¹ * (x * y * x⁻¹)⁻¹ = 1 := by
      group

There is also a tactic for identities in commutative additive groups called <span class="pre">`abel`</span>.

    example {G : Type*} [AddCommGroup G] (x y z : G) : z + x + (y - z - x) = y := by
      abel

Interestingly, a group morphism is nothing more than a monoid morphism between groups. So we can copy and paste one of our earlier examples, replacing <span class="pre">`Monoid`</span> with <span class="pre">`Group`</span>.

    example {G H : Type*} [Group G] [Group H] (x y : G) (f : G →* H) : f (x * y) = f x * f y :=
      f.map_mul x y

Of course we do get some new properties, such as this one:

    example {G H : Type*} [Group G] [Group H] (x : G) (f : G →* H) : f (x⁻¹) = (f x)⁻¹ :=
      f.map_inv x

You may be worried that constructing group morphisms will require us to do unnecessary work since the definition of monoid morphism enforces that neutral elements are sent to neutral elements while this is automatic in the case of group morphisms. In practice the extra work is not hard, but, to avoid it, there is a function building a group morphism from a function between groups that is compatible with the composition laws.

    example {G H : Type*} [Group G] [Group H] (f : G → H) (h : ∀ x y, f (x * y) = f x * f y) :
        G →* H :=
      MonoidHom.mk' f h

There is also a type <span class="pre">`MulEquiv`</span> of group (or monoid) isomorphisms denoted by <span class="pre">`≃*`</span> (and <span class="pre">`AddEquiv`</span> denoted by <span class="pre">`≃+`</span> in additive notation). The inverse of <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`G`</span>` `<span class="pre">`≃*`</span>` `<span class="pre">`H`</span> is <span class="pre">`MulEquiv.symm`</span>` `<span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`H`</span>` `<span class="pre">`≃*`</span>` `<span class="pre">`G`</span>, composition of <span class="pre">`f`</span> and <span class="pre">`g`</span> is <span class="pre">`MulEquiv.trans`</span>` `<span class="pre">`f`</span>` `<span class="pre">`g`</span>, and the identity isomorphism of <span class="pre">`G`</span> is <span class="pre">`M̀ulEquiv.refl`</span>` `<span class="pre">`G`</span>. Using anonymous projector notation, the first two can be written <span class="pre">`f.symm`</span> and <span class="pre">`f.trans`</span>` `<span class="pre">`g`</span> respectively. Elements of this type are automatically coerced to morphisms and functions when necessary.

    example {G H : Type*} [Group G] [Group H] (f : G ≃* H) :
        f.trans f.symm = MulEquiv.refl G :=
      f.self_trans_symm

One can use <span class="pre">`MulEquiv.ofBijective`</span> to build an isomorphism from a bijective morphism. Doing so makes the inverse function noncomputable.

    noncomputable example {G H : Type*} [Group G] [Group H]
        (f : G →* H) (h : Function.Bijective f) :
        G ≃* H :=
      MulEquiv.ofBijective f h

### <span class="section-number">9.1.3. </span>Subgroups<a href="#subgroups" class="headerlink" title="Link to this heading"></a>

Just as group morphisms are bundled, a subgroup of <span class="pre">`G`</span> is also a bundled structure consisting of a set in <span class="pre">`G`</span> with the relevant closure properties.

    example {G : Type*} [Group G] (H : Subgroup G) {x y : G} (hx : x ∈ H) (hy : y ∈ H) :
        x * y ∈ H :=
      H.mul_mem hx hy

    example {G : Type*} [Group G] (H : Subgroup G) {x : G} (hx : x ∈ H) :
        x⁻¹ ∈ H :=
      H.inv_mem hx

In the example above, it is important to understand that <span class="pre">`Subgroup`</span>` `<span class="pre">`G`</span> is the type of subgroups of <span class="pre">`G`</span>, rather than a predicate <span class="pre">`IsSubgroup`</span>` `<span class="pre">`H`</span> where <span class="pre">`H`</span> is an element of <span class="pre">`Set`</span>` `<span class="pre">`G`</span>. <span class="pre">`Subgroup`</span>` `<span class="pre">`G`</span> is endowed with a coercion to <span class="pre">`Set`</span>` `<span class="pre">`G`</span> and a membership predicate on <span class="pre">`G`</span>. See <a href="C08_Hierarchies.html#section-hierarchies-subobjects" class="reference internal"><span class="std std-numref">Section 8.3</span></a> for an explanation of how and why this is done.

Of course, two subgroups are the same if and only if they have the same elements. This fact is registered for use with the <span class="pre">`ext`</span> tactic, which can be used to prove two subgroups are equal in the same way it is used to prove that two sets are equal.

To state and prove, for example, that <span class="pre">`ℤ`</span> is an additive subgroup of <span class="pre">`ℚ`</span>, what we really want is to construct a term of type <span class="pre">`AddSubgroup`</span>` `<span class="pre">`ℚ`</span> whose projection to <span class="pre">`Set`</span>` `<span class="pre">`ℚ`</span> is <span class="pre">`ℤ`</span>, or, more precisely, the image of <span class="pre">`ℤ`</span> in <span class="pre">`ℚ`</span>.

    example : AddSubgroup ℚ where
      carrier := Set.range ((↑) : ℤ → ℚ)
      add_mem' := by
        rintro _ _ ⟨n, rfl⟩ ⟨m, rfl⟩
        use n + m
        simp
      zero_mem' := by
        use 0
        simp
      neg_mem' := by
        rintro _ ⟨n, rfl⟩
        use -n
        simp

Using type classes, Mathlib knows that a subgroup of a group inherits a group structure.

    example {G : Type*} [Group G] (H : Subgroup G) : Group H := inferInstance

This example is subtle. The object <span class="pre">`H`</span> is not a type, but Lean automatically coerces it to a type by interpreting it as a subtype of <span class="pre">`G`</span>. So the above example can be restated more explicitly as:

    example {G : Type*} [Group G] (H : Subgroup G) : Group {x : G // x ∈ H} := inferInstance

An important benefit of having a type <span class="pre">`Subgroup`</span>` `<span class="pre">`G`</span> instead of a predicate <span class="pre">`IsSubgroup`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`G`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Prop`</span> is that one can easily endow <span class="pre">`Subgroup`</span>` `<span class="pre">`G`</span> with additional structure. Importantly, it has the structure of a complete lattice structure with respect to inclusion. For instance, instead of having a lemma stating that an intersection of two subgroups of <span class="pre">`G`</span> is again a subgroup, we have used the lattice operation <span class="pre">`⊓`</span> to construct the intersection. We can then apply arbitrary lemmas about lattices to the construction.

Let us check that the set underlying the infimum of two subgroups is indeed, by definition, their intersection.

    example {G : Type*} [Group G] (H H' : Subgroup G) :
        ((H ⊓ H' : Subgroup G) : Set G) = (H : Set G) ∩ (H' : Set G) := rfl

It may look strange to have a different notation for what amounts to the intersection of the underlying sets, but the correspondence does not carry over to the supremum operation and set union, since a union of subgroups is not, in general, a subgroup. Instead one needs to use the subgroup generated by the union, which is done using <span class="pre">`Subgroup.closure`</span>.

    example {G : Type*} [Group G] (H H' : Subgroup G) :
        ((H ⊔ H' : Subgroup G) : Set G) = Subgroup.closure ((H : Set G) ∪ (H' : Set G)) := by
      rw [Subgroup.sup_eq_closure]

Another subtlety is that <span class="pre">`G`</span> itself does not have type <span class="pre">`Subgroup`</span>` `<span class="pre">`G`</span>, so we need a way to talk about <span class="pre">`G`</span> seen as a subgroup of <span class="pre">`G`</span>. This is also provided by the lattice structure: the full subgroup is the top element of this lattice.

    example {G : Type*} [Group G] (x : G) : x ∈ (⊤ : Subgroup G) := trivial

Similarly the bottom element of this lattice is the subgroup whose only element is the neutral element.

    example {G : Type*} [Group G] (x : G) : x ∈ (⊥ : Subgroup G) ↔ x = 1 := Subgroup.mem_bot

As an exercise in manipulating groups and subgroups, you can define the conjugate of a subgroup by an element of the ambient group.

    def conjugate {G : Type*} [Group G] (x : G) (H : Subgroup G) : Subgroup G where
      carrier := {a : G | ∃ h, h ∈ H ∧ a = x * h * x⁻¹}
      one_mem' := by
        dsimp
        sorry
      inv_mem' := by
        dsimp
        sorry
      mul_mem' := by
        dsimp
        sorry

Tying the previous two topics together, one can push forward and pull back subgroups using group morphisms. The naming convention in Mathlib is to call those operations <span class="pre">`map`</span> and <span class="pre">`comap`</span>. These are not the common mathematical terms, but they have the advantage of being shorter than “pushforward” and “direct image.”

    example {G H : Type*} [Group G] [Group H] (G' : Subgroup G) (f : G →* H) : Subgroup H :=
      Subgroup.map f G'

    example {G H : Type*} [Group G] [Group H] (H' : Subgroup H) (f : G →* H) : Subgroup G :=
      Subgroup.comap f H'

    #check Subgroup.mem_map
    #check Subgroup.mem_comap

In particular, the preimage of the bottom subgroup under a morphism <span class="pre">`f`</span> is a subgroup called the *kernel* of <span class="pre">`f`</span>, and the range of <span class="pre">`f`</span> is also a subgroup.

    example {G H : Type*} [Group G] [Group H] (f : G →* H) (g : G) :
        g ∈ MonoidHom.ker f ↔ f g = 1 :=
      f.mem_ker

    example {G H : Type*} [Group G] [Group H] (f : G →* H) (h : H) :
        h ∈ MonoidHom.range f ↔ ∃ g : G, f g = h :=
      f.mem_range

As exercises in manipulating group morphisms and subgroups, let us prove some elementary properties. They are already proved in Mathlib, so do not use <span class="pre">`exact?`</span> too quickly if you want to benefit from these exercises.

    section exercises
    variable {G H : Type*} [Group G] [Group H]

    open Subgroup

    example (φ : G →* H) (S T : Subgroup H) (hST : S ≤ T) : comap φ S ≤ comap φ T := by
      sorry

    example (φ : G →* H) (S T : Subgroup G) (hST : S ≤ T) : map φ S ≤ map φ T := by
      sorry

    variable {K : Type*} [Group K]

    -- Remember you can use the `ext` tactic to prove an equality of subgroups.
    example (φ : G →* H) (ψ : H →* K) (U : Subgroup K) :
        comap (ψ.comp φ) U = comap φ (comap ψ U) := by
      sorry

    -- Pushing a subgroup along one homomorphism and then another is equal to
    -- pushing it forward along the composite of the homomorphisms.
    example (φ : G →* H) (ψ : H →* K) (S : Subgroup G) :
        map (ψ.comp φ) S = map ψ (S.map φ) := by
      sorry

    end exercises

Let us finish this introduction to subgroups in Mathlib with two very classical results. Lagrange theorem states the cardinality of a subgroup of a finite group divides the cardinality of the group. Sylow’s first theorem is a famous partial converse to Lagrange’s theorem.

While this corner of Mathlib is partly set up to allow computation, we can tell Lean to use nonconstructive logic anyway using the following <span class="pre">`open`</span>` `<span class="pre">`scoped`</span> command.

    open scoped Classical


    example {G : Type*} [Group G] (G' : Subgroup G) : Nat.card G' ∣ Nat.card G :=
      ⟨G'.index, mul_comm G'.index _ ▸ G'.index_mul_card.symm⟩

    open Subgroup

    example {G : Type*} [Group G] [Finite G] (p : ℕ) {n : ℕ} [Fact p.Prime]
        (hdvd : p ^ n ∣ Nat.card G) : ∃ K : Subgroup G, Nat.card K = p ^ n :=
      Sylow.exists_subgroup_card_pow_prime p hdvd

The next two exercises derive a corollary of Lagrange’s lemma. (This is also already in Mathlib, so do not use <span class="pre">`exact?`</span> too quickly.)

    lemma eq_bot_iff_card {G : Type*} [Group G] {H : Subgroup G} :
        H = ⊥ ↔ Nat.card H = 1 := by
      suffices (∀ x ∈ H, x = 1) ↔ ∃ x ∈ H, ∀ a ∈ H, a = x by
        simpa [eq_bot_iff_forall, Nat.card_eq_one_iff_exists]
      sorry

    #check card_dvd_of_le

    lemma inf_bot_of_coprime {G : Type*} [Group G] (H K : Subgroup G)
        (h : (Nat.card H).Coprime (Nat.card K)) : H ⊓ K = ⊥ := by
      sorry

### <span class="section-number">9.1.4. </span>Concrete groups<a href="#concrete-groups" class="headerlink" title="Link to this heading"></a>

One can also manipulate concrete groups in Mathlib, although this is typically more complicated than working with the abstract theory. For instance, given any type <span class="pre">`X`</span>, the group of permutations of <span class="pre">`X`</span> is <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`X`</span>. In particular the symmetric group <span class="math notranslate nohighlight">\\\mathfrak{S}\_n\\</span> is <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`(Fin`</span>` `<span class="pre">`n)`</span>. One can state abstract results about this group, for instance saying that <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`X`</span> is generated by cycles if <span class="pre">`X`</span> is finite.

    open Equiv

    example {X : Type*} [Finite X] : Subgroup.closure {σ : Perm X | Perm.IsCycle σ} = ⊤ :=
      Perm.closure_isCycle

One can be fully concrete and compute actual products of cycles. Below we use the <span class="pre">`#simp`</span> command, which calls the <span class="pre">`simp`</span> tactic on a given expression. The notation <span class="pre">`c[]`</span> is used to define a cyclic permutation. In the example, the result is a permutation of <span class="pre">`ℕ`</span>. One could use a type ascription such as <span class="pre">`(1`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Fin`</span>` `<span class="pre">`5)`</span> on the first number appearing to make it a computation in <span class="pre">`Perm`</span>` `<span class="pre">`(Fin`</span>` `<span class="pre">`5)`</span>.

    #simp [mul_assoc] c[1, 2, 3] * c[2, 3, 4]

Another way to work with concrete groups is to use free groups and group presentations. The free group on a type <span class="pre">`α`</span> is <span class="pre">`FreeGroup`</span>` `<span class="pre">`α`</span> and the inclusion map is <span class="pre">`FreeGroup.of`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span>` `<span class="pre">`→`</span>` `<span class="pre">`FreeGroup`</span>` `<span class="pre">`α`</span>. For instance let us define a type <span class="pre">`S`</span> with three elements denoted by <span class="pre">`a`</span>, <span class="pre">`b`</span> and <span class="pre">`c`</span>, and the element <span class="pre">`ab⁻¹`</span> of the corresponding free group.

    section FreeGroup

    inductive S | a | b | c

    open S

    def myElement : FreeGroup S := (.of a) * (.of b)⁻¹

Note that we gave the expected type of the definition so that Lean knows that <span class="pre">`.of`</span> means <span class="pre">`FreeGroup.of`</span>.

The universal property of free groups is embodied as the equivalence <span class="pre">`FreeGroup.lift`</span>. For example, let us define the group morphism from <span class="pre">`FreeGroup`</span>` `<span class="pre">`S`</span> to <span class="pre">`Perm`</span>` `<span class="pre">`(Fin`</span>` `<span class="pre">`5)`</span> that sends <span class="pre">`a`</span> to <span class="pre">`c[1,`</span>` `<span class="pre">`2,`</span>` `<span class="pre">`3]`</span>, <span class="pre">`b`</span> to <span class="pre">`c[2,`</span>` `<span class="pre">`3,`</span>` `<span class="pre">`1]`</span>, and <span class="pre">`c`</span> to <span class="pre">`c[2,`</span>` `<span class="pre">`3]`</span>,

    def myMorphism : FreeGroup S →* Perm (Fin 5) :=
      FreeGroup.lift fun | .a => c[1, 2, 3]
                         | .b => c[2, 3, 1]
                         | .c => c[2, 3]

As a last concrete example, let us see how to define a group generated by a single element whose cube is one (so that group will be isomorphic to <span class="math notranslate nohighlight">\\\mathbb{Z}/3\\</span>) and build a morphism from that group to <span class="pre">`Perm`</span>` `<span class="pre">`(Fin`</span>` `<span class="pre">`5)`</span>.

As a type with exactly one element, we will use <span class="pre">`Unit`</span> whose only element is denoted by <span class="pre">`()`</span>. The function <span class="pre">`PresentedGroup`</span> takes a set of relations, i.e. a set of elements of some free group, and returns a group that is this free group quotiented by a normal subgroup generated by relations. (We will see how to handle more general quotients in <a href="#quotient-groups" class="reference internal"><span class="std std-numref">Section 9.1.6</span></a>.) Since we somehow hide this behind a definition, we use <span class="pre">`deriving`</span>` `<span class="pre">`Group`</span> to force creation of a group instance on <span class="pre">`myGroup`</span>.

    def myGroup := PresentedGroup {.of () ^ 3} deriving Group

The universal property of presented groups ensures that morphisms out of this group can be built from functions that send the relations to the neutral element of the target group. So we need such a function and a proof that the condition holds. Then we can feed this proof to <span class="pre">`PresentedGroup.toGroup`</span> to get the desired group morphism.

    def myMap : Unit → Perm (Fin 5)
    | () => c[1, 2, 3]

    lemma compat_myMap :
        ∀ r ∈ ({.of () ^ 3} : Set (FreeGroup Unit)), FreeGroup.lift myMap r = 1 := by
      rintro _ rfl
      simp
      decide

    def myNewMorphism : myGroup →* Perm (Fin 5) := PresentedGroup.toGroup compat_myMap

    end FreeGroup

### <span class="section-number">9.1.5. </span>Group actions<a href="#group-actions" class="headerlink" title="Link to this heading"></a>

One important way that group theory interacts with the rest of mathematics is through the use of group actions. An action of a group <span class="pre">`G`</span> on some type <span class="pre">`X`</span> is nothing more than a morphism from <span class="pre">`G`</span> to <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`X`</span>. So in a sense group actions are already covered by the previous discussion. But we don’t want to carry this morphism around; instead, we want it to be inferred automatically by Lean as much as possible. So we have a type class for this, which is <span class="pre">`MulAction`</span>` `<span class="pre">`G`</span>` `<span class="pre">`X`</span>. The downside of this setup is that having multiple actions of the same group on the same type requires some contortions, such as defining type synonyms, each of which carries different type class instances.

This allows us in particular to use <span class="pre">`g`</span>` `<span class="pre">`•`</span>` `<span class="pre">`x`</span> to denote the action of a group element <span class="pre">`g`</span> on a point <span class="pre">`x`</span>.

    noncomputable section GroupActions

    example {G X : Type*} [Group G] [MulAction G X] (g g': G) (x : X) :
        g • (g' • x) = (g * g') • x :=
      (mul_smul g g' x).symm

There is also a version for additive group called <span class="pre">`AddAction`</span>, where the action is denoted by <span class="pre">`+ᵥ`</span>. This is used for instance in the definition of affine spaces.

    example {G X : Type*} [AddGroup G] [AddAction G X] (g g' : G) (x : X) :
        g +ᵥ (g' +ᵥ x) = (g + g') +ᵥ x :=
      (add_vadd g g' x).symm

The underlying group morphism is called <span class="pre">`MulAction.toPermHom`</span>.

    open MulAction

    example {G X : Type*} [Group G] [MulAction G X] : G →* Equiv.Perm X :=
      toPermHom G X

As an illustration let us see how to define the Cayley isomorphism embedding of any group <span class="pre">`G`</span> into a permutation group, namely <span class="pre">`Perm`</span>` `<span class="pre">`G`</span>.

    def CayleyIsoMorphism (G : Type*) [Group G] : G ≃* (toPermHom G G).range :=
      Equiv.Perm.subgroupOfMulAction G G

Note that nothing before the above definition required having a group rather than a monoid (or any type endowed with a multiplication operation really).

The group condition really enters the picture when we will want to partition <span class="pre">`X`</span> into orbits. The corresponding equivalence relation on <span class="pre">`X`</span> is called <span class="pre">`MulAction.orbitRel`</span>. It is not declared as a global instance.

    example {G X : Type*} [Group G] [MulAction G X] : Setoid X := orbitRel G X

Using this we can state that <span class="pre">`X`</span> is partitioned into orbits under the action of <span class="pre">`G`</span>. More precisely, we get a bijection between <span class="pre">`X`</span> and the dependent product <span class="pre">`(ω`</span>` `<span class="pre">`:`</span>` `<span class="pre">`orbitRel.Quotient`</span>` `<span class="pre">`G`</span>` `<span class="pre">`X)`</span>` `<span class="pre">`×`</span>` `<span class="pre">`(orbit`</span>` `<span class="pre">`G`</span>` `<span class="pre">`(Quotient.out'`</span>` `<span class="pre">`ω))`</span> where <span class="pre">`Quotient.out'`</span>` `<span class="pre">`ω`</span> simply chooses an element that projects to <span class="pre">`ω`</span>. Recall that elements of this dependent product are pairs <span class="pre">`⟨ω,`</span>` `<span class="pre">`x⟩`</span> where the type <span class="pre">`orbit`</span>` `<span class="pre">`G`</span>` `<span class="pre">`(Quotient.out'`</span>` `<span class="pre">`ω)`</span> of <span class="pre">`x`</span> depends on <span class="pre">`ω`</span>.

    example {G X : Type*} [Group G] [MulAction G X] :
        X ≃ (ω : orbitRel.Quotient G X) × (orbit G (Quotient.out ω)) :=
      MulAction.selfEquivSigmaOrbits G X

In particular, when X is finite, this can be combined with <span class="pre">`Fintype.card_congr`</span> and <span class="pre">`Fintype.card_sigma`</span> to deduce that the cardinality of <span class="pre">`X`</span> is the sum of the cardinalities of the orbits. Furthermore, the orbits are in bijection with the quotient of <span class="pre">`G`</span> under the action of the stabilizers by left translation. This action of a subgroup by left-translation is used to define quotients of a group by a subgroup with notation / so we can use the following concise statement.

    example {G X : Type*} [Group G] [MulAction G X] (x : X) :
        orbit G x ≃ G ⧸ stabilizer G x :=
      MulAction.orbitEquivQuotientStabilizer G x

An important special case of combining the above two results is when <span class="pre">`X`</span> is a group <span class="pre">`G`</span> equipped with the action of a subgroup <span class="pre">`H`</span> by translation. In this case all stabilizers are trivial so every orbit is in bijection with <span class="pre">`H`</span> and we get:

    example {G : Type*} [Group G] (H : Subgroup G) : G ≃ (G ⧸ H) × H :=
      groupEquivQuotientProdSubgroup

This is the conceptual variant of the version of Lagrange theorem that we saw above. Note this version makes no finiteness assumption.

As an exercise for this section, let us build the action of a group on its subgroup by conjugation, using our definition of <span class="pre">`conjugate`</span> from a previous exercise.

    variable {G : Type*} [Group G]

    lemma conjugate_one (H : Subgroup G) : conjugate 1 H = H := by
      sorry

    instance : MulAction G (Subgroup G) where
      smul := conjugate
      one_smul := by
        sorry
      mul_smul := by
        sorry

    end GroupActions

<span id="id1"></span>

### <span class="section-number">9.1.6. </span>Quotient groups<a href="#quotient-groups" class="headerlink" title="Link to this heading"></a>

In the above discussion of subgroups acting on groups, we saw the quotient <span class="pre">`G`</span>` `<span class="pre">`⧸`</span>` `<span class="pre">`H`</span> appear. In general this is only a type. It can be endowed with a group structure such that the quotient map is a group morphism if and only if <span class="pre">`H`</span> is a normal subgroup (and this group structure is then unique).

The normality assumption is a type class <span class="pre">`Subgroup.Normal`</span> so that type class inference can use it to derive the group structure on the quotient.

    noncomputable section QuotientGroup

    example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : Group (G ⧸ H) := inferInstance

    example {G : Type*} [Group G] (H : Subgroup G) [H.Normal] : G →* G ⧸ H :=
      QuotientGroup.mk' H

The universal property of quotient groups is accessed through <span class="pre">`QuotientGroup.lift`</span>: a group morphism <span class="pre">`φ`</span> descends to <span class="pre">`G`</span>` `<span class="pre">`⧸`</span>` `<span class="pre">`N`</span> as soon as its kernel contains <span class="pre">`N`</span>.

    example {G : Type*} [Group G] (N : Subgroup G) [N.Normal] {M : Type*}
        [Group M] (φ : G →* M) (h : N ≤ MonoidHom.ker φ) : G ⧸ N →* M :=
      QuotientGroup.lift N φ h

The fact that the target group is called <span class="pre">`M`</span> is the above snippet is a clue that having a monoid structure on <span class="pre">`M`</span> would be enough.

An important special case is when <span class="pre">`N`</span>` `<span class="pre">`=`</span>` `<span class="pre">`ker`</span>` `<span class="pre">`φ`</span>. In that case the descended morphism is injective and we get a group isomorphism onto its image. This result is often called the first isomorphism theorem.

    example {G : Type*} [Group G] {M : Type*} [Group M] (φ : G →* M) :
        G ⧸ MonoidHom.ker φ →* MonoidHom.range φ :=
      QuotientGroup.quotientKerEquivRange φ

Applying the universal property to a composition of a morphism <span class="pre">`φ`</span>` `<span class="pre">`:`</span>` `<span class="pre">`G`</span>` `<span class="pre">`→*`</span>` `<span class="pre">`G'`</span> with a quotient group projection <span class="pre">`Quotient.mk'`</span>` `<span class="pre">`N'`</span>, we can also aim for a morphism from <span class="pre">`G`</span>` `<span class="pre">`⧸`</span>` `<span class="pre">`N`</span> to <span class="pre">`G'`</span>` `<span class="pre">`⧸`</span>` `<span class="pre">`N'`</span>. The condition required on <span class="pre">`φ`</span> is usually formulated by saying “<span class="pre">`φ`</span> should send <span class="pre">`N`</span> inside <span class="pre">`N'`</span>.” But this is equivalent to asking that <span class="pre">`φ`</span> should pull <span class="pre">`N'`</span> back over <span class="pre">`N`</span>, and the latter condition is nicer to work with since the definition of pullback does not involve an existential quantifier.

    example {G G': Type*} [Group G] [Group G']
        {N : Subgroup G} [N.Normal] {N' : Subgroup G'} [N'.Normal]
        {φ : G →* G'} (h : N ≤ Subgroup.comap φ N') : G ⧸ N →* G' ⧸ N':=
      QuotientGroup.map N N' φ h

One subtle point to keep in mind is that the type <span class="pre">`G`</span>` `<span class="pre">`⧸`</span>` `<span class="pre">`N`</span> really depends on <span class="pre">`N`</span> (up to definitional equality), so having a proof that two normal subgroups <span class="pre">`N`</span> and <span class="pre">`M`</span> are equal is not enough to make the corresponding quotients equal. However the universal properties does give an isomorphism in this case.

    example {G : Type*} [Group G] {M N : Subgroup G} [M.Normal]
        [N.Normal] (h : M = N) : G ⧸ M ≃* G ⧸ N := QuotientGroup.quotientMulEquivOfEq h

As a final series of exercises for this section, we will prove that if <span class="pre">`H`</span> and <span class="pre">`K`</span> are disjoint normal subgroups of a finite group <span class="pre">`G`</span> such that the product of their cardinalities is equal to the cardinality of <span class="pre">`G`</span> then <span class="pre">`G`</span> is isomorphic to <span class="pre">`H`</span>` `<span class="pre">`×`</span>` `<span class="pre">`K`</span>. Recall that disjoint in this context means <span class="pre">`H`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`K`</span>` `<span class="pre">`=`</span>` `<span class="pre">`⊥`</span>.

We start with playing a bit with Lagrange’s lemma, without assuming the subgroups are normal or disjoint.

    section
    variable {G : Type*} [Group G] {H K : Subgroup G}

    open MonoidHom

    #check Nat.card_pos -- The nonempty argument will be automatically inferred for subgroups
    #check Subgroup.index_eq_card
    #check Subgroup.index_mul_card
    #check Nat.eq_of_mul_eq_mul_right

    lemma aux_card_eq [Finite G] (h' : Nat.card G = Nat.card H * Nat.card K) :
        Nat.card (G ⧸ H) = Nat.card K := by
      sorry

From now on, we assume that our subgroups are normal and disjoint, and we assume the cardinality condition. Now we construct the first building block of the desired isomorphism.

    variable [H.Normal] [K.Normal] [Fintype G] (h : Disjoint H K)
      (h' : Nat.card G = Nat.card H * Nat.card K)

    #check Nat.bijective_iff_injective_and_card
    #check ker_eq_bot_iff
    #check restrict
    #check ker_restrict

    def iso₁ : K ≃* G ⧸ H := by
      sorry

Now we can define our second building block. We will need <span class="pre">`MonoidHom.prod`</span>, which builds a morphism from <span class="pre">`G₀`</span> to <span class="pre">`G₁`</span>` `<span class="pre">`×`</span>` `<span class="pre">`G₂`</span> out of morphisms from <span class="pre">`G₀`</span> to <span class="pre">`G₁`</span> and <span class="pre">`G₂`</span>.

    def iso₂ : G ≃* (G ⧸ K) × (G ⧸ H) := by
      sorry

We are ready to put all pieces together.

    #check MulEquiv.prodCongr

    def finalIso : G ≃* H × K :=
      sorry

<span id="id2"></span>

## <span class="section-number">9.2. </span>Rings<a href="#rings" class="headerlink" title="Link to this heading"></a>

<span id="index-4"></span>

### <span class="section-number">9.2.1. </span>Rings, their units, morphisms and subrings<a href="#rings-their-units-morphisms-and-subrings" class="headerlink" title="Link to this heading"></a>

The type of ring structures on a type <span class="pre">`R`</span> is <span class="pre">`Ring`</span>` `<span class="pre">`R`</span>. The variant where multiplication is assumed to be commutative is <span class="pre">`CommRing`</span>` `<span class="pre">`R`</span>. We have already seen that the <span class="pre">`ring`</span> tactic will prove any equality that follows from the axioms of a commutative ring.

    example {R : Type*} [CommRing R] (x y : R) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

More exotic variants do not require that the addition on <span class="pre">`R`</span> forms a group but only an additive monoid. The corresponding type classes are <span class="pre">`Semiring`</span>` `<span class="pre">`R`</span> and <span class="pre">`CommSemiring`</span>` `<span class="pre">`R`</span>. The type of natural numbers is an important instance of <span class="pre">`CommSemiring`</span>` `<span class="pre">`R`</span>, as is any type of functions taking values in the natural numbers. Another important example is the type of ideals in a ring, which will be discussed below. The name of the <span class="pre">`ring`</span> tactic is doubly misleading, since it assumes commutativity but works in semirings as well. In other words, it applies to any <span class="pre">`CommSemiring`</span>.

    example (x y : ℕ) : (x + y) ^ 2 = x ^ 2 + y ^ 2 + 2 * x * y := by ring

There are also versions of the ring and semiring classes that do not assume the existence of a multiplicative unit or the associativity of multiplication. We will not discuss those here.

Some concepts that are traditionally taught in an introduction to ring theory are actually about the underlying multiplicative monoid. A prominent example is the definition of the units of a ring. Every (multiplicative) monoid <span class="pre">`M`</span> has a predicate <span class="pre">`IsUnit`</span>` `<span class="pre">`:`</span>` `<span class="pre">`M`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Prop`</span> asserting existence of a two-sided inverse, a type <span class="pre">`Units`</span>` `<span class="pre">`M`</span> of units with notation <span class="pre">`Mˣ`</span>, and a coercion to <span class="pre">`M`</span>. The type <span class="pre">`Units`</span>` `<span class="pre">`M`</span> bundles an invertible element with its inverse as well as properties than ensure that each is indeed the inverse of the other. This implementation detail is relevant mainly when defining computable functions. In most situations one can use <span class="pre">`IsUnit.unit`</span>` `<span class="pre">`{x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`M}`</span>` `<span class="pre">`:`</span>` `<span class="pre">`IsUnit`</span>` `<span class="pre">`x`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Mˣ`</span> to build a unit. In the commutative case, one also has <span class="pre">`Units.mkOfMulEqOne`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`y`</span>` `<span class="pre">`:`</span>` `<span class="pre">`M)`</span>` `<span class="pre">`:`</span>` `<span class="pre">`x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`1`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Mˣ`</span> which builds <span class="pre">`x`</span> seen as unit.

    example (x : ℤˣ) : x = 1 ∨ x = -1 := Int.units_eq_one_or x

    example {M : Type*} [Monoid M] (x : Mˣ) : (x : M) * x⁻¹ = 1 := Units.mul_inv x

    example {M : Type*} [Monoid M] : Group Mˣ := inferInstance

The type of ring morphisms between two (semi)-rings <span class="pre">`R`</span> and <span class="pre">`S`</span> is <span class="pre">`RingHom`</span>` `<span class="pre">`R`</span>` `<span class="pre">`S`</span>, with notation <span class="pre">`R`</span>` `<span class="pre">`→+*`</span>` `<span class="pre">`S`</span>.

    example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) (x y : R) :
        f (x + y) = f x + f y := f.map_add x y

    example {R S : Type*} [Ring R] [Ring S] (f : R →+* S) : Rˣ →* Sˣ :=
      Units.map f

The isomorphism variant is <span class="pre">`RingEquiv`</span>, with notation <span class="pre">`≃+*`</span>.

As with submonoids and subgroups, there is a <span class="pre">`Subring`</span>` `<span class="pre">`R`</span> type for subrings of a ring <span class="pre">`R`</span>, but this type is a lot less useful than the type of subgroups since one cannot quotient a ring by a subring.

    example {R : Type*} [Ring R] (S : Subring R) : Ring S := inferInstance

Also notice that <span class="pre">`RingHom.range`</span> produces a subring.

### <span class="section-number">9.2.2. </span>Ideals and quotients<a href="#ideals-and-quotients" class="headerlink" title="Link to this heading"></a>

For historical reasons, Mathlib only has a theory of ideals for commutative rings. (The ring library was originally developed to make quick progress toward the foundations of modern algebraic geometry.) So in this section we will work with commutative (semi)rings. Ideals of <span class="pre">`R`</span> are defined as submodules of <span class="pre">`R`</span> seen as <span class="pre">`R`</span>-modules. Modules will be covered later in a chapter on linear algebra, but this implementation detail can mostly be safely ignored since most (but not all) relevant lemmas are restated in the special context of ideals. But anonymous projection notation won’t always work as expected. For instance, one cannot replace <span class="pre">`Ideal.Quotient.mk`</span>` `<span class="pre">`I`</span> by <span class="pre">`I.Quotient.mk`</span> in the snippet below because there are two <span class="pre">`.`</span>s and so it will parse as <span class="pre">`(Ideal.Quotient`</span>` `<span class="pre">`I).mk`</span>; but <span class="pre">`Ideal.Quotient`</span> by itself doesn’t exist.

    example {R : Type*} [CommRing R] (I : Ideal R) : R →+* R ⧸ I :=
      Ideal.Quotient.mk I

    example {R : Type*} [CommRing R] {a : R} {I : Ideal R} :
        Ideal.Quotient.mk I a = 0 ↔ a ∈ I :=
      Ideal.Quotient.eq_zero_iff_mem

The universal property of quotient rings is <span class="pre">`Ideal.Quotient.lift`</span>.

    example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (f : R →+* S)
        (H : I ≤ RingHom.ker f) : R ⧸ I →+* S :=
      Ideal.Quotient.lift I f H

In particular it leads to the first isomorphism theorem for rings.

    example {R S : Type*} [CommRing R] [CommRing S](f : R →+* S) :
        R ⧸ RingHom.ker f ≃+* f.range :=
      RingHom.quotientKerEquivRange f

Ideals form a complete lattice structure with the inclusion relation, as well as a semiring structure. These two structures interact nicely.

    variable {R : Type*} [CommRing R] {I J : Ideal R}

    example : I + J = I ⊔ J := rfl

    example {x : R} : x ∈ I + J ↔ ∃ a ∈ I, ∃ b ∈ J, a + b = x := by
      simp [Submodule.mem_sup]

    example : I * J ≤ J := Ideal.mul_le_left

    example : I * J ≤ I := Ideal.mul_le_right

    example : I * J ≤ I ⊓ J := Ideal.mul_le_inf

One can use ring morphisms to push ideals forward and pull them back using <span class="pre">`Ideal.map`</span> and <span class="pre">`Ideal.comap`</span>, respectively. As usual, the latter is more convenient to use since it does not involve an existential quantifier. This explains why it is used to state the condition that allows us to build morphisms between quotient rings.

    example {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (J : Ideal S) (f : R →+* S)
        (H : I ≤ Ideal.comap f J) : R ⧸ I →+* S ⧸ J :=
      Ideal.quotientMap J f H

One subtle point is that the type <span class="pre">`R`</span>` `<span class="pre">`⧸`</span>` `<span class="pre">`I`</span> really depends on <span class="pre">`I`</span> (up to definitional equality), so having a proof that two ideals <span class="pre">`I`</span> and <span class="pre">`J`</span> are equal is not enough to make the corresponding quotients equal. However, the universal properties do provide an isomorphism in this case.

    example {R : Type*} [CommRing R] {I J : Ideal R} (h : I = J) : R ⧸ I ≃+* R ⧸ J :=
      Ideal.quotEquivOfEq h

We can now present the Chinese remainder isomorphism as an example. Pay attention to the difference between the indexed infimum symbol <span class="pre">`⨅`</span> and the big product of types symbol <span class="pre">`Π`</span>. Depending on your font, those can be pretty hard to distinguish.

    example {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] (f : ι → Ideal R)
        (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
      Ideal.quotientInfRingEquivPiQuotient f hf

The elementary version of the Chinese remainder theorem, a statement about <span class="pre">`ZMod`</span>, can be easily deduced from the previous one:

    open BigOperators PiNotation

    example {ι : Type*} [Fintype ι] (a : ι → ℕ) (coprime : ∀ i j, i ≠ j → (a i).Coprime (a j)) :
        ZMod (∏ i, a i) ≃+* Π i, ZMod (a i) :=
      ZMod.prodEquivPi a coprime

As a series of exercises, we will reprove the Chinese remainder theorem in the general case.

We first need to define the map appearing in the theorem, as a ring morphism, using the universal property of quotient rings.

    variable {ι R : Type*} [CommRing R]
    open Ideal Quotient Function

    #check Pi.ringHom
    #check ker_Pi_Quotient_mk

    /-- The homomorphism from ``R ⧸ ⨅ i, I i`` to ``Π i, R ⧸ I i`` featured in the Chinese
      Remainder Theorem. -/
    def chineseMap (I : ι → Ideal R) : (R ⧸ ⨅ i, I i) →+* Π i, R ⧸ I i :=
      sorry

Make sure the following next two lemmas can be proven by <span class="pre">`rfl`</span>.

    lemma chineseMap_mk (I : ι → Ideal R) (x : R) :
        chineseMap I (Quotient.mk _ x) = fun i : ι ↦ Ideal.Quotient.mk (I i) x :=
      sorry

    lemma chineseMap_mk' (I : ι → Ideal R) (x : R) (i : ι) :
        chineseMap I (mk _ x) i = mk (I i) x :=
      sorry

The next lemma proves the easy half of the Chinese remainder theorem, without any assumption on the family of ideals. The proof is less than one line long.

    #check injective_lift_iff

    lemma chineseMap_inj (I : ι → Ideal R) : Injective (chineseMap I) := by
      sorry

We are now ready for the heart of the theorem, which will show the surjectivity of our <span class="pre">`chineseMap`</span>. First we need to know the different ways one can express the coprimality (also called co-maximality assumption). Only the first two will be needed below.

    #check IsCoprime
    #check isCoprime_iff_add
    #check isCoprime_iff_exists
    #check isCoprime_iff_sup_eq
    #check isCoprime_iff_codisjoint

We take the opportunity to use induction on <span class="pre">`Finset`</span>. Relevant lemmas on <span class="pre">`Finset`</span> are given below. Remember that the <span class="pre">`ring`</span> tactic works for semirings and that the ideals of a ring form a semiring.

    #check Finset.mem_insert_of_mem
    #check Finset.mem_insert_self

    theorem isCoprime_Inf {I : Ideal R} {J : ι → Ideal R} {s : Finset ι}
        (hf : ∀ j ∈ s, IsCoprime I (J j)) : IsCoprime I (⨅ j ∈ s, J j) := by
      classical
      simp_rw [isCoprime_iff_add] at *
      induction s using Finset.induction with
      | empty =>
          simp
      | @insert i s _ hs =>
          rw [Finset.iInf_insert, inf_comm, one_eq_top, eq_top_iff, ← one_eq_top]
          set K := ⨅ j ∈ s, J j
          calc
            1 = I + K                  := sorry
            _ = I + K * (I + J i)      := sorry
            _ = (1 + K) * I + K * J i  := sorry
            _ ≤ I + K ⊓ J i            := sorry

We can now prove surjectivity of the map appearing in the Chinese remainder theorem.

    lemma chineseMap_surj [Fintype ι] {I : ι → Ideal R}
        (hI : ∀ i j, i ≠ j → IsCoprime (I i) (I j)) : Surjective (chineseMap I) := by
      classical
      intro g
      choose f hf using fun i ↦ Ideal.Quotient.mk_surjective (g i)
      have key : ∀ i, ∃ e : R, mk (I i) e = 1 ∧ ∀ j, j ≠ i → mk (I j) e = 0 := by
        intro i
        have hI' : ∀ j ∈ ({i} : Finset ι)ᶜ, IsCoprime (I i) (I j) := by
          sorry
        sorry
      choose e he using key
      use mk _ (∑ i, f i * e i)
      sorry

Now all the pieces come together in the following:

    noncomputable def chineseIso [Fintype ι] (f : ι → Ideal R)
        (hf : ∀ i j, i ≠ j → IsCoprime (f i) (f j)) : (R ⧸ ⨅ i, f i) ≃+* Π i, R ⧸ f i :=
      { Equiv.ofBijective _ ⟨chineseMap_inj f, chineseMap_surj hf⟩,
        chineseMap f with }

### <span class="section-number">9.2.3. </span>Algebras and polynomials<a href="#algebras-and-polynomials" class="headerlink" title="Link to this heading"></a>

Given a commutative (semi)ring <span class="pre">`R`</span>, an *algebra over* <span class="pre">`R`</span> is a semiring <span class="pre">`A`</span> equipped with a ring morphism whose image commutes with every element of <span class="pre">`A`</span>. This is encoded as a type class <span class="pre">`Algebra`</span>` `<span class="pre">`R`</span>` `<span class="pre">`A`</span>. The morphism from <span class="pre">`R`</span> to <span class="pre">`A`</span> is called the structure map and is denoted <span class="pre">`algebraMap`</span>` `<span class="pre">`R`</span>` `<span class="pre">`A`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R`</span>` `<span class="pre">`→+*`</span>` `<span class="pre">`A`</span> in Lean. Multiplication of <span class="pre">`a`</span>` `<span class="pre">`:`</span>` `<span class="pre">`A`</span> by <span class="pre">`algebraMap`</span>` `<span class="pre">`R`</span>` `<span class="pre">`A`</span>` `<span class="pre">`r`</span> for some <span class="pre">`r`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R`</span> is called the scalar multiplication of <span class="pre">`a`</span> by <span class="pre">`r`</span> and denoted by <span class="pre">`r`</span>` `<span class="pre">`•`</span>` `<span class="pre">`a`</span>. Note that this notion of algebra is sometimes called an *associative unital algebra* to emphasize the existence of more general notions of algebra.

The fact that <span class="pre">`algebraMap`</span>` `<span class="pre">`R`</span>` `<span class="pre">`A`</span> is ring morphism packages together a lot of properties of scalar multiplication, such as the following:

    example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
        (r + r') • a = r • a + r' • a :=
      add_smul r r' a

    example {R A : Type*} [CommRing R] [Ring A] [Algebra R A] (r r' : R) (a : A) :
        (r * r') • a = r • r' • a :=
      mul_smul r r' a

The morphisms between two <span class="pre">`R`</span>-algebras <span class="pre">`A`</span> and <span class="pre">`B`</span> are ring morphisms which commute with scalar multiplication by elements of <span class="pre">`R`</span>. They are bundled morphisms with type <span class="pre">`AlgHom`</span>` `<span class="pre">`R`</span>` `<span class="pre">`A`</span>` `<span class="pre">`B`</span>, which is denoted by <span class="pre">`A`</span>` `<span class="pre">`→ₐ[R]`</span>` `<span class="pre">`B`</span>.

Important examples of non-commutative algebras include algebras of endomorphisms and algebras of square matrices, both of which will be covered in the chapter on linear algebra. In this chapter we will discuss one of the most important examples of a commutative algebra, namely, polynomial algebras.

The algebra of univariate polynomials with coefficients in <span class="pre">`R`</span> is called <span class="pre">`Polynomial`</span>` `<span class="pre">`R`</span>, which can be written as <span class="pre">`R[X]`</span> as soon as one opens the <span class="pre">`Polynomial`</span> namespace. The algebra structure map from <span class="pre">`R`</span> to <span class="pre">`R[X]`</span> is denoted by <span class="pre">`C`</span>, which stands for “constant” since the corresponding polynomial functions are always constant. The indeterminate is denoted by <span class="pre">`X`</span>.

    open Polynomial

    example {R : Type*} [CommRing R] : R[X] := X

    example {R : Type*} [CommRing R] (r : R) := X - C r

In the first example above, it is crucial that we give Lean the expected type since it cannot be determined from the body of the definition. In the second example, the target polynomial algebra can be inferred from our use of <span class="pre">`C`</span>` `<span class="pre">`r`</span> since the type of <span class="pre">`r`</span> is known.

Because <span class="pre">`C`</span> is a ring morphism from <span class="pre">`R`</span> to <span class="pre">`R[X]`</span>, we can use all ring morphisms lemmas such as <span class="pre">`map_zero`</span>, <span class="pre">`map_one`</span>, <span class="pre">`map_mul`</span>, and <span class="pre">`map_pow`</span> before computing in the ring <span class="pre">`R[X]`</span>. For example:

    example {R : Type*} [CommRing R] (r : R) : (X + C r) * (X - C r) = X ^ 2 - C (r ^ 2) := by
      rw [C.map_pow]
      ring

You can access coefficients using <span class="pre">`Polynomial.coeff`</span>

    example {R : Type*} [CommRing R] (r:R) : (C r).coeff 0 = r := by simp

    example {R : Type*} [CommRing R] : (X ^ 2 + 2 * X + C 3 : R[X]).coeff 1 = 2 := by simp

Defining the degree of a polynomial is always tricky because of the special case of the zero polynomial. Mathlib has two variants: <span class="pre">`Polynomial.natDegree`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R[X]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℕ`</span> assigns degree <span class="pre">`0`</span> to the zero polynomial, and <span class="pre">`Polynomial.degree`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R[X]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`WithBot`</span>` `<span class="pre">`ℕ`</span> assigns <span class="pre">`⊥`</span>. In the latter, <span class="pre">`WithBot`</span>` `<span class="pre">`ℕ`</span> can be seen as <span class="pre">`ℕ`</span>` `<span class="pre">`∪`</span>` `<span class="pre">`{-∞}`</span>, except that <span class="pre">`-∞`</span> is denoted <span class="pre">`⊥`</span>, the same symbol as the bottom element in a complete lattice. This special value is used as the degree of the zero polynomial, and it is absorbent for addition. (It is almost absorbent for multiplication, except that <span class="pre">`⊥`</span>` `<span class="pre">`*`</span>` `<span class="pre">`0`</span>` `<span class="pre">`=`</span>` `<span class="pre">`0`</span>.)

Morally speaking, the <span class="pre">`degree`</span> version is the correct one. For instance, it allows us to state the expected formula for the degree of a product (assuming the base ring has no zero divisor).

    example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
        degree (p * q) = degree p + degree q :=
      Polynomial.degree_mul

Whereas the version for <span class="pre">`natDegree`</span> needs to assume non-zero polynomials.

    example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
        natDegree (p * q) = natDegree p + natDegree q :=
      Polynomial.natDegree_mul hp hq

However, <span class="pre">`ℕ`</span> is much nicer to use than <span class="pre">`WithBot`</span>` `<span class="pre">`ℕ`</span>, so Mathlib makes both versions available and provides lemmas to convert between them. Also, <span class="pre">`natDegree`</span> is the more convenient definition to use when computing the degree of a composition. Composition of polynomial is <span class="pre">`Polynomial.comp`</span> and we have:

    example {R : Type*} [Semiring R] [NoZeroDivisors R] {p q : R[X]} :
        natDegree (comp p q) = natDegree p * natDegree q :=
      Polynomial.natDegree_comp

Polynomials give rise to polynomial functions: any polynomial can be evaluated on <span class="pre">`R`</span> using <span class="pre">`Polynomial.eval`</span>.

    example {R : Type*} [CommRing R] (P: R[X]) (x : R) := P.eval x

    example {R : Type*} [CommRing R] (r : R) : (X - C r).eval r = 0 := by simp

In particular, there is a predicate, <span class="pre">`IsRoot`</span>, that holds for elements <span class="pre">`r`</span> in <span class="pre">`R`</span> where a polynomial vanishes.

    example {R : Type*} [CommRing R] (P : R[X]) (r : R) : IsRoot P r ↔ P.eval r = 0 := Iff.rfl

We would like to say that, assuming <span class="pre">`R`</span> has no zero divisor, a polynomial has at most as many roots as its degree, where the roots are counted with multiplicities. But once again the case of the zero polynomial is painful. So Mathlib defines <span class="pre">`Polynomial.roots`</span> to send a polynomial <span class="pre">`P`</span> to a multiset, i.e. the finite set that is defined to be empty if <span class="pre">`P`</span> is zero and the roots of <span class="pre">`P`</span>, with multiplicities, otherwise. This is defined only when the underlying ring is a domain since otherwise the definition does not have good properties.

    example {R : Type*} [CommRing R] [IsDomain R] (r : R) : (X - C r).roots = {r} :=
      roots_X_sub_C r

    example {R : Type*} [CommRing R] [IsDomain R] (r : R) (n : ℕ):
        ((X - C r) ^ n).roots = n • {r} :=
      by simp

Both <span class="pre">`Polynomial.eval`</span> and <span class="pre">`Polynomial.roots`</span> consider only the coefficients ring. They do not allow us to say that <span class="pre">`X`</span>` `<span class="pre">`^`</span>` `<span class="pre">`2`</span>` `<span class="pre">`-`</span>` `<span class="pre">`2`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℚ[X]`</span> has a root in <span class="pre">`ℝ`</span> or that <span class="pre">`X`</span>` `<span class="pre">`^`</span>` `<span class="pre">`2`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ[X]`</span> has a root in <span class="pre">`ℂ`</span>. For this, we need <span class="pre">`Polynomial.aeval`</span>, which will evaluate <span class="pre">`P`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R[X]`</span> in any <span class="pre">`R`</span>-algebra. More precisely, given a semiring <span class="pre">`A`</span> and an instance of <span class="pre">`Algebra`</span>` `<span class="pre">`R`</span>` `<span class="pre">`A`</span>, <span class="pre">`Polynomial.aeval`</span> sends every element of <span class="pre">`a`</span> along the <span class="pre">`R`</span>-algebra morphism of evaluation at <span class="pre">`a`</span>. Since <span class="pre">`AlgHom`</span> has a coercion to functions, one can apply it to a polynomial. But <span class="pre">`aeval`</span> does not have a polynomial as an argument, so one cannot use dot notation like in <span class="pre">`P.eval`</span> above.

    example : aeval Complex.I (X ^ 2 + 1 : ℝ[X]) = 0 := by simp

The function corresponding to <span class="pre">`roots`</span> in this context is <span class="pre">`aroots`</span> which takes a polynomial and then an algebra and outputs a multiset (with the same caveat about the zero polynomial as for <span class="pre">`roots`</span>).

    open Complex Polynomial

    example : aroots (X ^ 2 + 1 : ℝ[X]) ℂ = {Complex.I, -I} := by
      suffices roots (X ^ 2 + 1 : ℂ[X]) = {I, -I} by simpa [aroots_def]
      have factored : (X ^ 2 + 1 : ℂ[X]) = (X - C I) * (X - C (-I)) := by
        have key : (C I * C I : ℂ[X]) = -1 := by simp [← C_mul]
        rw [C_neg]
        linear_combination key
      have p_ne_zero : (X - C I) * (X - C (-I)) ≠ 0 := by
        intro H
        apply_fun eval 0 at H
        simp [eval] at H
      simp only [factored, roots_mul p_ne_zero, roots_X_sub_C]
      rfl

    -- Mathlib knows about D'Alembert-Gauss theorem: ``ℂ`` is algebraically closed.
    example : IsAlgClosed ℂ := inferInstance

More generally, given an ring morphism <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R`</span>` `<span class="pre">`→+*`</span>` `<span class="pre">`S`</span> one can evaluate <span class="pre">`P`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R[X]`</span> at a point in <span class="pre">`S`</span> using <span class="pre">`Polynomial.eval₂`</span>. This one produces an actual function from <span class="pre">`R[X]`</span> to <span class="pre">`S`</span> since it does not assume the existence of a <span class="pre">`Algebra`</span>` `<span class="pre">`R`</span>` `<span class="pre">`S`</span> instance, so dot notation works as you would expect.

    #check (Complex.ofRealHom : ℝ →+* ℂ)

    example : (X ^ 2 + 1 : ℝ[X]).eval₂ Complex.ofRealHom Complex.I = 0 := by simp

Let us end by mentioning multivariate polynomials briefly. Given a commutative semiring <span class="pre">`R`</span>, the <span class="pre">`R`</span>-algebra of polynomials with coefficients in <span class="pre">`R`</span> and indeterminates indexed by a type <span class="pre">`σ`</span> is <span class="pre">`MVPolynomial`</span>` `<span class="pre">`σ`</span>` `<span class="pre">`R`</span>. Given <span class="pre">`i`</span>` `<span class="pre">`:`</span>` `<span class="pre">`σ`</span>, the corresponding polynomial is <span class="pre">`MvPolynomial.X`</span>` `<span class="pre">`i`</span>. (As usual, one can open the <span class="pre">`MVPolynomial`</span> namespace to shorten this to <span class="pre">`X`</span>` `<span class="pre">`i`</span>.) For instance, if we want two indeterminates we can use <span class="pre">`Fin`</span>` `<span class="pre">`2`</span> as <span class="pre">`σ`</span> and write the polynomial defining the unit circle in <span class="math notranslate nohighlight">\\\mathbb{R}^2\`\\</span> as:

    open MvPolynomial

    def circleEquation : MvPolynomial (Fin 2) ℝ := X 0 ^ 2 + X 1 ^ 2 - 1

Recall that function application has a very high precedence so the expression above is read as <span class="pre">`(X`</span>` `<span class="pre">`0)`</span>` `<span class="pre">`^`</span>` `<span class="pre">`2`</span>` `<span class="pre">`+`</span>` `<span class="pre">`(X`</span>` `<span class="pre">`1)`</span>` `<span class="pre">`^`</span>` `<span class="pre">`2`</span>` `<span class="pre">`-`</span>` `<span class="pre">`1`</span>. We can evaluate it to make sure the point with coordinates <span class="math notranslate nohighlight">\\(1, 0)\\</span> is on the circle. Recall the <span class="pre">`![...]`</span> notation denotes elements of <span class="pre">`Fin`</span>` `<span class="pre">`n`</span>` `<span class="pre">`→`</span>` `<span class="pre">`X`</span> for some natural number <span class="pre">`n`</span> determined by the number of arguments and some type <span class="pre">`X`</span> determined by the type of arguments.

    example : MvPolynomial.eval ![1, 0] circleEquation = 0 := by simp [circleEquation]
