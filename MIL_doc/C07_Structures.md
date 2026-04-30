<span id="id1"></span>

# <span class="section-number">7. </span>Structures<a href="#structures" class="headerlink" title="Link to this heading"></a>

Modern mathematics makes essential use of algebraic structures, which encapsulate patterns that can be instantiated in multiple settings. The subject provides various ways of defining such structures and constructing particular instances.

Lean therefore provides corresponding ways of defining structures formally and working with them. You have already seen examples of algebraic structures in Lean, such as rings and lattices, which were discussed in <a href="C02_Basics.html#basics" class="reference internal"><span class="std std-numref">Chapter 2</span></a>. This chapter will explain the mysterious square bracket annotations that you saw there, <span class="pre">`[Ring`</span>` `<span class="pre">`α]`</span> and <span class="pre">`[Lattice`</span>` `<span class="pre">`α]`</span>. It will also show you how to define and use algebraic structures on your own.

For more technical detail, you can consult <a href="https://leanprover.github.io/theorem_proving_in_lean/" class="reference external">Theorem Proving in Lean</a>, and a paper by Anne Baanen, <a href="https://arxiv.org/abs/2202.01629" class="reference external">Use and abuse of instance parameters in the Lean mathematical library</a>.

<span id="section-structures"></span>

## <span class="section-number">7.1. </span>Defining structures<a href="#defining-structures" class="headerlink" title="Link to this heading"></a>

In the broadest sense of the term, a *structure* is a specification of a collection of data, possibly with constraints that the data is required to satisfy. An *instance* of the structure is a particular bundle of data satisfying the constraints. For example, we can specify that a point is a tuple of three real numbers:

    @[ext]
    structure Point where
      x : ℝ
      y : ℝ
      z : ℝ

The <span class="pre">`@[ext]`</span> annotation tells Lean to automatically generate theorems that can be used to prove that two instances of a structure are equal when their components are equal, a property known as *extensionality*.

    #check Point.ext

    example (a b : Point) (hx : a.x = b.x) (hy : a.y = b.y) (hz : a.z = b.z) : a = b := by
      ext
      repeat' assumption

We can then define particular instances of the <span class="pre">`Point`</span> structure. Lean provides multiple ways of doing that.

    def myPoint1 : Point where
      x := 2
      y := -1
      z := 4

    def myPoint2 : Point :=
      ⟨2, -1, 4⟩

    def myPoint3 :=
      Point.mk 2 (-1) 4

In the first example, the fields of the structure are named explicitly. The function <span class="pre">`Point.mk`</span> referred to in the definition of <span class="pre">`myPoint3`</span> is known as the *constructor* for the <span class="pre">`Point`</span> structure, because it serves to construct elements. You can specify a different name if you want, like <span class="pre">`build`</span>.

    structure Point' where build ::
      x : ℝ
      y : ℝ
      z : ℝ

    #check Point'.build 2 (-1) 4

The next two examples show how to define functions on structures. Whereas the second example makes the <span class="pre">`Point.mk`</span> constructor explicit, the first example uses an anonymous constructor for brevity. Lean can infer the relevant constructor from the indicated type of <span class="pre">`add`</span>. It is conventional to put definitions and theorems associated with a structure like <span class="pre">`Point`</span> in a namespace with the same name. In the example below, because we have opened the <span class="pre">`Point`</span> namespace, the full name of <span class="pre">`add`</span> is <span class="pre">`Point.add`</span>. When the namespace is not open, we have to use the full name. But remember that it is often convenient to use anonymous projection notation, which allows us to write <span class="pre">`a.add`</span>` `<span class="pre">`b`</span> instead of <span class="pre">`Point.add`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>. Lean interprets the former as the latter because <span class="pre">`a`</span> has type <span class="pre">`Point`</span>.

    namespace Point

    def add (a b : Point) : Point :=
      ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

    def add' (a b : Point) : Point where
      x := a.x + b.x
      y := a.y + b.y
      z := a.z + b.z

    #check add myPoint1 myPoint2
    #check myPoint1.add myPoint2

    end Point

    #check Point.add myPoint1 myPoint2
    #check myPoint1.add myPoint2

Below we will continue to put definitions in the relevant namespace, but we will leave the namespacing commands out of the quoted snippets. To prove properties of the addition function, we can use <span class="pre">`rw`</span> to expand the definition and <span class="pre">`ext`</span> to reduce an equation between two elements of the structure to equations between the components. Below we use the <span class="pre">`protected`</span> keyword so that the name of the theorem is <span class="pre">`Point.add_comm`</span>, even when the namespace is open. This is helpful when we want to avoid ambiguity with a generic theorem like <span class="pre">`add_comm`</span>.

    protected theorem add_comm (a b : Point) : add a b = add b a := by
      rw [add, add]
      ext <;> dsimp
      repeat' apply add_comm

    example (a b : Point) : add a b = add b a := by simp [add, add_comm]

Because Lean can unfold definitions and simplify projections internally, sometimes the equations we want hold definitionally.

    theorem add_x (a b : Point) : (a.add b).x = a.x + b.x :=
      rfl

It is also possible to define functions on structures using pattern matching, in a manner similar to the way we defined recursive functions in <a href="C05_Elementary_Number_Theory.html#section-induction-and-recursion" class="reference internal"><span class="std std-numref">Section 5.2</span></a>. The definitions <span class="pre">`addAlt`</span> and <span class="pre">`addAlt'`</span> below are essentially the same; the only difference is that we use anonymous constructor notation in the second. Although it is sometimes convenient to define functions this way, and structural eta-reduction makes this alternative definitionally equivalent, it can make things less convenient in later proofs. In particular, <span class="pre">`rw`</span>` `<span class="pre">`[addAlt]`</span> leaves us with a messier goal view containing a <span class="pre">`match`</span> statement.

    def addAlt : Point → Point → Point
      | Point.mk x₁ y₁ z₁, Point.mk x₂ y₂ z₂ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

    def addAlt' : Point → Point → Point
      | ⟨x₁, y₁, z₁⟩, ⟨x₂, y₂, z₂⟩ => ⟨x₁ + x₂, y₁ + y₂, z₁ + z₂⟩

    theorem addAlt_x (a b : Point) : (a.addAlt b).x = a.x + b.x := by
      rfl

    theorem addAlt_comm (a b : Point) : addAlt a b = addAlt b a := by
      rw [addAlt, addAlt]
      -- the same proof still works, but the goal view here is harder to read
      ext <;> dsimp
      repeat' apply add_comm

Mathematical constructions often involve taking apart bundled information and putting it together again in different ways. It therefore makes sense that Lean and Mathlib offer so many ways of doing this efficiently. As an exercise, try proving that <span class="pre">`Point.add`</span> is associative. Then define scalar multiplication for a point and show that it distributes over addition.

    protected theorem add_assoc (a b c : Point) : (a.add b).add c = a.add (b.add c) := by
      sorry

    def smul (r : ℝ) (a : Point) : Point :=
      sorry

    theorem smul_distrib (r : ℝ) (a b : Point) :
        (smul r a).add (smul r b) = smul r (a.add b) := by
      sorry

Using structures is only the first step on the road to algebraic abstraction. We don’t yet have a way to link <span class="pre">`Point.add`</span> to the generic <span class="pre">`+`</span> symbol, or to connect <span class="pre">`Point.add_comm`</span> and <span class="pre">`Point.add_assoc`</span> to the generic <span class="pre">`add_comm`</span> and <span class="pre">`add_assoc`</span> theorems. These tasks belong to the *algebraic* aspect of using structures, and we will explain how to carry them out in the next section. For now, just think of a structure as a way of bundling together objects and information.

It is especially useful that a structure can specify not only data types but also constraints that the data must satisfy. In Lean, the latter are represented as fields of type <span class="pre">`Prop`</span>. For example, the *standard 2-simplex* is defined to be the set of points <span class="math notranslate nohighlight">\\(x, y, z)\\</span> satisfying <span class="math notranslate nohighlight">\\x ≥ 0\\</span>, <span class="math notranslate nohighlight">\\y ≥ 0\\</span>, <span class="math notranslate nohighlight">\\z ≥ 0\\</span>, and <span class="math notranslate nohighlight">\\x + y + z = 1\\</span>. If you are not familiar with the notion, you should draw a picture, and convince yourself that this set is the equilateral triangle in three-space with vertices <span class="math notranslate nohighlight">\\(1, 0, 0)\\</span>, <span class="math notranslate nohighlight">\\(0, 1, 0)\\</span>, and <span class="math notranslate nohighlight">\\(0, 0, 1)\\</span>, together with its interior. We can represent it in Lean as follows:

    structure StandardTwoSimplex where
      x : ℝ
      y : ℝ
      z : ℝ
      x_nonneg : 0 ≤ x
      y_nonneg : 0 ≤ y
      z_nonneg : 0 ≤ z
      sum_eq : x + y + z = 1

Notice that the last four fields refer to <span class="pre">`x`</span>, <span class="pre">`y`</span>, and <span class="pre">`z`</span>, that is, the first three fields. We can define a map from the two-simplex to itself that swaps <span class="pre">`x`</span> and <span class="pre">`y`</span>:

    def swapXy (a : StandardTwoSimplex) : StandardTwoSimplex
        where
      x := a.y
      y := a.x
      z := a.z
      x_nonneg := a.y_nonneg
      y_nonneg := a.x_nonneg
      z_nonneg := a.z_nonneg
      sum_eq := by rw [add_comm a.y a.x, a.sum_eq]

More interestingly, we can compute the midpoint of two points on the simplex. We have added the phrase <span class="pre">`noncomputable`</span>` `<span class="pre">`section`</span> at the beginning of this file in order to use division on the real numbers.

    noncomputable section

    def midpoint (a b : StandardTwoSimplex) : StandardTwoSimplex
        where
      x := (a.x + b.x) / 2
      y := (a.y + b.y) / 2
      z := (a.z + b.z) / 2
      x_nonneg := div_nonneg (add_nonneg a.x_nonneg b.x_nonneg) (by norm_num)
      y_nonneg := div_nonneg (add_nonneg a.y_nonneg b.y_nonneg) (by norm_num)
      z_nonneg := div_nonneg (add_nonneg a.z_nonneg b.z_nonneg) (by norm_num)
      sum_eq := by field_simp; linarith [a.sum_eq, b.sum_eq]

Here we have established <span class="pre">`x_nonneg`</span>, <span class="pre">`y_nonneg`</span>, and <span class="pre">`z_nonneg`</span> with concise proof terms, but establish <span class="pre">`sum_eq`</span> in tactic mode, using <span class="pre">`by`</span>.

Given a parameter <span class="math notranslate nohighlight">\\\lambda\\</span> satisfying <span class="math notranslate nohighlight">\\0 \le \lambda \le 1\\</span>, we can take the weighted average <span class="math notranslate nohighlight">\\\lambda a + (1 - \lambda) b\\</span> of two points <span class="math notranslate nohighlight">\\a\\</span> and <span class="math notranslate nohighlight">\\b\\</span> in the standard 2-simplex. We challenge you to define that function, in analogy to the <span class="pre">`midpoint`</span> function above.

    def weightedAverage (lambda : Real) (lambda_nonneg : 0 ≤ lambda) (lambda_le : lambda ≤ 1)
        (a b : StandardTwoSimplex) : StandardTwoSimplex :=
      sorry

Structures can depend on parameters. For example, we can generalize the standard 2-simplex to the standard <span class="math notranslate nohighlight">\\n\\</span>-simplex for any <span class="math notranslate nohighlight">\\n\\</span>. At this stage, you don’t have to know anything about the type <span class="pre">`Fin`</span>` `<span class="pre">`n`</span> except that it has <span class="math notranslate nohighlight">\\n\\</span> elements, and that Lean knows how to sum over it.

    open BigOperators

    structure StandardSimplex (n : ℕ) where
      V : Fin n → ℝ
      NonNeg : ∀ i : Fin n, 0 ≤ V i
      sum_eq_one : (∑ i, V i) = 1

    namespace StandardSimplex

    def midpoint (n : ℕ) (a b : StandardSimplex n) : StandardSimplex n
        where
      V i := (a.V i + b.V i) / 2
      NonNeg := by
        intro i
        apply div_nonneg
        · linarith [a.NonNeg i, b.NonNeg i]
        norm_num
      sum_eq_one := by
        simp [div_eq_mul_inv, ← Finset.sum_mul, Finset.sum_add_distrib,
          a.sum_eq_one, b.sum_eq_one]
        field_simp

    end StandardSimplex

As an exercise, see if you can define the weighted average of two points in the standard <span class="math notranslate nohighlight">\\n\\</span>-simplex. You can use <span class="pre">`Finset.sum_add_distrib`</span> and <span class="pre">`Finset.mul_sum`</span> to manipulate the relevant sums.

We have seen that structures can be used to bundle together data and properties. Interestingly, they can also be used to bundle together properties without the data. For example, the next structure, <span class="pre">`IsLinear`</span>, bundles together the two components of linearity.

    structure IsLinear (f : ℝ → ℝ) where
      is_additive : ∀ x y, f (x + y) = f x + f y
      preserves_mul : ∀ x c, f (c * x) = c * f x

    section
    variable (f : ℝ → ℝ) (linf : IsLinear f)

    #check linf.is_additive
    #check linf.preserves_mul

    end

It is worth pointing out that structures are not the only way to bundle together data. The <span class="pre">`Point`</span> data structure can be defined using the generic type product, and <span class="pre">`IsLinear`</span> can be defined with a simple <span class="pre">`and`</span>.

    def Point'' :=
      ℝ × ℝ × ℝ

    def IsLinear' (f : ℝ → ℝ) :=
      (∀ x y, f (x + y) = f x + f y) ∧ ∀ x c, f (c * x) = c * f x

Generic type constructions can even be used in place of structures with dependencies between their components. For example, the *subtype* construction combines a piece of data with a property. You can think of the type <span class="pre">`PReal`</span> in the next example as being the type of positive real numbers. Any <span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`PReal`</span> has two components: the value, and the property of being positive. You can access these components as <span class="pre">`x.val`</span>, which has type <span class="pre">`ℝ`</span>, and <span class="pre">`x.property`</span>, which represents the fact <span class="pre">`0`</span>` `<span class="pre">`<`</span>` `<span class="pre">`x.val`</span>.

    def PReal :=
      { y : ℝ // 0 < y }

    section
    variable (x : PReal)

    #check x.val
    #check x.property
    #check x.1
    #check x.2

    end

We could have used subtypes to define the standard 2-simplex, as well as the standard <span class="math notranslate nohighlight">\\n\\</span>-simplex for an arbitrary <span class="math notranslate nohighlight">\\n\\</span>.

    def StandardTwoSimplex' :=
      { p : ℝ × ℝ × ℝ // 0 ≤ p.1 ∧ 0 ≤ p.2.1 ∧ 0 ≤ p.2.2 ∧ p.1 + p.2.1 + p.2.2 = 1 }

    def StandardSimplex' (n : ℕ) :=
      { v : Fin n → ℝ // (∀ i : Fin n, 0 ≤ v i) ∧ (∑ i, v i) = 1 }

Similarly, *Sigma types* are generalizations of ordered pairs, whereby the type of the second component depends on the type of the first.

    def StdSimplex := Σ n : ℕ, StandardSimplex n

    section
    variable (s : StdSimplex)

    #check s.fst
    #check s.snd

    #check s.1
    #check s.2

    end

Given <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`StdSimplex`</span>, the first component <span class="pre">`s.fst`</span> is a natural number, and the second component is an element of the corresponding simplex <span class="pre">`StandardSimplex`</span>` `<span class="pre">`s.fst`</span>. The difference between a Sigma type and a subtype is that the second component of a Sigma type is data rather than a proposition.

But even though we can use products, subtypes, and Sigma types instead of structures, using structures has a number of advantages. Defining a structure abstracts away the underlying representation and provides custom names for the functions that access the components. This makes proofs more robust: proofs that rely only on the interface to a structure will generally continue to work when we change the definition, as long as we redefine the old accessors in terms of the new definition. Moreover, as we are about to see, Lean provides support for weaving structures together into a rich, interconnected hierarchy, and for managing the interactions between them.

<span id="section-algebraic-structures"></span>

## <span class="section-number">7.2. </span>Algebraic Structures<a href="#algebraic-structures" class="headerlink" title="Link to this heading"></a>

To clarify what we mean by the phrase *algebraic structure*, it will help to consider some examples.

1.  A *partially ordered set* consists of a set <span class="math notranslate nohighlight">\\P\\</span> and a binary relation <span class="math notranslate nohighlight">\\\le\\</span> on <span class="math notranslate nohighlight">\\P\\</span> that is transitive and reflexive.

2.  A *group* consists of a set <span class="math notranslate nohighlight">\\G\\</span> with an associative binary operation, an identity element <span class="math notranslate nohighlight">\\1\\</span>, and a function <span class="math notranslate nohighlight">\\g \mapsto g^{-1}\\</span> that returns an inverse for each <span class="math notranslate nohighlight">\\g\\</span> in <span class="math notranslate nohighlight">\\G\\</span>. A group is *abelian* or *commutative* if the operation is commutative.

3.  A *lattice* is a partially ordered set with meets and joins.

4.  A *ring* consists of an (additively written) abelian group <span class="math notranslate nohighlight">\\(R, +, 0, x \mapsto -x)\\</span> together with an associative multiplication operation <span class="math notranslate nohighlight">\\\cdot\\</span> and an identity <span class="math notranslate nohighlight">\\1\\</span>, such that multiplication distributes over addition. A ring is *commutative* if the multiplication is commutative.

5.  An *ordered ring* <span class="math notranslate nohighlight">\\(R, +, 0, -, \cdot, 1, \le)\\</span> consists of a ring together with a partial order on its elements, such that <span class="math notranslate nohighlight">\\a \le b\\</span> implies <span class="math notranslate nohighlight">\\a + c \le b + c\\</span> for every <span class="math notranslate nohighlight">\\a\\</span>, <span class="math notranslate nohighlight">\\b\\</span>, and <span class="math notranslate nohighlight">\\c\\</span> in <span class="math notranslate nohighlight">\\R\\</span>, and <span class="math notranslate nohighlight">\\0 \le a\\</span> and <span class="math notranslate nohighlight">\\0 \le b\\</span> implies <span class="math notranslate nohighlight">\\0 \le a b\\</span> for every <span class="math notranslate nohighlight">\\a\\</span> and <span class="math notranslate nohighlight">\\b\\</span> in <span class="math notranslate nohighlight">\\R\\</span>.

6.  A *metric space* consists of a set <span class="math notranslate nohighlight">\\X\\</span> and a function <span class="math notranslate nohighlight">\\d : X \times X \to \mathbb{R}\\</span> such that the following hold:

    - <span class="math notranslate nohighlight">\\d(x, y) \ge 0\\</span> for every <span class="math notranslate nohighlight">\\x\\</span> and <span class="math notranslate nohighlight">\\y\\</span> in <span class="math notranslate nohighlight">\\X\\</span>.

    - <span class="math notranslate nohighlight">\\d(x, y) = 0\\</span> if and only if <span class="math notranslate nohighlight">\\x = y\\</span>.

    - <span class="math notranslate nohighlight">\\d(x, y) = d(y, x)\\</span> for every <span class="math notranslate nohighlight">\\x\\</span> and <span class="math notranslate nohighlight">\\y\\</span> in <span class="math notranslate nohighlight">\\X\\</span>.

    - <span class="math notranslate nohighlight">\\d(x, z) \le d(x, y) + d(y, z)\\</span> for every <span class="math notranslate nohighlight">\\x\\</span>, <span class="math notranslate nohighlight">\\y\\</span>, and <span class="math notranslate nohighlight">\\z\\</span> in <span class="math notranslate nohighlight">\\X\\</span>.

7.  A *topological space* consists of a set <span class="math notranslate nohighlight">\\X\\</span> and a collection <span class="math notranslate nohighlight">\\\mathcal T\\</span> of subsets of <span class="math notranslate nohighlight">\\X\\</span>, called the *open subsets of* <span class="math notranslate nohighlight">\\X\\</span>, such that the following hold:

    - The empty set and <span class="math notranslate nohighlight">\\X\\</span> are open.

    - The intersection of two open sets is open.

    - An arbitrary union of open sets is open.

In each of these examples, the elements of the structure belong to a set, the *carrier set*, that sometimes stands proxy for the entire structure. For example, when we say “let <span class="math notranslate nohighlight">\\G\\</span> be a group” and then “let <span class="math notranslate nohighlight">\\g \in G\\</span>,” we are using <span class="math notranslate nohighlight">\\G\\</span> to stand for both the structure and its carrier. Not every algebraic structure is associated with a single carrier set in this way. For example, a *bipartite graph* involves a relation between two sets, as does a *Galois connection*, A *category* also involves two sets of interest, commonly called the *objects* and the *morphisms*.

The examples indicate some of the things that a proof assistant has to do in order to support algebraic reasoning. First, it needs to recognize concrete instances of structures. The number systems <span class="math notranslate nohighlight">\\\mathbb{Z}\\</span>, <span class="math notranslate nohighlight">\\\mathbb{Q}\\</span>, and <span class="math notranslate nohighlight">\\\mathbb{R}\\</span> are all ordered rings, and we should be able to apply a generic theorem about ordered rings in any of these instances. Sometimes a concrete set may be an instance of a structure in more than one way. For example, in addition to the usual topology on <span class="math notranslate nohighlight">\\\mathbb{R}\\</span>, which forms the basis for real analysis, we can also consider the *discrete* topology on <span class="math notranslate nohighlight">\\\mathbb{R}\\</span>, in which every set is open.

Second, a proof assistant needs to support generic notation on structures. In Lean, the notation <span class="pre">`*`</span> is used for multiplication in all the usual number systems, as well as for multiplication in generic groups and rings. When we use an expression like <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span>, Lean has to use information about the types of <span class="pre">`f`</span>, <span class="pre">`x`</span>, and <span class="pre">`y`</span> to determine which multiplication we have in mind.

Third, it needs to deal with the fact that structures can inherit definitions, theorems, and notation from other structures in various ways. Some structures extend others by adding more axioms. A commutative ring is still a ring, so any definition that makes sense in a ring also makes sense in a commutative ring, and any theorem that holds in a ring also holds in a commutative ring. Some structures extend others by adding more data. For example, the additive part of any ring is an additive group. The ring structure adds a multiplication and an identity, as well as axioms that govern them and relate them to the additive part. Sometimes we can define one structure in terms of another. Any metric space has a canonical topology associated with it, the *metric space topology*, and there are various topologies that can be associated with any linear ordering.

Finally, it is important to keep in mind that mathematics allows us to use functions and operations to define structures in the same way we use functions and operations to define numbers. Products and powers of groups are again groups. For every <span class="math notranslate nohighlight">\\n\\</span>, the integers modulo <span class="math notranslate nohighlight">\\n\\</span> form a ring, and for every <span class="math notranslate nohighlight">\\k &gt; 0\\</span>, the <span class="math notranslate nohighlight">\\k \times k\\</span> matrices of polynomials with coefficients in that ring again form a ring. Thus we can calculate with structures just as easily as we can calculate with their elements. This means that algebraic structures lead dual lives in mathematics, as containers for collections of objects and as objects in their own right. A proof assistant has to accommodate this dual role.

When dealing with elements of a type that has an algebraic structure associated with it, a proof assistant needs to recognize the structure and find the relevant definitions, theorems, and notation. All this should sound like a lot of work, and it is. But Lean uses a small collection of fundamental mechanisms to carry out these tasks. The goal of this section is to explain these mechanisms and show you how to use them.

The first ingredient is almost too obvious to mention: formally speaking, algebraic structures are structures in the sense of <a href="#section-structures" class="reference internal"><span class="std std-numref">Section 7.1</span></a>. An algebraic structure is a specification of a bundle of data satisfying some axiomatic hypotheses, and we saw in <a href="#section-structures" class="reference internal"><span class="std std-numref">Section 7.1</span></a> that this is exactly what the <span class="pre">`structure`</span> command is designed to accommodate. It’s a marriage made in heaven!

Given a data type <span class="pre">`α`</span>, we can define the group structure on <span class="pre">`α`</span> as follows.

    structure Group₁ (α : Type*) where
      mul : α → α → α
      one : α
      inv : α → α
      mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
      mul_one : ∀ x : α, mul x one = x
      one_mul : ∀ x : α, mul one x = x
      inv_mul_cancel : ∀ x : α, mul (inv x) x = one

Notice that the type <span class="pre">`α`</span> is a *parameter* in the definition of <span class="pre">`Group₁`</span>. So you should think of an object <span class="pre">`struc`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Group₁`</span>` `<span class="pre">`α`</span> as being a group structure on <span class="pre">`α`</span>. We saw in <a href="C02_Basics.html#proving-identities-in-algebraic-structures" class="reference internal"><span class="std std-numref">Section 2.2</span></a> that the counterpart <span class="pre">`mul_inv_cancel`</span> to <span class="pre">`inv_mul_cancel`</span> follows from the other group axioms, so there is no need to add it to the definition.

This definition of a group is similar to the definition of <span class="pre">`Group`</span> in Mathlib, and we have chosen the name <span class="pre">`Group₁`</span> to distinguish our version. If you write <span class="pre">`#check`</span>` `<span class="pre">`Group`</span> and ctrl-click on the definition, you will see that the Mathlib version of <span class="pre">`Group`</span> is defined to extend another structure; we will explain how to do that later. If you type <span class="pre">`#print`</span>` `<span class="pre">`Group`</span> you will also see that the Mathlib version of <span class="pre">`Group`</span> has a number of extra fields. For reasons we will explain later, sometimes it is useful to add redundant information to a structure, so that there are additional fields for objects and functions that can be defined from the core data. Don’t worry about that for now. Rest assured that our simplified version <span class="pre">`Group₁`</span> is morally the same as the definition of a group that Mathlib uses.

It is sometimes useful to bundle the type together with the structure, and Mathlib also contains a definition of a <span class="pre">`Grp`</span> structure that is equivalent to the following:

    structure Grp₁ where
      α : Type*
      str : Group₁ α

The Mathlib version is found in <span class="pre">`Mathlib.Algebra.Category.Grp.Basic`</span>, and you can <span class="pre">`#check`</span> it if you add this to the imports at the beginning of the examples file.

For reasons that will become clearer below, it is more often useful to keep the type <span class="pre">`α`</span> separate from the structure <span class="pre">`Group`</span>` `<span class="pre">`α`</span>. We refer to the two objects together as a *partially bundled structure*, since the representation combines most, but not all, of the components into one structure. It is common in Mathlib to use capital roman letters like <span class="pre">`G`</span> for a type when it is used as the carrier type for a group.

Let’s construct a group, which is to say, an element of the <span class="pre">`Group₁`</span> type. For any pair of types <span class="pre">`α`</span> and <span class="pre">`β`</span>, Mathlib defines the type <span class="pre">`Equiv`</span>` `<span class="pre">`α`</span>` `<span class="pre">`β`</span> of *equivalences* between <span class="pre">`α`</span> and <span class="pre">`β`</span>. Mathlib also defines the suggestive notation <span class="pre">`α`</span>` `<span class="pre">`≃`</span>` `<span class="pre">`β`</span> for this type. An element <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span>` `<span class="pre">`≃`</span>` `<span class="pre">`β`</span> is a bijection between <span class="pre">`α`</span> and <span class="pre">`β`</span> represented by four components: a function <span class="pre">`f.toFun`</span> from <span class="pre">`α`</span> to <span class="pre">`β`</span>, the inverse function <span class="pre">`f.invFun`</span> from <span class="pre">`β`</span> to <span class="pre">`α`</span>, and two properties that specify these functions are indeed inverse to one another.

    variable (α β γ : Type*)
    variable (f : α ≃ β) (g : β ≃ γ)

    #check Equiv α β
    #check (f.toFun : α → β)
    #check (f.invFun : β → α)
    #check (f.right_inv : ∀ x : β, f (f.invFun x) = x)
    #check (f.left_inv : ∀ x : α, f.invFun (f x) = x)
    #check (Equiv.refl α : α ≃ α)
    #check (f.symm : β ≃ α)
    #check (f.trans g : α ≃ γ)

Notice the creative naming of the last three constructions. We think of the identity function <span class="pre">`Equiv.refl`</span>, the inverse operation <span class="pre">`Equiv.symm`</span>, and the composition operation <span class="pre">`Equiv.trans`</span> as explicit evidence that the property of being in bijective correspondence is an equivalence relation.

Notice also that <span class="pre">`f.trans`</span>` `<span class="pre">`g`</span> requires composing the forward functions in reverse order. Mathlib has declared a *coercion* from <span class="pre">`Equiv`</span>` `<span class="pre">`α`</span>` `<span class="pre">`β`</span> to the function type <span class="pre">`α`</span>` `<span class="pre">`→`</span>` `<span class="pre">`β`</span>, so we can omit writing <span class="pre">`.toFun`</span> and have Lean insert it for us.

    example (x : α) : (f.trans g).toFun x = g.toFun (f.toFun x) :=
      rfl

    example (x : α) : (f.trans g) x = g (f x) :=
      rfl

    example : (f.trans g : α → γ) = g ∘ f :=
      rfl

Mathlib also defines the type <span class="pre">`perm`</span>` `<span class="pre">`α`</span> of equivalences between <span class="pre">`α`</span> and itself.

    example (α : Type*) : Equiv.Perm α = (α ≃ α) :=
      rfl

It should be clear that <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`α`</span> forms a group under composition of equivalences. We orient things so that <span class="pre">`mul`</span>` `<span class="pre">`f`</span>` `<span class="pre">`g`</span> is equal to <span class="pre">`g.trans`</span>` `<span class="pre">`f`</span>, whose forward function is <span class="pre">`f`</span>` `<span class="pre">`∘`</span>` `<span class="pre">`g`</span>. In other words, multiplication is what we ordinarily think of as composition of the bijections. Here we define this group:

    def permGroup {α : Type*} : Group₁ (Equiv.Perm α)
        where
      mul f g := Equiv.trans g f
      one := Equiv.refl α
      inv := Equiv.symm
      mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
      one_mul := Equiv.trans_refl
      mul_one := Equiv.refl_trans
      inv_mul_cancel := Equiv.self_trans_symm

In fact, Mathlib defines exactly this <span class="pre">`Group`</span> structure on <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`α`</span> in the file <span class="pre">`Algebra.Group.End`</span>. As always, you can hover over the theorems used in the definition of <span class="pre">`permGroup`</span> to see their statements, and you can jump to their definitions in the original file to learn more about how they are implemented.

In ordinary mathematics, we generally think of notation as independent of structure. For example, we can consider groups <span class="math notranslate nohighlight">\\(G\_1, \cdot, 1, \cdot^{-1})\\</span>, <span class="math notranslate nohighlight">\\(G\_2, \circ, e, i(\cdot))\\</span>, and <span class="math notranslate nohighlight">\\(G\_3, +, 0, -)\\</span>. In the first case, we write the binary operation as <span class="math notranslate nohighlight">\\\cdot\\</span>, the identity as <span class="math notranslate nohighlight">\\1\\</span>, and the inverse function as <span class="math notranslate nohighlight">\\x \mapsto x^{-1}\\</span>. In the second and third cases, we use the notational alternatives shown. When we formalize the notion of a group in Lean, however, the notation is more tightly linked to the structure. In Lean, the components of any <span class="pre">`Group`</span> are named <span class="pre">`mul`</span>, <span class="pre">`one`</span>, and <span class="pre">`inv`</span>, and in a moment we will see how multiplicative notation is set up to refer to them. If we want to use additive notation, we instead use an isomorphic structure <span class="pre">`AddGroup`</span> (the structure underlying additive groups). Its components are named <span class="pre">`add`</span>, <span class="pre">`zero`</span>, and <span class="pre">`neg`</span>, and the associated notation is what you would expect it to be.

Recall the type <span class="pre">`Point`</span> that we defined in <a href="#section-structures" class="reference internal"><span class="std std-numref">Section 7.1</span></a>, and the addition function that we defined there. These definitions are reproduced in the examples file that accompanies this section. As an exercise, define an <span class="pre">`AddGroup₁`</span> structure that is similar to the <span class="pre">`Group₁`</span> structure we defined above, except that it uses the additive naming scheme just described. Define negation and a zero on the <span class="pre">`Point`</span> data type, and define the <span class="pre">`AddGroup₁`</span> structure on <span class="pre">`Point`</span>.

    structure AddGroup₁ (α : Type*) where
      (add : α → α → α)
      -- fill in the rest
    @[ext]
    structure Point where
      x : ℝ
      y : ℝ
      z : ℝ

    namespace Point

    def add (a b : Point) : Point :=
      ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩

    def neg (a : Point) : Point := sorry

    def zero : Point := sorry

    def addGroupPoint : AddGroup₁ Point := sorry

    end Point

We are making progress. Now we know how to define algebraic structures in Lean, and we know how to define instances of those structures. But we also want to associate notation with structures so that we can use it with each instance. Moreover, we want to arrange it so that we can define an operation on a structure and use it with any particular instance, and we want to arrange it so that we can prove a theorem about a structure and use it with any instance.

In fact, Mathlib is already set up to use generic group notation, definitions, and theorems for <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`α`</span>.

    variable {α : Type*} (f g : Equiv.Perm α) (n : ℕ)

    #check f * g
    #check mul_assoc f g g⁻¹

    -- group power, defined for any group
    #check g ^ n

    example : f * g * g⁻¹ = f := by rw [mul_assoc, mul_inv_cancel, mul_one]

    example : f * g * g⁻¹ = f :=
      mul_inv_cancel_right f g

    example {α : Type*} (f g : Equiv.Perm α) : g.symm.trans (g.trans f) = f :=
      mul_inv_cancel_right f g

You can check that this is not the case for the additive group structure on <span class="pre">`Point`</span> that we asked you to define above. Our task now is to understand that magic that goes on under the hood in order to make the examples for <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`α`</span> work the way they do.

The issue is that Lean needs to be able to *find* the relevant notation and the implicit group structure, using the information that is found in the expressions that we type. Similarly, when we write <span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`y`</span> with expressions <span class="pre">`x`</span> and <span class="pre">`y`</span> that have type <span class="pre">`ℝ`</span>, Lean needs to interpret the <span class="pre">`+`</span> symbol as the relevant addition function on the reals. It also has to recognize the type <span class="pre">`ℝ`</span> as an instance of a commutative ring, so that all the definitions and theorems for a commutative ring are available. For another example, continuity is defined in Lean relative to any two topological spaces. When we have <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℂ`</span> and we write <span class="pre">`Continuous`</span>` `<span class="pre">`f`</span>, Lean has to find the relevant topologies on <span class="pre">`ℝ`</span> and <span class="pre">`ℂ`</span>.

The magic is achieved with a combination of three things.

1.  *Logic.* A definition that should be interpreted in any group takes, as arguments, the type of the group and the group structure as arguments. Similarly, a theorem about the elements of an arbitrary group begins with universal quantifiers over the type of the group and the group structure.

2.  *Implicit arguments.* The arguments for the type and the structure are generally left implicit, so that we do not have to write them or see them in the Lean information window. Lean fills the information in for us silently.

3.  *Type class inference.* Also known as *class inference*, this is a simple but powerful mechanism that enables us to register information for Lean to use later on. When Lean is called on to fill in implicit arguments to a definition, theorem, or piece of notation, it can make use of information that has been registered.

Whereas an annotation <span class="pre">`(grp`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Group`</span>` `<span class="pre">`G)`</span> tells Lean that it should expect to be given that argument explicitly and the annotation <span class="pre">`{grp`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Group`</span>` `<span class="pre">`G}`</span> tells Lean that it should try to figure it out from contextual cues in the expression, the annotation <span class="pre">`[grp`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Group`</span>` `<span class="pre">`G]`</span> tells Lean that the corresponding argument should be synthesized using type class inference. Since the whole point to the use of such arguments is that we generally do not need to refer to them explicitly, Lean allows us to write <span class="pre">`[Group`</span>` `<span class="pre">`G]`</span> and leave the name anonymous. You have probably already noticed that Lean chooses names like <span class="pre">`_inst_1`</span> automatically. When we use the anonymous square-bracket annotation with the <span class="pre">`variables`</span> command, then as long as the variables are still in scope, Lean automatically adds the argument <span class="pre">`[Group`</span>` `<span class="pre">`G]`</span> to any definition or theorem that mentions <span class="pre">`G`</span>.

How do we register the information that Lean needs to use to carry out the search? Returning to our group example, we need only make two changes. First, instead of using the <span class="pre">`structure`</span> command to define the group structure, we use the keyword <span class="pre">`class`</span> to indicate that it is a candidate for class inference. Second, instead of defining particular instances with <span class="pre">`def`</span>, we use the keyword <span class="pre">`instance`</span> to register the particular instance with Lean. As with the names of class variables, we are allowed to leave the name of an instance definition anonymous, since in general we intend Lean to find it and put it to use without troubling us with the details.

    class Group₂ (α : Type*) where
      mul : α → α → α
      one : α
      inv : α → α
      mul_assoc : ∀ x y z : α, mul (mul x y) z = mul x (mul y z)
      mul_one : ∀ x : α, mul x one = x
      one_mul : ∀ x : α, mul one x = x
      inv_mul_cancel : ∀ x : α, mul (inv x) x = one

    instance {α : Type*} : Group₂ (Equiv.Perm α) where
      mul f g := Equiv.trans g f
      one := Equiv.refl α
      inv := Equiv.symm
      mul_assoc f g h := (Equiv.trans_assoc _ _ _).symm
      one_mul := Equiv.trans_refl
      mul_one := Equiv.refl_trans
      inv_mul_cancel := Equiv.self_trans_symm

The following illustrates their use.

    #check Group₂.mul

    def mySquare {α : Type*} [Group₂ α] (x : α) :=
      Group₂.mul x x

    #check mySquare

    section
    variable {β : Type*} (f g : Equiv.Perm β)

    example : Group₂.mul f g = g.trans f :=
      rfl

    example : mySquare f = f.trans f :=
      rfl

    end

The <span class="pre">`#check`</span> command shows that <span class="pre">`Group₂.mul`</span> has an implicit argument <span class="pre">`[Group₂`</span>` `<span class="pre">`α]`</span> that we expect to be found by class inference, where <span class="pre">`α`</span> is the type of the arguments to <span class="pre">`Group₂.mul`</span>. In other words, <span class="pre">`{α`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type*}`</span> is the implicit argument for the type of the group elements and <span class="pre">`[Group₂`</span>` `<span class="pre">`α]`</span> is the implicit argument for the group structure on <span class="pre">`α`</span>. Similarly, when we define a generic squaring function <span class="pre">`my_square`</span> for <span class="pre">`Group₂`</span>, we use an implicit argument <span class="pre">`{α`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type*}`</span> for the type of the elements and an implicit argument <span class="pre">`[Group₂`</span>` `<span class="pre">`α]`</span> for the <span class="pre">`Group₂`</span> structure.

In the first example, when we write <span class="pre">`Group₂.mul`</span>` `<span class="pre">`f`</span>` `<span class="pre">`g`</span>, the type of <span class="pre">`f`</span> and <span class="pre">`g`</span> tells Lean that in the argument <span class="pre">`α`</span> to <span class="pre">`Group₂.mul`</span> has to be instantiated to <span class="pre">`Equiv.Perm`</span>` `<span class="pre">`β`</span>. That means that Lean has to find an element of <span class="pre">`Group₂`</span>` `<span class="pre">`(Equiv.Perm`</span>` `<span class="pre">`β)`</span>. The previous <span class="pre">`instance`</span> declaration tells Lean exactly how to do that. Problem solved!

This simple mechanism for registering information so that Lean can find it when it needs it is remarkably useful. Here is one way it comes up. In Lean’s foundation, a data type <span class="pre">`α`</span> may be empty. In a number of applications, however, it is useful to know that a type has at least one element. For example, the function <span class="pre">`List.headI`</span>, which returns the first element of a list, can return the default value when the list is empty. To make that work, the Lean library defines a class <span class="pre">`Inhabited`</span>` `<span class="pre">`α`</span>, which does nothing more than store a default value. We can show that the <span class="pre">`Point`</span> type is an instance:

    instance : Inhabited Point where default := ⟨0, 0, 0⟩

    #check (default : Point)

    example : ([] : List Point).headI = default :=
      rfl

The class inference mechanism is also used for generic notation. The expression <span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`y`</span> is an abbreviation for <span class="pre">`Add.add`</span>` `<span class="pre">`x`</span>` `<span class="pre">`y`</span> where—you guessed it—<span class="pre">`Add`</span>` `<span class="pre">`α`</span> is a class that stores a binary function on <span class="pre">`α`</span>. Writing <span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`y`</span> tells Lean to find a registered instance of <span class="pre">`[Add.add`</span>` `<span class="pre">`α]`</span> and use the corresponding function. Below, we register the addition function for <span class="pre">`Point`</span>.

    instance : Add Point where add := Point.add

    section
    variable (x y : Point)

    #check x + y

    example : x + y = Point.add x y :=
      rfl

    end

In this way, we can assign the notation <span class="pre">`+`</span> to binary operations on other types as well.

But we can do even better. We have seen that <span class="pre">`*`</span> can be used in any group, <span class="pre">`+`</span> can be used in any additive group, and both can be used in any ring. When we define a new instance of a ring in Lean, we don’t have to define <span class="pre">`+`</span> and <span class="pre">`*`</span> for that instance, because Lean knows that these are defined for every ring. We can use this method to specify notation for our <span class="pre">`Group₂`</span> class:

    instance {α : Type*} [Group₂ α] : Mul α :=
      ⟨Group₂.mul⟩

    instance {α : Type*} [Group₂ α] : One α :=
      ⟨Group₂.one⟩

    instance {α : Type*} [Group₂ α] : Inv α :=
      ⟨Group₂.inv⟩

    section
    variable {α : Type*} (f g : Equiv.Perm α)

    #check f * 1 * g⁻¹

    def foo : f * 1 * g⁻¹ = g.symm.trans ((Equiv.refl α).trans f) :=
      rfl

    end

What makes this approach work is that Lean carries out a recursive search. According to the instances we have declared, Lean can find an instance of <span class="pre">`Mul`</span>` `<span class="pre">`(Equiv.Perm`</span>` `<span class="pre">`α)`</span> by finding an instance of <span class="pre">`Group₂`</span>` `<span class="pre">`(Equiv.Perm`</span>` `<span class="pre">`α)`</span>, and it can find an instance of <span class="pre">`Group₂`</span>` `<span class="pre">`(Equiv.Perm`</span>` `<span class="pre">`α)`</span> because we have provided one. Lean is capable of finding these two facts and chaining them together.

The example we have just given is dangerous, because Lean’s library also has an instance of <span class="pre">`Group`</span>` `<span class="pre">`(Equiv.Perm`</span>` `<span class="pre">`α)`</span>, and multiplication is defined on any group. So it is ambiguous as to which instance is found. In fact, Lean favors more recent declarations unless you explicitly specify a different priority. Also, there is another way to tell Lean that one structure is an instance of another, using the <span class="pre">`extends`</span> keyword. This is how Mathlib specifies that, for example, every commutative ring is a ring. You can find more information in <a href="C08_Hierarchies.html#hierarchies" class="reference internal"><span class="std std-numref">Section 8</span></a> and in a <a href="https://leanprover.github.io/theorem_proving_in_lean4/type_classes.html#managing-type-class-inference" class="reference external">section on class inference</a> in *Theorem Proving in Lean*.

In general, it is a bad idea to specify a value of <span class="pre">`*`</span> for an instance of an algebraic structure that already has the notation defined. Redefining the notion of <span class="pre">`Group`</span> in Lean is an artificial example. In this case, however, both interpretations of the group notation unfold to <span class="pre">`Equiv.trans`</span>, <span class="pre">`Equiv.refl`</span>, and <span class="pre">`Equiv.symm`</span>, in the same way.

As a similarly artificial exercise, define a class <span class="pre">`AddGroup₂`</span> in analogy to <span class="pre">`Group₂`</span>. Define the usual notation for addition, negation, and zero on any <span class="pre">`AddGroup₂`</span> using the classes <span class="pre">`Add`</span>, <span class="pre">`Neg`</span>, and <span class="pre">`Zero`</span>. Then show <span class="pre">`Point`</span> is an instance of <span class="pre">`AddGroup₂`</span>. Try it out and make sure that the additive group notation works for elements of <span class="pre">`Point`</span>.

    class AddGroup₂ (α : Type*) where
      add : α → α → α
      -- fill in the rest

It is not a big problem that we have already declared instances <span class="pre">`Add`</span>, <span class="pre">`Neg`</span>, and <span class="pre">`Zero`</span> for <span class="pre">`Point`</span> above. Once again, the two ways of synthesizing the notation should come up with the same answer.

Class inference is subtle, and you have to be careful when using it, because it configures automation that invisibly governs the interpretation of the expressions we type. When used wisely, however, class inference is a powerful tool. It is what makes algebraic reasoning possible in Lean.

<span id="section-building-the-gaussian-integers"></span>

## <span class="section-number">7.3. </span>Building the Gaussian Integers<a href="#building-the-gaussian-integers" class="headerlink" title="Link to this heading"></a>

We will now illustrate the use of the algebraic hierarchy in Lean by building an important mathematical object, the *Gaussian integers*, and showing that it is a Euclidean domain. In other words, according to the terminology we have been using, we will define the Gaussian integers and show that they are an instance of the Euclidean domain structure.

In ordinary mathematical terms, the set of Gaussian integers <span class="math notranslate nohighlight">\\\Bbb{Z}\[i\]\\</span> is the set of complex numbers <span class="math notranslate nohighlight">\\\\ a + b i \mid a, b \in \Bbb{Z}\\\\</span>. But rather than define them as a subset of the complex numbers, our goal here is to define them as a data type in their own right. We do this by representing a Gaussian integer as a pair of integers, which we think of as the *real* and *imaginary* parts.

    @[ext]
    structure GaussInt where
      re : ℤ
      im : ℤ

We first show that the Gaussian integers have the structure of a ring, with <span class="pre">`0`</span> defined to be <span class="pre">`⟨0,`</span>` `<span class="pre">`0⟩`</span>, <span class="pre">`1`</span> defined to be <span class="pre">`⟨1,`</span>` `<span class="pre">`0⟩`</span>, and addition defined pointwise. To work out the definition of multiplication, remember that we want the element <span class="math notranslate nohighlight">\\i\\</span>, represented by <span class="pre">`⟨0,`</span>` `<span class="pre">`1⟩`</span>, to be a square root of <span class="math notranslate nohighlight">\\-1\\</span>. Thus we want

\\\begin{split}(a + bi) (c + di) & = ac + bci + adi + bd i^2 \\ & = (ac - bd) + (bc + ad)i.\end{split}\\

This explains the definition of <span class="pre">`Mul`</span> below.

    instance : Zero GaussInt :=
      ⟨⟨0, 0⟩⟩

    instance : One GaussInt :=
      ⟨⟨1, 0⟩⟩

    instance : Add GaussInt :=
      ⟨fun x y ↦ ⟨x.re + y.re, x.im + y.im⟩⟩

    instance : Neg GaussInt :=
      ⟨fun x ↦ ⟨-x.re, -x.im⟩⟩

    instance : Mul GaussInt :=
      ⟨fun x y ↦ ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

As noted in <a href="#section-structures" class="reference internal"><span class="std std-numref">Section 7.1</span></a>, it is a good idea to put all the definitions related to a data type in a namespace with the same name. Thus in the Lean files associated with this chapter, these definitions are made in the <span class="pre">`GaussInt`</span> namespace.

Notice that here we are defining the interpretations of the notation <span class="pre">`0`</span>, <span class="pre">`1`</span>, <span class="pre">`+`</span>, <span class="pre">`-`</span>, and <span class="pre">`*`</span> directly, rather than naming them <span class="pre">`GaussInt.zero`</span> and the like and assigning the notation to those. It is often useful to have an explicit name for the definitions, for example, to use with <span class="pre">`simp`</span> and <span class="pre">`rw`</span>.

    theorem zero_def : (0 : GaussInt) = ⟨0, 0⟩ :=
      rfl

    theorem one_def : (1 : GaussInt) = ⟨1, 0⟩ :=
      rfl

    theorem add_def (x y : GaussInt) : x + y = ⟨x.re + y.re, x.im + y.im⟩ :=
      rfl

    theorem neg_def (x : GaussInt) : -x = ⟨-x.re, -x.im⟩ :=
      rfl

    theorem mul_def (x y : GaussInt) :
        x * y = ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩ :=
      rfl

It is also useful to name the rules that compute the real and imaginary parts, and to declare them to the simplifier.

    @[simp]
    theorem zero_re : (0 : GaussInt).re = 0 :=
      rfl

    @[simp]
    theorem zero_im : (0 : GaussInt).im = 0 :=
      rfl

    @[simp]
    theorem one_re : (1 : GaussInt).re = 1 :=
      rfl

    @[simp]
    theorem one_im : (1 : GaussInt).im = 0 :=
      rfl

    @[simp]
    theorem add_re (x y : GaussInt) : (x + y).re = x.re + y.re :=
      rfl

    @[simp]
    theorem add_im (x y : GaussInt) : (x + y).im = x.im + y.im :=
      rfl

    @[simp]
    theorem neg_re (x : GaussInt) : (-x).re = -x.re :=
      rfl

    @[simp]
    theorem neg_im (x : GaussInt) : (-x).im = -x.im :=
      rfl

    @[simp]
    theorem mul_re (x y : GaussInt) : (x * y).re = x.re * y.re - x.im * y.im :=
      rfl

    @[simp]
    theorem mul_im (x y : GaussInt) : (x * y).im = x.re * y.im + x.im * y.re :=
      rfl

It is now surprisingly easy to show that the Gaussian integers are an instance of a commutative ring. We are putting the structure concept to good use. Each particular Gaussian integer is an instance of the <span class="pre">`GaussInt`</span> structure, whereas the type <span class="pre">`GaussInt`</span> itself, together with the relevant operations, is an instance of the <span class="pre">`CommRing`</span> structure. The <span class="pre">`CommRing`</span> structure, in turn, extends the notational structures <span class="pre">`Zero`</span>, <span class="pre">`One`</span>, <span class="pre">`Add`</span>, <span class="pre">`Neg`</span>, and <span class="pre">`Mul`</span>.

If you type <span class="pre">`instance`</span>` `<span class="pre">`:`</span>` `<span class="pre">`CommRing`</span>` `<span class="pre">`GaussInt`</span>` `<span class="pre">`:=`</span>` `<span class="pre">`_`</span>, click on the light bulb that appears in VS Code, and then ask Lean to fill in a skeleton for the structure definition, you will see a scary number of entries. Jumping to the definition of the structure, however, shows that many of the fields have default definitions that Lean will fill in for you automatically. The essential ones appear in the definition below. A special case are <span class="pre">`nsmul`</span> and <span class="pre">`zsmul`</span> which should be ignored for now and will be explained in the next chapter. In each case, the relevant identity is proved by unfolding definitions, using the <span class="pre">`ext`</span> tactic to reduce the identities to their real and imaginary components, simplifying, and, if necessary, carrying out the relevant ring calculation in the integers. Note that we could easily avoid repeating all this code, but this is not the topic of the current discussion.

    instance instCommRing : CommRing GaussInt where
      zero := 0
      one := 1
      add := (· + ·)
      neg x := -x
      mul := (· * ·)
      nsmul := nsmulRec
      zsmul := zsmulRec
      add_assoc := by
        intros
        ext <;> simp <;> ring
      zero_add := by
        intro
        ext <;> simp
      add_zero := by
        intro
        ext <;> simp
      neg_add_cancel := by
        intro
        ext <;> simp
      add_comm := by
        intros
        ext <;> simp <;> ring
      mul_assoc := by
        intros
        ext <;> simp <;> ring
      one_mul := by
        intro
        ext <;> simp
      mul_one := by
        intro
        ext <;> simp
      left_distrib := by
        intros
        ext <;> simp <;> ring
      right_distrib := by
        intros
        ext <;> simp <;> ring
      mul_comm := by
        intros
        ext <;> simp <;> ring
      zero_mul := by
        intros
        ext <;> simp
      mul_zero := by
        intros
        ext <;> simp

Lean’s library defines the class of *nontrivial* types to be types with at least two distinct elements. In the context of a ring, this is equivalent to saying that the zero is not equal to the one. Since some common theorems depend on that fact, we may as well establish it now.

    instance : Nontrivial GaussInt := by
      use 0, 1
      rw [Ne, GaussInt.ext_iff]
      simp

We will now show that the Gaussian integers have an important additional property. A *Euclidean domain* is a ring <span class="math notranslate nohighlight">\\R\\</span> equipped with a *norm* function <span class="math notranslate nohighlight">\\N : R \to \mathbb{N}\\</span> with the following two properties:

- For every <span class="math notranslate nohighlight">\\a\\</span> and <span class="math notranslate nohighlight">\\b \ne 0\\</span> in <span class="math notranslate nohighlight">\\R\\</span>, there are <span class="math notranslate nohighlight">\\q\\</span> and <span class="math notranslate nohighlight">\\r\\</span> in <span class="math notranslate nohighlight">\\R\\</span> such that <span class="math notranslate nohighlight">\\a = bq + r\\</span> and either <span class="math notranslate nohighlight">\\r = 0\\</span> or <span class="math notranslate nohighlight">\\N(r) &lt; N(b)\\</span>.

- For every <span class="math notranslate nohighlight">\\a\\</span> and <span class="math notranslate nohighlight">\\b \ne 0\\</span>, <span class="math notranslate nohighlight">\\N(a) \le N(ab)\\</span>.

The ring of integers <span class="math notranslate nohighlight">\\\Bbb{Z}\\</span> with <span class="math notranslate nohighlight">\\N(a) = |a|\\</span> is an archetypal example of a Euclidean domain. In that case, we can take <span class="math notranslate nohighlight">\\q\\</span> to be the result of integer division of <span class="math notranslate nohighlight">\\a\\</span> by <span class="math notranslate nohighlight">\\b\\</span> and <span class="math notranslate nohighlight">\\r\\</span> to be the remainder. These functions are defined in Lean so that the satisfy the following:

    example (a b : ℤ) : a = b * (a / b) + a % b :=
      Eq.symm (Int.ediv_add_emod a b)

    example (a b : ℤ) : b ≠ 0 → 0 ≤ a % b :=
      Int.emod_nonneg a

    example (a b : ℤ) : b ≠ 0 → a % b < |b| :=
      Int.emod_lt_abs a

In an arbitrary ring, an element <span class="math notranslate nohighlight">\\a\\</span> is said to be a *unit* if it divides <span class="math notranslate nohighlight">\\1\\</span>. A nonzero element <span class="math notranslate nohighlight">\\a\\</span> is said to be *irreducible* if it cannot be written in the form <span class="math notranslate nohighlight">\\a = bc\\</span> where neither <span class="math notranslate nohighlight">\\b\\</span> nor <span class="math notranslate nohighlight">\\c\\</span> is a unit. In the integers, every irreducible element <span class="math notranslate nohighlight">\\a\\</span> is *prime*, which is to say, whenever <span class="math notranslate nohighlight">\\a\\</span> divides a product <span class="math notranslate nohighlight">\\bc\\</span>, it divides either <span class="math notranslate nohighlight">\\b\\</span> or <span class="math notranslate nohighlight">\\c\\</span>. But in other rings this property can fail. In the ring <span class="math notranslate nohighlight">\\\Bbb{Z}\[\sqrt{-5}\]\\</span>, we have

\\6 = 2 \cdot 3 = (1 + \sqrt{-5})(1 - \sqrt{-5}),\\

and the elements <span class="math notranslate nohighlight">\\2\\</span>, <span class="math notranslate nohighlight">\\3\\</span>, <span class="math notranslate nohighlight">\\1 + \sqrt{-5}\\</span>, and <span class="math notranslate nohighlight">\\1 - \sqrt{-5}\\</span> are all irreducible, but they are not prime. For example, <span class="math notranslate nohighlight">\\2\\</span> divides the product <span class="math notranslate nohighlight">\\(1 + \sqrt{-5})(1 - \sqrt{-5})\\</span>, but it does not divide either factor. In particular, we no longer have unique factorization: the number <span class="math notranslate nohighlight">\\6\\</span> can be factored into irreducible elements in more than one way.

In contrast, every Euclidean domain is a unique factorization domain, which implies that every irreducible element is prime. The axioms for a Euclidean domain imply that one can write any nonzero element as a finite product of irreducible elements. They also imply that one can use the Euclidean algorithm to find a greatest common divisor of any two nonzero elements <span class="pre">`a`</span> and <span class="pre">`b`</span>, i.e. an element that is divisible by any other common divisor. This, in turn, implies that factorization into irreducible elements is unique up to multiplication by units.

We now show that the Gaussian integers are a Euclidean domain with the norm defined by <span class="math notranslate nohighlight">\\N(a + bi) = (a + bi)(a - bi) = a^2 + b^2\\</span>. The Gaussian integer <span class="math notranslate nohighlight">\\a - bi\\</span> is called the *conjugate* of <span class="math notranslate nohighlight">\\a + bi\\</span>. It is not hard to check that for any complex numbers <span class="math notranslate nohighlight">\\x\\</span> and <span class="math notranslate nohighlight">\\y\\</span>, we have <span class="math notranslate nohighlight">\\N(xy) = N(x)N(y)\\</span>.

To see that this definition of the norm makes the Gaussian integers a Euclidean domain, only the first property is challenging. Suppose we want to write <span class="math notranslate nohighlight">\\a + bi = (c + di) q + r\\</span> for suitable <span class="math notranslate nohighlight">\\q\\</span> and <span class="math notranslate nohighlight">\\r\\</span>. Treating <span class="math notranslate nohighlight">\\a + bi\\</span> and <span class="math notranslate nohighlight">\\c + di\\</span> as complex numbers, carry out the division

\\\frac{a + bi}{c + di} = \frac{(a + bi)(c - di)}{(c + di)(c-di)} = \frac{ac + bd}{c^2 + d^2} + \frac{bc -ad}{c^2+d^2} i.\\

The real and imaginary parts might not be integers, but we can round them to the nearest integers <span class="math notranslate nohighlight">\\u\\</span> and <span class="math notranslate nohighlight">\\v\\</span>. We can then express the right-hand side as <span class="math notranslate nohighlight">\\(u + vi) + (u' + v'i)\\</span>, where <span class="math notranslate nohighlight">\\u' + v'i\\</span> is the part left over. Note that we have <span class="math notranslate nohighlight">\\|u'| \le 1/2\\</span> and <span class="math notranslate nohighlight">\\|v'| \le 1/2\\</span>, and hence

\\N(u' + v' i) = (u')^2 + (v')^2 \le 1/4 + 1/4 \le 1/2.\\

Multiplying through by <span class="math notranslate nohighlight">\\c + di\\</span>, we have

\\a + bi = (c + di) (u + vi) + (c + di) (u' + v'i).\\

Setting <span class="math notranslate nohighlight">\\q = u + vi\\</span> and <span class="math notranslate nohighlight">\\r = (c + di) (u' + v'i)\\</span>, we have <span class="math notranslate nohighlight">\\a + bi = (c + di) q + r\\</span>, and we only need to bound <span class="math notranslate nohighlight">\\N(r)\\</span>:

\\N(r) = N(c + di)N(u' + v'i) \le N(c + di) \cdot 1/2 &lt; N(c + di).\\

The argument we just carried out requires viewing the Gaussian integers as a subset of the complex numbers. One option for formalizing it in Lean is therefore to embed the Gaussian integers in the complex numbers, embed the integers in the Gaussian integers, define the rounding function from the real numbers to the integers, and take great care to pass back and forth between these number systems appropriately. In fact, this is exactly the approach that is followed in Mathlib, where the Gaussian integers themselves are constructed as a special case of a ring of *quadratic integers*. See the file <a href="https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/NumberTheory/Zsqrtd/GaussianInt.lean" class="reference external">GaussianInt.lean</a>.

Here we will instead carry out an argument that stays in the integers. This illustrates a choice one commonly faces when formalizing mathematics. Given an argument that requires concepts or machinery that is not already in the library, one has two choices: either formalize the concepts and machinery needed, or adapt the argument to make use of concepts and machinery you already have. The first choice is generally a good investment of time when the results can be used in other contexts. Pragmatically speaking, however, sometimes seeking a more elementary proof is more efficient.

The usual quotient-remainder theorem for the integers says that for every <span class="math notranslate nohighlight">\\a\\</span> and nonzero <span class="math notranslate nohighlight">\\b\\</span>, there are <span class="math notranslate nohighlight">\\q\\</span> and <span class="math notranslate nohighlight">\\r\\</span> such that <span class="math notranslate nohighlight">\\a = b q + r\\</span> and <span class="math notranslate nohighlight">\\0 \le r &lt; b\\</span>. Here we will make use of the following variation, which says that there are <span class="math notranslate nohighlight">\\q'\\</span> and <span class="math notranslate nohighlight">\\r'\\</span> such that <span class="math notranslate nohighlight">\\a = b q' + r'\\</span> and <span class="math notranslate nohighlight">\\|r'| \le b/2\\</span>. You can check that if the value of <span class="math notranslate nohighlight">\\r\\</span> in the first statement satisfies <span class="math notranslate nohighlight">\\r \le b/2\\</span>, we can take <span class="math notranslate nohighlight">\\q' = q\\</span> and <span class="math notranslate nohighlight">\\r' = r\\</span>, and otherwise we can take <span class="math notranslate nohighlight">\\q' = q + 1\\</span> and <span class="math notranslate nohighlight">\\r' = r - b\\</span>. We are grateful to Heather Macbeth for suggesting the following more elegant approach, which avoids definition by cases. We simply add <span class="pre">`b`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span> to <span class="pre">`a`</span> before dividing and then subtract it from the remainder.

    def div' (a b : ℤ) :=
      (a + b / 2) / b

    def mod' (a b : ℤ) :=
      (a + b / 2) % b - b / 2

    theorem div'_add_mod' (a b : ℤ) : b * div' a b + mod' a b = a := by
      rw [div', mod']
      linarith [Int.ediv_add_emod (a + b / 2) b]

    theorem abs_mod'_le (a b : ℤ) (h : 0 < b) : |mod' a b| ≤ b / 2 := by
      rw [mod', abs_le]
      constructor
      · linarith [Int.emod_nonneg (a + b / 2) h.ne']
      have := Int.emod_lt_of_pos (a + b / 2) h
      have := Int.ediv_add_emod b 2
      have := Int.emod_lt_of_pos b zero_lt_two
      linarith

Note the use of our old friend, <span class="pre">`linarith`</span>. We will also need to express <span class="pre">`mod'`</span> in terms of <span class="pre">`div'`</span>.

    theorem mod'_eq (a b : ℤ) : mod' a b = a - b * div' a b := by linarith [div'_add_mod' a b]

We will use the fact that <span class="math notranslate nohighlight">\\x^2 + y^2\\</span> is equal to zero if and only if <span class="math notranslate nohighlight">\\x\\</span> and <span class="math notranslate nohighlight">\\y\\</span> are both zero. As an exercise, we ask you to prove that this holds in any ordered ring.

    theorem sq_add_sq_eq_zero {α : Type*} [Ring α] [LinearOrder α] [IsStrictOrderedRing α]
        (x y : α) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 := by
      sorry

We will put all the remaining definitions and theorems in this section in the <span class="pre">`GaussInt`</span> namespace. First, we define the <span class="pre">`norm`</span> function and ask you to establish some of its properties. The proofs are all short.

    def norm (x : GaussInt) :=
      x.re ^ 2 + x.im ^ 2

    @[simp]
    theorem norm_nonneg (x : GaussInt) : 0 ≤ norm x := by
      sorry
    theorem norm_eq_zero (x : GaussInt) : norm x = 0 ↔ x = 0 := by
      sorry
    theorem norm_pos (x : GaussInt) : 0 < norm x ↔ x ≠ 0 := by
      sorry
    theorem norm_mul (x y : GaussInt) : norm (x * y) = norm x * norm y := by
      sorry

Next we define the conjugate function:

    def conj (x : GaussInt) : GaussInt :=
      ⟨x.re, -x.im⟩

    @[simp]
    theorem conj_re (x : GaussInt) : (conj x).re = x.re :=
      rfl

    @[simp]
    theorem conj_im (x : GaussInt) : (conj x).im = -x.im :=
      rfl

    theorem norm_conj (x : GaussInt) : norm (conj x) = norm x := by simp [norm]

Finally, we define division for the Gaussian integers with the notation <span class="pre">`x`</span>` `<span class="pre">`/`</span>` `<span class="pre">`y`</span>, that rounds the complex quotient to the nearest Gaussian integer. We use our bespoke <span class="pre">`Int.div'`</span> for that purpose. As we calculated above, if <span class="pre">`x`</span> is <span class="math notranslate nohighlight">\\a + bi\\</span> and <span class="pre">`y`</span> is <span class="math notranslate nohighlight">\\c + di\\</span>, then the real and imaginary parts of <span class="pre">`x`</span>` `<span class="pre">`/`</span>` `<span class="pre">`y`</span> are the nearest integers to

\\\frac{ac + bd}{c^2 + d^2} \quad \text{and} \quad \frac{bc -ad}{c^2+d^2},\\

respectively. Here the numerators are the real and imaginary parts of <span class="math notranslate nohighlight">\\(a + bi) (c - di)\\</span>, and the denominators are both equal to the norm of <span class="math notranslate nohighlight">\\c + di\\</span>.

    instance : Div GaussInt :=
      ⟨fun x y ↦ ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩⟩

Having defined <span class="pre">`x`</span>` `<span class="pre">`/`</span>` `<span class="pre">`y`</span>, We define <span class="pre">`x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y`</span> to be the remainder, <span class="pre">`x`</span>` `<span class="pre">`-`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`/`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span>. As above, we record the definitions in the theorems <span class="pre">`div_def`</span> and <span class="pre">`mod_def`</span> so that we can use them with <span class="pre">`simp`</span> and <span class="pre">`rw`</span>.

    instance : Mod GaussInt :=
      ⟨fun x y ↦ x - y * (x / y)⟩

    theorem div_def (x y : GaussInt) :
        x / y = ⟨Int.div' (x * conj y).re (norm y), Int.div' (x * conj y).im (norm y)⟩ :=
      rfl

    theorem mod_def (x y : GaussInt) : x % y = x - y * (x / y) :=
      rfl

These definitions immediately yield <span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y`</span>` `<span class="pre">`*`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`/`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`+`</span>` `<span class="pre">`x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y`</span> for every <span class="pre">`x`</span> and <span class="pre">`y`</span>, so all we need to do is show that the norm of <span class="pre">`x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y`</span> is less than the norm of <span class="pre">`y`</span> when <span class="pre">`y`</span> is not zero.

We just defined the real and imaginary parts of <span class="pre">`x`</span>` `<span class="pre">`/`</span>` `<span class="pre">`y`</span> to be <span class="pre">`div'`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y).re`</span>` `<span class="pre">`(norm`</span>` `<span class="pre">`y)`</span> and <span class="pre">`div'`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y).im`</span>` `<span class="pre">`(norm`</span>` `<span class="pre">`y)`</span>, respectively. Calculating, we have

> <span class="pre">`(x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`-`</span>` `<span class="pre">`x`</span>` `<span class="pre">`/`</span>` `<span class="pre">`y`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y`</span>` `<span class="pre">`-`</span>` `<span class="pre">`x`</span>` `<span class="pre">`/`</span>` `<span class="pre">`y`</span>` `<span class="pre">`*`</span>` `<span class="pre">`(y`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y)`</span>

The real and imaginary parts of the right-hand side are exactly <span class="pre">`mod'`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y).re`</span>` `<span class="pre">`(norm`</span>` `<span class="pre">`y)`</span> and <span class="pre">`mod'`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y).im`</span>` `<span class="pre">`(norm`</span>` `<span class="pre">`y)`</span>. By the properties of <span class="pre">`div'`</span> and <span class="pre">`mod'`</span>, these are guaranteed to be less than or equal to <span class="pre">`norm`</span>` `<span class="pre">`y`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span>. So we have

> <span class="pre">`norm`</span>` `<span class="pre">`((x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`(norm`</span>` `<span class="pre">`y`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2)^2`</span>` `<span class="pre">`+`</span>` `<span class="pre">`(norm`</span>` `<span class="pre">`y`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2)^2`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`(norm`</span>` `<span class="pre">`y`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`norm`</span>` `<span class="pre">`y`</span>.

On the other hand, we have

> <span class="pre">`norm`</span>` `<span class="pre">`((x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`conj`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`=`</span>` `<span class="pre">`norm`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`norm`</span>` `<span class="pre">`(conj`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`=`</span>` `<span class="pre">`norm`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`norm`</span>` `<span class="pre">`y`</span>.

Dividing through by <span class="pre">`norm`</span>` `<span class="pre">`y`</span> we have <span class="pre">`norm`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`%`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`(norm`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span>` `<span class="pre">`<`</span>` `<span class="pre">`norm`</span>` `<span class="pre">`y`</span>, as required.

This messy calculation is carried out in the next proof. We encourage you to step through the details and see if you can find a nicer argument.

    theorem norm_mod_lt (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
        (x % y).norm < y.norm := by
      have norm_y_pos : 0 < norm y := by rwa [norm_pos]
      have H1 : x % y * conj y = ⟨Int.mod' (x * conj y).re (norm y), Int.mod' (x * conj y).im (norm y)⟩
      · ext <;> simp [Int.mod'_eq, mod_def, div_def, norm] <;> ring
      have H2 : norm (x % y) * norm y ≤ norm y / 2 * norm y
      · calc
          norm (x % y) * norm y = norm (x % y * conj y) := by simp only [norm_mul, norm_conj]
          _ = |Int.mod' (x.re * y.re + x.im * y.im) (norm y)| ^ 2
              + |Int.mod' (-(x.re * y.im) + x.im * y.re) (norm y)| ^ 2 := by simp [H1, norm, sq_abs]
          _ ≤ (y.norm / 2) ^ 2 + (y.norm / 2) ^ 2 := by gcongr <;> apply Int.abs_mod'_le _ _ norm_y_pos
          _ = norm y / 2 * (norm y / 2 * 2) := by ring
          _ ≤ norm y / 2 * norm y := by gcongr; apply Int.ediv_mul_le; norm_num
      calc norm (x % y) ≤ norm y / 2 := le_of_mul_le_mul_right H2 norm_y_pos
        _ < norm y := by
            apply Int.ediv_lt_of_lt_mul
            · norm_num
            · linarith

We are in the home stretch. Our <span class="pre">`norm`</span> function maps Gaussian integers to nonnegative integers. We need a function that maps Gaussian integers to natural numbers, and we obtain that by composing <span class="pre">`norm`</span> with the function <span class="pre">`Int.natAbs`</span>, which maps integers to the natural numbers. The first of the next two lemmas establishes that mapping the norm to the natural numbers and back to the integers does not change the value. The second one re-expresses the fact that the norm is decreasing.

    theorem coe_natAbs_norm (x : GaussInt) : (x.norm.natAbs : ℤ) = x.norm :=
      Int.natAbs_of_nonneg (norm_nonneg _)

    theorem natAbs_norm_mod_lt (x y : GaussInt) (hy : y ≠ 0) :
        (x % y).norm.natAbs < y.norm.natAbs := by
      apply Int.ofNat_lt.1
      simp only [Int.natCast_natAbs, abs_of_nonneg, norm_nonneg]
      exact norm_mod_lt x hy

We also need to establish the second key property of the norm function on a Euclidean domain.

    theorem not_norm_mul_left_lt_norm (x : GaussInt) {y : GaussInt} (hy : y ≠ 0) :
        ¬(norm (x * y)).natAbs < (norm x).natAbs := by
      apply not_lt_of_ge
      rw [norm_mul, Int.natAbs_mul]
      apply le_mul_of_one_le_right (Nat.zero_le _)
      apply Int.ofNat_le.1
      rw [coe_natAbs_norm]
      exact Int.add_one_le_of_lt ((norm_pos _).mpr hy)

We can now put it together to show that the Gaussian integers are an instance of a Euclidean domain. We use the quotient and remainder function we have defined. The Mathlib definition of a Euclidean domain is more general than the one above in that it allows us to show that remainder decreases with respect to any well-founded measure. Comparing the values of a norm function that returns natural numbers is just one instance of such a measure, and in that case, the required properties are the theorems <span class="pre">`natAbs_norm_mod_lt`</span> and <span class="pre">`not_norm_mul_left_lt_norm`</span>.

    instance : EuclideanDomain GaussInt :=
      { GaussInt.instCommRing with
        quotient := (· / ·)
        remainder := (· % ·)
        quotient_mul_add_remainder_eq :=
          fun x y ↦ by rw [mod_def, add_comm] ; ring
        quotient_zero := fun x ↦ by
          simp [div_def, norm, Int.div']
          rfl
        r := (measure (Int.natAbs ∘ norm)).1
        r_wellFounded := (measure (Int.natAbs ∘ norm)).2
        remainder_lt := natAbs_norm_mod_lt
        mul_left_not_lt := not_norm_mul_left_lt_norm }

An immediate payoff is that we now know that, in the Gaussian integers, the notions of being prime and being irreducible coincide.

    example (x : GaussInt) : Irreducible x ↔ Prime x :=
      irreducible_iff_prime
