<span id="topology"></span><span id="id1"></span>

# <span class="section-number">11. </span>Topology<a href="#index-0" class="headerlink" title="Link to this heading"></a>

Calculus is based on the concept of a function, which is used to model quantities that depend on one another. For example, it is common to study quantities that change over time. The notion of a *limit* is also fundamental. We may say that the limit of a function <span class="math notranslate nohighlight">\\f(x)\\</span> is a value <span class="math notranslate nohighlight">\\b\\</span> as <span class="math notranslate nohighlight">\\x\\</span> approaches a value <span class="math notranslate nohighlight">\\a\\</span>, or that <span class="math notranslate nohighlight">\\f(x)\\</span> *converges to* <span class="math notranslate nohighlight">\\b\\</span> as <span class="math notranslate nohighlight">\\x\\</span> approaches <span class="math notranslate nohighlight">\\a\\</span>. Equivalently, we may say that <span class="math notranslate nohighlight">\\f(x)\\</span> approaches <span class="math notranslate nohighlight">\\b\\</span> as <span class="math notranslate nohighlight">\\x\\</span> approaches a value <span class="math notranslate nohighlight">\\a\\</span>, or that it *tends to* <span class="math notranslate nohighlight">\\b\\</span> as <span class="math notranslate nohighlight">\\x\\</span> tends to <span class="math notranslate nohighlight">\\a\\</span>. We have already begun to consider such notions in <a href="C03_Logic.html#sequences-and-convergence" class="reference internal"><span class="std std-numref">Section 3.6</span></a>.

*Topology* is the abstract study of limits and continuity. Having covered the essentials of formalization in Chapters <a href="C02_Basics.html#basics" class="reference internal"><span class="std std-numref">2</span></a> to <a href="C07_Structures.html#structures" class="reference internal"><span class="std std-numref">7</span></a>, in this chapter, we will explain how topological notions are formalized in Mathlib. Not only do topological abstractions apply in much greater generality, but they also, somewhat paradoxically, make it easier to reason about limits and continuity in concrete instances.

Topological notions build on quite a few layers of mathematical structure. The first layer is naive set theory, as described in <a href="C04_Sets_and_Functions.html#sets-and-functions" class="reference internal"><span class="std std-numref">Chapter 4</span></a>. The next layer is the theory of *filters*, which we will describe in <a href="#filters" class="reference internal"><span class="std std-numref">Section 11.1</span></a>. On top of that, we layer the theories of *topological spaces*, *metric spaces*, and a slightly more exotic intermediate notion called a *uniform space*.

Whereas previous chapters relied on mathematical notions that were likely familiar to you, the notion of a filter is less well known, even to many working mathematicians. The notion is essential, however, for formalizing mathematics effectively. Let us explain why. Let <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> be any function. We can consider the limit of <span class="pre">`f`</span>` `<span class="pre">`x`</span> as <span class="pre">`x`</span> approaches some value <span class="pre">`x₀`</span>, but we can also consider the limit of <span class="pre">`f`</span>` `<span class="pre">`x`</span> as <span class="pre">`x`</span> approaches infinity or negative infinity. We can moreover consider the limit of <span class="pre">`f`</span>` `<span class="pre">`x`</span> as <span class="pre">`x`</span> approaches <span class="pre">`x₀`</span> from the right, conventionally written <span class="pre">`x₀⁺`</span>, or from the left, written <span class="pre">`x₀⁻`</span>. There are variations where <span class="pre">`x`</span> approaches <span class="pre">`x₀`</span> or <span class="pre">`x₀⁺`</span> or <span class="pre">`x₀⁻`</span> but is not allowed to take on the value <span class="pre">`x₀`</span> itself. This results in at least eight ways that <span class="pre">`x`</span> can approach something. We can also restrict to rational values of <span class="pre">`x`</span> or place other constraints on the domain, but let’s stick to those 8 cases.

We have a similar variety of options on the codomain: we can specify that <span class="pre">`f`</span>` `<span class="pre">`x`</span> approaches a value from the left or right, or that it approaches positive or negative infinity, and so on. For example, we may wish to say that <span class="pre">`f`</span>` `<span class="pre">`x`</span> tends to <span class="pre">`+∞`</span> when <span class="pre">`x`</span> tends to <span class="pre">`x₀`</span> from the right without being equal to <span class="pre">`x₀`</span>. This results in 64 different kinds of limit statements, and we haven’t even begun to deal with limits of sequences, as we did in <a href="C03_Logic.html#sequences-and-convergence" class="reference internal"><span class="std std-numref">Section 3.6</span></a>.

The problem is compounded even further when it comes to the supporting lemmas. For instance, limits compose: if <span class="pre">`f`</span>` `<span class="pre">`x`</span> tends to <span class="pre">`y₀`</span> when <span class="pre">`x`</span> tends to <span class="pre">`x₀`</span> and <span class="pre">`g`</span>` `<span class="pre">`y`</span> tends to <span class="pre">`z₀`</span> when <span class="pre">`y`</span> tends to <span class="pre">`y₀`</span> then <span class="pre">`g`</span>` `<span class="pre">`∘`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span> tends to <span class="pre">`z₀`</span> when <span class="pre">`x`</span> tends to <span class="pre">`x₀`</span>. There are three notions of “tends to” at play here, each of which can be instantiated in any of the eight ways described in the previous paragraph. This results in 512 lemmas, a lot to have to add to a library! Informally, mathematicians generally prove two or three of these and simply note that the rest can be proved “in the same way.” Formalizing mathematics requires making the relevant notion of “sameness” fully explicit, and that is exactly what Bourbaki’s theory of filters manages to do.

<span id="index-1"></span><span id="id2"></span>

## <span class="section-number">11.1. </span>Filters<a href="#filters" class="headerlink" title="Link to this heading"></a>

A *filter* on a type <span class="pre">`X`</span> is a collection of sets of <span class="pre">`X`</span> that satisfies three conditions that we will spell out below. The notion supports two related ideas:

- *limits*, including all the kinds of limits discussed above: finite and infinite limits of sequences, finite and infinite limits of functions at a point or at infinity, and so on.

- *things happening eventually*, including things happening for large enough <span class="pre">`n`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℕ`</span>, or sufficiently near a point <span class="pre">`x`</span>, or for sufficiently close pairs of points, or almost everywhere in the sense of measure theory. Dually, filters can also express the idea of *things happening often*: for arbitrarily large <span class="pre">`n`</span>, at a point in any neighborhood of a given point, etc.

The filters that correspond to these descriptions will be defined later in this section, but we can already name them:

- <span class="pre">`(atTop`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`ℕ)`</span>, made of sets of <span class="pre">`ℕ`</span> containing <span class="pre">`{n`</span>` `<span class="pre">`|`</span>` `<span class="pre">`n`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`N}`</span> for some <span class="pre">`N`</span>

- <span class="pre">`𝓝`</span>` `<span class="pre">`x`</span>, made of neighborhoods of <span class="pre">`x`</span> in a topological space

- <span class="pre">`𝓤`</span>` `<span class="pre">`X`</span>, made of entourages of a uniform space (uniform spaces generalize metric spaces and topological groups)

- <span class="pre">`μ.ae`</span> , made of sets whose complement has zero measure with respect to a measure <span class="pre">`μ`</span>.

The general definition is as follows: a filter <span class="pre">`F`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span> is a collection of sets <span class="pre">`F.sets`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`(Set`</span>` `<span class="pre">`X)`</span> satisfying the following:

- <span class="pre">`F.univ_sets`</span>` `<span class="pre">`:`</span>` `<span class="pre">`univ`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F.sets`</span>

- <span class="pre">`F.sets_of_superset`</span>` `<span class="pre">`:`</span>` `<span class="pre">`∀`</span>` `<span class="pre">`{U`</span>` `<span class="pre">`V},`</span>` `<span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F.sets`</span>` `<span class="pre">`→`</span>` `<span class="pre">`U`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`V`</span>` `<span class="pre">`→`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F.sets`</span>

- <span class="pre">`F.inter_sets`</span>` `<span class="pre">`:`</span>` `<span class="pre">`∀`</span>` `<span class="pre">`{U`</span>` `<span class="pre">`V},`</span>` `<span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F.sets`</span>` `<span class="pre">`→`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F.sets`</span>` `<span class="pre">`→`</span>` `<span class="pre">`U`</span>` `<span class="pre">`∩`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F.sets`</span>.

The first condition says that the set of all elements of <span class="pre">`X`</span> belongs to <span class="pre">`F.sets`</span>. The second condition says that if <span class="pre">`U`</span> belongs to <span class="pre">`F.sets`</span> then anything containing <span class="pre">`U`</span> also belongs to <span class="pre">`F.sets`</span>. The third condition says that <span class="pre">`F.sets`</span> is closed under finite intersections. In Mathlib, a filter <span class="pre">`F`</span> is defined to be a structure bundling <span class="pre">`F.sets`</span> and its three properties, but the properties carry no additional data, and it is convenient to blur the distinction between <span class="pre">`F`</span> and <span class="pre">`F.sets`</span>. We therefore define <span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span> to mean <span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F.sets`</span>. This explains why the word <span class="pre">`sets`</span> appears in the names of some lemmas that that mention <span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span>.

It may help to think of a filter as defining a notion of a “sufficiently large” set. The first condition then says that <span class="pre">`univ`</span> is sufficiently large, the second one says that a set containing a sufficiently large set is sufficiently large and the third one says that the intersection of two sufficiently large sets is sufficiently large.

It may be even more useful to think of a filter on a type <span class="pre">`X`</span> as a generalized element of <span class="pre">`Set`</span>` `<span class="pre">`X`</span>. For instance, <span class="pre">`atTop`</span> is the “set of very large numbers” and <span class="pre">`𝓝`</span>` `<span class="pre">`x₀`</span> is the “set of points very close to <span class="pre">`x₀`</span>.” One manifestation of this view is that we can associate to any <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`X`</span> the so-called *principal filter* consisting of all sets that contain <span class="pre">`s`</span>. This definition is already in Mathlib and has a notation <span class="pre">`𝓟`</span> (localized in the <span class="pre">`Filter`</span> namespace). For the purpose of demonstration, we ask you to take this opportunity to work out the definition here.

    def principal {α : Type*} (s : Set α) : Filter α
        where
      sets := { t | s ⊆ t }
      univ_sets := sorry
      sets_of_superset := sorry
      inter_sets := sorry

For our second example, we ask you to define the filter <span class="pre">`atTop`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`ℕ`</span>. (We could use any type with a preorder instead of <span class="pre">`ℕ`</span>.)

    example : Filter ℕ :=
      { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
        univ_sets := sorry
        sets_of_superset := sorry
        inter_sets := sorry }

We can also directly define the filter <span class="pre">`𝓝`</span>` `<span class="pre">`x`</span> of neighborhoods of any <span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>. In the real numbers, a neighborhood of <span class="pre">`x`</span> is a set containing an open interval <span class="math notranslate nohighlight">\\(x\_0 - \varepsilon, x\_0 + \varepsilon)\\</span>, defined in Mathlib as <span class="pre">`Ioo`</span>` `<span class="pre">`(x₀`</span>` `<span class="pre">`-`</span>` `<span class="pre">`ε)`</span>` `<span class="pre">`(x₀`</span>` `<span class="pre">`+`</span>` `<span class="pre">`ε)`</span>. (This notion of a neighborhood is only a special case of a more general construction in Mathlib.)

With these examples, we can already define what it means for a function <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Y`</span> to converge to some <span class="pre">`G`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`Y`</span> along some <span class="pre">`F`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span>, as follows:

    def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
      ∀ V ∈ G, f ⁻¹' V ∈ F

When <span class="pre">`X`</span> is <span class="pre">`ℕ`</span> and <span class="pre">`Y`</span> is <span class="pre">`ℝ`</span>, <span class="pre">`Tendsto₁`</span>` `<span class="pre">`u`</span>` `<span class="pre">`atTop`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x)`</span> is equivalent to saying that the sequence <span class="pre">`u`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℕ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> converges to the real number <span class="pre">`x`</span>. When both <span class="pre">`X`</span> and <span class="pre">`Y`</span> are <span class="pre">`ℝ`</span>, <span class="pre">`Tendsto`</span>` `<span class="pre">`f`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x₀)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`y₀)`</span> is equivalent to the familiar notion <span class="math notranslate nohighlight">\\\lim\_{x \to x₀} f(x) = y₀\\</span>. All of the other kinds of limits mentioned in the introduction are also equivalent to instances of <span class="pre">`Tendsto₁`</span> for suitable choices of filters on the source and target.

The notion <span class="pre">`Tendsto₁`</span> above is definitionally equivalent to the notion <span class="pre">`Tendsto`</span> that is defined in Mathlib, but the latter is defined more abstractly. The problem with the definition of <span class="pre">`Tendsto₁`</span> is that it exposes a quantifier and elements of <span class="pre">`G`</span>, and it hides the intuition that we get by viewing filters as generalized sets. We can hide the quantifier <span class="pre">`∀`</span>` `<span class="pre">`V`</span> and make the intuition more salient by using more algebraic and set-theoretic machinery. The first ingredient is the *pushforward* operation <span class="math notranslate nohighlight">\\f\_\*\\</span> associated to any map <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Y`</span>, denoted <span class="pre">`Filter.map`</span>` `<span class="pre">`f`</span> in Mathlib. Given a filter <span class="pre">`F`</span> on <span class="pre">`X`</span>, <span class="pre">`Filter.map`</span>` `<span class="pre">`f`</span>` `<span class="pre">`F`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`Y`</span> is defined so that <span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`Filter.map`</span>` `<span class="pre">`f`</span>` `<span class="pre">`F`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`f`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span> holds definitionally. In the example file we’ve opened the <span class="pre">`Filter`</span> namespace so that <span class="pre">`Filter.map`</span> can be written as <span class="pre">`map`</span>. This means that we can rewrite the definition of <span class="pre">`Tendsto`</span> using the order relation on <span class="pre">`Filter`</span>` `<span class="pre">`Y`</span>, which is reversed inclusion of the set of members. In other words, given <span class="pre">`G`</span>` `<span class="pre">`H`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`Y`</span>, we have <span class="pre">`G`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`H`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`∀`</span>` `<span class="pre">`V`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`Y,`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`H`</span>` `<span class="pre">`→`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`G`</span>.

    def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
      map f F ≤ G

    example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
        Tendsto₂ f F G ↔ Tendsto₁ f F G :=
      Iff.rfl

It may seem that the order relation on filters is backward. But recall that we can view filters on <span class="pre">`X`</span> as generalized elements of <span class="pre">`Set`</span>` `<span class="pre">`X`</span>, via the inclusion of <span class="pre">`𝓟`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span> which maps any set <span class="pre">`s`</span> to the corresponding principal filter. This inclusion is order preserving, so the order relation on <span class="pre">`Filter`</span> can indeed be seen as the natural inclusion relation between generalized sets. In this analogy, pushforward is analogous to the direct image. And, indeed, <span class="pre">`map`</span>` `<span class="pre">`f`</span>` `<span class="pre">`(𝓟`</span>` `<span class="pre">`s)`</span>` `<span class="pre">`=`</span>` `<span class="pre">`𝓟`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`''`</span>` `<span class="pre">`s)`</span>.

We can now understand intuitively why a sequence <span class="pre">`u`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℕ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> converges to a point <span class="pre">`x₀`</span> if and only if we have <span class="pre">`map`</span>` `<span class="pre">`u`</span>` `<span class="pre">`atTop`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`𝓝`</span>` `<span class="pre">`x₀`</span>. The inequality means the “direct image under <span class="pre">`u`</span>” of “the set of very big natural numbers” is “included” in “the set of points very close to <span class="pre">`x₀`</span>.”

As promised, the definition of <span class="pre">`Tendsto₂`</span> does not exhibit any quantifiers or sets. It also leverages the algebraic properties of the pushforward operation. First, each <span class="pre">`Filter.map`</span>` `<span class="pre">`f`</span> is monotone. And, second, <span class="pre">`Filter.map`</span> is compatible with composition.

    #check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

    #check
      (@Filter.map_map :
        ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

Together these two properties allow us to prove that limits compose, yielding in one shot all 512 variants of the composition lemma described in the introduction, and lots more. You can practice proving the following statement using either the definition of <span class="pre">`Tendsto₁`</span> in terms of the universal quantifier or the algebraic definition, together with the two lemmas above.

    example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
        (hf : Tendsto₁ f F G) (hg : Tendsto₁ g G H) : Tendsto₁ (g ∘ f) F H :=
      sorry

The pushforward construction uses a map to push filters from the map source to the map target. There also a *pullback* operation, <span class="pre">`Filter.comap`</span>, going in the other direction. This generalizes the preimage operation on sets. For any map <span class="pre">`f`</span>, <span class="pre">`Filter.map`</span>` `<span class="pre">`f`</span> and <span class="pre">`Filter.comap`</span>` `<span class="pre">`f`</span> form what is known as a *Galois connection*, which is to say, they satisfy

> <span class="pre">`Filter.map_le_iff_le_comap`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter.map`</span>` `<span class="pre">`f`</span>` `<span class="pre">`F`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`G`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`F`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`Filter.comap`</span>` `<span class="pre">`f`</span>` `<span class="pre">`G`</span>

for every <span class="pre">`F`</span> and <span class="pre">`G`</span>. This operation could be used to provided another formulation of <span class="pre">`Tendsto`</span> that would be provably (but not definitionally) equivalent to the one in Mathlib.

The <span class="pre">`comap`</span> operation can be used to restrict filters to a subtype. For instance, suppose we have <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span>, <span class="pre">`x₀`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span> and <span class="pre">`y₀`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>, and suppose we want to state that <span class="pre">`f`</span>` `<span class="pre">`x`</span> approaches <span class="pre">`y₀`</span> when <span class="pre">`x`</span> approaches <span class="pre">`x₀`</span> within the rational numbers. We can pull the filter <span class="pre">`𝓝`</span>` `<span class="pre">`x₀`</span> back to <span class="pre">`ℚ`</span> using the coercion map <span class="pre">`(↑)`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℚ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> and state <span class="pre">`Tendsto`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`∘`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℚ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ)`</span>` `<span class="pre">`(comap`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x₀))`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`y₀)`</span>.

    variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

    #check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

    #check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

The pullback operation is also compatible with composition, but it is *contravariant*, which is to say, it reverses the order of the arguments.

    section
    variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

    #check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

    end

Let’s now shift attention to the plane <span class="pre">`ℝ`</span>` `<span class="pre">`×`</span>` `<span class="pre">`ℝ`</span> and try to understand how the neighborhoods of a point <span class="pre">`(x₀,`</span>` `<span class="pre">`y₀)`</span> are related to <span class="pre">`𝓝`</span>` `<span class="pre">`x₀`</span> and <span class="pre">`𝓝`</span>` `<span class="pre">`y₀`</span>. There is a product operation <span class="pre">`Filter.prod`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`Y`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`(X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`Y)`</span>, denoted by <span class="pre">`×ˢ`</span>, which answers this question:

    example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
      nhds_prod_eq

The product operation is defined in terms of the pullback operation and the <span class="pre">`inf`</span> operation:

> <span class="pre">`F`</span>` `<span class="pre">`×ˢ`</span>` `<span class="pre">`G`</span>` `<span class="pre">`=`</span>` `<span class="pre">`(comap`</span>` `<span class="pre">`Prod.fst`</span>` `<span class="pre">`F)`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`(comap`</span>` `<span class="pre">`Prod.snd`</span>` `<span class="pre">`G)`</span>.

Here the <span class="pre">`inf`</span> operation refers to the lattice structure on <span class="pre">`Filter`</span>` `<span class="pre">`X`</span> for any type <span class="pre">`X`</span>, whereby <span class="pre">`F`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`G`</span> is the greatest filter that is smaller than both <span class="pre">`F`</span> and <span class="pre">`G`</span>. Thus the <span class="pre">`inf`</span> operation generalizes the notion of the intersection of sets.

A lot of proofs in Mathlib use all of the aforementioned structure (<span class="pre">`map`</span>, <span class="pre">`comap`</span>, <span class="pre">`inf`</span>, <span class="pre">`sup`</span>, and <span class="pre">`prod`</span>) to give algebraic proofs about convergence without ever referring to members of filters. You can practice doing this in a proof of the following lemma, unfolding the definition of <span class="pre">`Tendsto`</span> and <span class="pre">`Filter.prod`</span> if needed.

    #check le_inf_iff

    example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
        Tendsto f atTop (𝓝 (x₀, y₀)) ↔
          Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) :=
      sorry

The ordered type <span class="pre">`Filter`</span>` `<span class="pre">`X`</span> is actually a *complete* lattice, which is to say, there is a bottom element, there is a top element, and every set of filters on <span class="pre">`X`</span> has an <span class="pre">`Inf`</span> and a <span class="pre">`Sup`</span>.

Note that given the second property in the definition of a filter (if <span class="pre">`U`</span> belongs to <span class="pre">`F`</span> then anything larger than <span class="pre">`U`</span> also belongs to <span class="pre">`F`</span>), the first property (the set of all inhabitants of <span class="pre">`X`</span> belongs to <span class="pre">`F`</span>) is equivalent to the property that <span class="pre">`F`</span> is not the empty collection of sets. This shouldn’t be confused with the more subtle question as to whether the empty set is an *element* of <span class="pre">`F`</span>. The definition of a filter does not prohibit <span class="pre">`∅`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span>, but if the empty set is in <span class="pre">`F`</span> then every set is in <span class="pre">`F`</span>, which is to say, <span class="pre">`∀`</span>` `<span class="pre">`U`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`X,`</span>` `<span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span>. In this case, <span class="pre">`F`</span> is a rather trivial filter, which is precisely the bottom element of the complete lattice <span class="pre">`Filter`</span>` `<span class="pre">`X`</span>. This contrasts with the definition of filters in Bourbaki, which doesn’t allow filters containing the empty set.

Because we include the trivial filter in our definition, we sometimes need to explicitly assume nontriviality in some lemmas. In return, however, the theory has nicer global properties. We have already seen that including the trivial filter gives us a bottom element. It also allows us to define <span class="pre">`principal`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span>, which maps <span class="pre">`∅`</span> to <span class="pre">`⊥`</span>, without adding a precondition to rule out the empty set. And it allows us to define the pullback operation without a precondition as well. Indeed, it can happen that <span class="pre">`comap`</span>` `<span class="pre">`f`</span>` `<span class="pre">`F`</span>` `<span class="pre">`=`</span>` `<span class="pre">`⊥`</span> although <span class="pre">`F`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`⊥`</span>. For instance, given <span class="pre">`x₀`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span> and <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`ℝ`</span>, the pullback of <span class="pre">`𝓝`</span>` `<span class="pre">`x₀`</span> under the coercion from the subtype corresponding to <span class="pre">`s`</span> is nontrivial if and only if <span class="pre">`x₀`</span> belongs to the closure of <span class="pre">`s`</span>.

In order to manage lemmas that do need to assume some filter is nontrivial, Mathlib has a type class <span class="pre">`Filter.NeBot`</span>, and the library has lemmas that assume <span class="pre">`(F`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X)`</span>` `<span class="pre">`[F.NeBot]`</span>. The instance database knows, for example, that <span class="pre">`(atTop`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`ℕ).NeBot`</span>, and it knows that pushing forward a nontrivial filter gives a nontrivial filter. As a result, a lemma assuming <span class="pre">`[F.NeBot]`</span> will automatically apply to <span class="pre">`map`</span>` `<span class="pre">`u`</span>` `<span class="pre">`atTop`</span> for any sequence <span class="pre">`u`</span>.

Our tour of the algebraic properties of filters and their relation to limits is essentially done, but we have not yet justified our claim to have recaptured the usual limit notions. Superficially, it may seem that <span class="pre">`Tendsto`</span>` `<span class="pre">`u`</span>` `<span class="pre">`atTop`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x₀)`</span> is stronger than the notion of convergence defined in <a href="C03_Logic.html#sequences-and-convergence" class="reference internal"><span class="std std-numref">Section 3.6</span></a> because we ask that *every* neighborhood of <span class="pre">`x₀`</span> has a preimage belonging to <span class="pre">`atTop`</span>, whereas the usual definition only requires this for the standard neighborhoods <span class="pre">`Ioo`</span>` `<span class="pre">`(x₀`</span>` `<span class="pre">`-`</span>` `<span class="pre">`ε)`</span>` `<span class="pre">`(x₀`</span>` `<span class="pre">`+`</span>` `<span class="pre">`ε)`</span>. The key is that, by definition, every neighborhood contains such a standard one. This observation leads to the notion of a *filter basis*.

Given <span class="pre">`F`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span>, a family of sets <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ι`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`X`</span> is a basis for <span class="pre">`F`</span> if for every set <span class="pre">`U`</span>, we have <span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span> if and only if it contains some <span class="pre">`s`</span>` `<span class="pre">`i`</span>. In other words, formally speaking, <span class="pre">`s`</span> is a basis if it satisfies <span class="pre">`∀`</span>` `<span class="pre">`U`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`X,`</span>` `<span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`∃`</span>` `<span class="pre">`i,`</span>` `<span class="pre">`s`</span>` `<span class="pre">`i`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`U`</span>. It is even more flexible to consider a predicate on <span class="pre">`ι`</span> that selects only some of the values <span class="pre">`i`</span> in the indexing type. In the case of <span class="pre">`𝓝`</span>` `<span class="pre">`x₀`</span>, we want <span class="pre">`ι`</span> to be <span class="pre">`ℝ`</span>, we write <span class="pre">`ε`</span> for <span class="pre">`i`</span>, and the predicate should select the positive values of <span class="pre">`ε`</span>. So the fact that the sets <span class="pre">`Ioo`</span>`  `<span class="pre">`(x₀`</span>` `<span class="pre">`-`</span>` `<span class="pre">`ε)`</span>` `<span class="pre">`(x₀`</span>` `<span class="pre">`+`</span>` `<span class="pre">`ε)`</span> form a basis for the neighborhood topology on <span class="pre">`ℝ`</span> is stated as follows:

    example (x₀ : ℝ) : HasBasis (𝓝 x₀) (fun ε : ℝ ↦ 0 < ε) fun ε ↦ Ioo (x₀ - ε) (x₀ + ε) :=
      nhds_basis_Ioo_pos x₀

There is also a nice basis for the filter <span class="pre">`atTop`</span>. The lemma <span class="pre">`Filter.HasBasis.tendsto_iff`</span> allows us to reformulate a statement of the form <span class="pre">`Tendsto`</span>` `<span class="pre">`f`</span>` `<span class="pre">`F`</span>` `<span class="pre">`G`</span> given bases for <span class="pre">`F`</span> and <span class="pre">`G`</span>. Putting these pieces together gives us essentially the notion of convergence that we used in <a href="C03_Logic.html#sequences-and-convergence" class="reference internal"><span class="std std-numref">Section 3.6</span></a>.

    example (u : ℕ → ℝ) (x₀ : ℝ) :
        Tendsto u atTop (𝓝 x₀) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, u n ∈ Ioo (x₀ - ε) (x₀ + ε) := by
      have : atTop.HasBasis (fun _ : ℕ ↦ True) Ici := atTop_basis
      rw [this.tendsto_iff (nhds_basis_Ioo_pos x₀)]
      simp

We now show how filters facilitate working with properties that hold for sufficiently large numbers or for points that are sufficiently close to a given point. In <a href="C03_Logic.html#sequences-and-convergence" class="reference internal"><span class="std std-numref">Section 3.6</span></a>, we were often faced with the situation where we knew that some property <span class="pre">`P`</span>` `<span class="pre">`n`</span> holds for sufficiently large <span class="pre">`n`</span> and that some other property <span class="pre">`Q`</span>` `<span class="pre">`n`</span> holds for sufficiently large <span class="pre">`n`</span>. Using <span class="pre">`cases`</span> twice gave us <span class="pre">`N_P`</span> and <span class="pre">`N_Q`</span> satisfying <span class="pre">`∀`</span>` `<span class="pre">`n`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`N_P,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`n`</span> and <span class="pre">`∀`</span>` `<span class="pre">`n`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`N_Q,`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`n`</span>. Using <span class="pre">`set`</span>` `<span class="pre">`N`</span>` `<span class="pre">`:=`</span>` `<span class="pre">`max`</span>` `<span class="pre">`N_P`</span>` `<span class="pre">`N_Q`</span>, we could eventually prove <span class="pre">`∀`</span>` `<span class="pre">`n`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`N,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`n`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`n`</span>. Doing this repeatedly becomes tiresome.

We can do better by noting that the statement “<span class="pre">`P`</span>` `<span class="pre">`n`</span> and <span class="pre">`Q`</span>` `<span class="pre">`n`</span> hold for large enough <span class="pre">`n`</span>” means that we have <span class="pre">`{n`</span>` `<span class="pre">`|`</span>` `<span class="pre">`P`</span>` `<span class="pre">`n}`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`atTop`</span> and <span class="pre">`{n`</span>` `<span class="pre">`|`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`n}`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`atTop`</span>. The fact that <span class="pre">`atTop`</span> is a filter implies that the intersection of two elements of <span class="pre">`atTop`</span> is again in <span class="pre">`atTop`</span>, so we have <span class="pre">`{n`</span>` `<span class="pre">`|`</span>` `<span class="pre">`P`</span>` `<span class="pre">`n`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`n}`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`atTop`</span>. Writing <span class="pre">`{n`</span>` `<span class="pre">`|`</span>` `<span class="pre">`P`</span>` `<span class="pre">`n}`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`atTop`</span> is unpleasant, but we can use the more suggestive notation <span class="pre">`∀ᶠ`</span>` `<span class="pre">`n`</span>` `<span class="pre">`in`</span>` `<span class="pre">`atTop,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`n`</span>. Here the superscripted <span class="pre">`f`</span> stands for “Filter.” You can think of the notation as saying that for all <span class="pre">`n`</span> in the “set of very large numbers,” <span class="pre">`P`</span>` `<span class="pre">`n`</span> holds. The <span class="pre">`∀ᶠ`</span> notation stands for <span class="pre">`Filter.Eventually`</span>, and the lemma <span class="pre">`Filter.Eventually.and`</span> uses the intersection property of filters to do what we just described:

    example (P Q : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n) :
        ∀ᶠ n in atTop, P n ∧ Q n :=
      hP.and hQ

This notation is so convenient and intuitive that we also have specializations when <span class="pre">`P`</span> is an equality or inequality statement. For example, let <span class="pre">`u`</span> and <span class="pre">`v`</span> be two sequences of real numbers, and let us show that if <span class="pre">`u`</span>` `<span class="pre">`n`</span> and <span class="pre">`v`</span>` `<span class="pre">`n`</span> coincide for sufficiently large <span class="pre">`n`</span> then <span class="pre">`u`</span> tends to <span class="pre">`x₀`</span> if and only if <span class="pre">`v`</span> tends to <span class="pre">`x₀`</span>. First we’ll use the generic <span class="pre">`Eventually`</span> and then the one specialized for the equality predicate, <span class="pre">`EventuallyEq`</span>. The two statements are definitionally equivalent so the same proof work in both cases.

    example (u v : ℕ → ℝ) (h : ∀ᶠ n in atTop, u n = v n) (x₀ : ℝ) :
        Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
      tendsto_congr' h

    example (u v : ℕ → ℝ) (h : u =ᶠ[atTop] v) (x₀ : ℝ) :
        Tendsto u atTop (𝓝 x₀) ↔ Tendsto v atTop (𝓝 x₀) :=
      tendsto_congr' h

It is instructive to review the definition of filters in terms of <span class="pre">`Eventually`</span>. Given <span class="pre">`F`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span>, for any predicates <span class="pre">`P`</span> and <span class="pre">`Q`</span> on <span class="pre">`X`</span>,

- the condition <span class="pre">`univ`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span> ensures <span class="pre">`(∀`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`∀ᶠ`</span>` `<span class="pre">`x`</span>` `<span class="pre">`in`</span>` `<span class="pre">`F,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span>,

- the condition <span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span>` `<span class="pre">`→`</span>` `<span class="pre">`U`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`V`</span>` `<span class="pre">`→`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span> ensures <span class="pre">`(∀ᶠ`</span>` `<span class="pre">`x`</span>` `<span class="pre">`in`</span>` `<span class="pre">`F,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`(∀`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`∀ᶠ`</span>` `<span class="pre">`x`</span>` `<span class="pre">`in`</span>` `<span class="pre">`F,`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`x`</span>, and

- the condition <span class="pre">`U`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span>` `<span class="pre">`→`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span>` `<span class="pre">`→`</span>` `<span class="pre">`U`</span>` `<span class="pre">`∩`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`F`</span> ensures <span class="pre">`(∀ᶠ`</span>` `<span class="pre">`x`</span>` `<span class="pre">`in`</span>` `<span class="pre">`F,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`(∀ᶠ`</span>` `<span class="pre">`x`</span>` `<span class="pre">`in`</span>` `<span class="pre">`F,`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`∀ᶠ`</span>` `<span class="pre">`x`</span>` `<span class="pre">`in`</span>` `<span class="pre">`F,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`x`</span>.

    #check Eventually.of_forall
    #check Eventually.mono
    #check Eventually.and

The second item, corresponding to <span class="pre">`Eventually.mono`</span>, supports nice ways of using filters, especially when combined with <span class="pre">`Eventually.and`</span>. The <span class="pre">`filter_upwards`</span> tactic allows us to combine them. Compare:

    example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
        (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
      apply (hP.and (hQ.and hR)).mono
      rintro n ⟨h, h', h''⟩
      exact h'' ⟨h, h'⟩

    example (P Q R : ℕ → Prop) (hP : ∀ᶠ n in atTop, P n) (hQ : ∀ᶠ n in atTop, Q n)
        (hR : ∀ᶠ n in atTop, P n ∧ Q n → R n) : ∀ᶠ n in atTop, R n := by
      filter_upwards [hP, hQ, hR] with n h h' h''
      exact h'' ⟨h, h'⟩

Readers who know about measure theory will note that the filter <span class="pre">`μ.ae`</span> of sets whose complement has measure zero (aka “the set consisting of almost every point”) is not very useful as the source or target of <span class="pre">`Tendsto`</span>, but it can be conveniently used with <span class="pre">`Eventually`</span> to say that a property holds for almost every point.

There is a dual version of <span class="pre">`∀ᶠ`</span>` `<span class="pre">`x`</span>` `<span class="pre">`in`</span>` `<span class="pre">`F,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span>, which is occasionally useful: <span class="pre">`∃ᶠ`</span>` `<span class="pre">`x`</span>` `<span class="pre">`in`</span>` `<span class="pre">`F,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span> means <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`¬P`</span>` `<span class="pre">`x}`</span>` `<span class="pre">`∉`</span>` `<span class="pre">`F`</span>. For example, <span class="pre">`∃ᶠ`</span>` `<span class="pre">`n`</span>` `<span class="pre">`in`</span>` `<span class="pre">`atTop,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`n`</span> means there are arbitrarily large <span class="pre">`n`</span> such that <span class="pre">`P`</span>` `<span class="pre">`n`</span> holds. The <span class="pre">`∃ᶠ`</span> notation stands for <span class="pre">`Filter.Frequently`</span>.

For a more sophisticated example, consider the following statement about a sequence <span class="pre">`u`</span>, a set <span class="pre">`M`</span>, and a value <span class="pre">`x`</span>:

> If <span class="pre">`u`</span> converges to <span class="pre">`x`</span> and <span class="pre">`u`</span>` `<span class="pre">`n`</span> belongs to <span class="pre">`M`</span> for sufficiently large <span class="pre">`n`</span> then <span class="pre">`x`</span> is in the closure of <span class="pre">`M`</span>.

This can be formalized as follows:

> <span class="pre">`Tendsto`</span>` `<span class="pre">`u`</span>` `<span class="pre">`atTop`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`(∀ᶠ`</span>` `<span class="pre">`n`</span>` `<span class="pre">`in`</span>` `<span class="pre">`atTop,`</span>` `<span class="pre">`u`</span>` `<span class="pre">`n`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`M)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`closure`</span>` `<span class="pre">`M`</span>.

This is a special case of the theorem <span class="pre">`mem_closure_of_tendsto`</span> from the topology library. See if you can prove it using the quoted lemmas, using the fact that <span class="pre">`ClusterPt`</span>` `<span class="pre">`x`</span>` `<span class="pre">`F`</span> means <span class="pre">`(𝓝`</span>` `<span class="pre">`x`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`F).NeBot`</span> and that, by definition, the assumption <span class="pre">`∀ᶠ`</span>` `<span class="pre">`n`</span>` `<span class="pre">`in`</span>` `<span class="pre">`atTop,`</span>` `<span class="pre">`u`</span>` `<span class="pre">`n`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`M`</span> means <span class="pre">`M`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`map`</span>` `<span class="pre">`u`</span>` `<span class="pre">`atTop`</span>.

    #check mem_closure_iff_clusterPt
    #check le_principal_iff
    #check neBot_of_le

    example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
        (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
      sorry

<span id="index-2"></span><span id="id3"></span>

## <span class="section-number">11.2. </span>Metric spaces<a href="#metric-spaces" class="headerlink" title="Link to this heading"></a>

Examples in the previous section focus on sequences of real numbers. In this section we will go up a bit in generality and focus on metric spaces. A metric space is a type <span class="pre">`X`</span> equipped with a distance function <span class="pre">`dist`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> which is a generalization of the function <span class="pre">`fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`y`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`|x`</span>` `<span class="pre">`-`</span>` `<span class="pre">`y|`</span> from the case where <span class="pre">`X`</span>` `<span class="pre">`=`</span>` `<span class="pre">`ℝ`</span>.

Introducing such a space is easy and we will check all properties required from the distance function.

    variable {X : Type*} [MetricSpace X] (a b c : X)

    #check (dist a b : ℝ)
    #check (dist_nonneg : 0 ≤ dist a b)
    #check (dist_eq_zero : dist a b = 0 ↔ a = b)
    #check (dist_comm a b : dist a b = dist b a)
    #check (dist_triangle a b c : dist a c ≤ dist a b + dist b c)

Note we also have variants where the distance can be infinite or where <span class="pre">`dist`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span> can be zero without having <span class="pre">`a`</span>` `<span class="pre">`=`</span>` `<span class="pre">`b`</span> or both. They are called <span class="pre">`EMetricSpace`</span>, <span class="pre">`PseudoMetricSpace`</span> and <span class="pre">`PseudoEMetricSpace`</span> respectively (here “e” stands for “extended”).

Note that our journey from <span class="pre">`ℝ`</span> to metric spaces jumped over the special case of normed spaces that also require linear algebra and will be explained as part of the calculus chapter.

### <span class="section-number">11.2.1. </span>Convergence and continuity<a href="#convergence-and-continuity" class="headerlink" title="Link to this heading"></a>

Using distance functions, we can already define convergent sequences and continuous functions between metric spaces. They are actually defined in a more general setting covered in the next section, but we have lemmas recasting the definition in terms of distances.

    example {u : ℕ → X} {a : X} :
        Tendsto u atTop (𝓝 a) ↔ ∀ ε > 0, ∃ N, ∀ n ≥ N, dist (u n) a < ε :=
      Metric.tendsto_atTop

    example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} :
        Continuous f ↔
          ∀ x : X, ∀ ε > 0, ∃ δ > 0, ∀ x', dist x' x < δ → dist (f x') (f x) < ε :=
      Metric.continuous_iff

A *lot* of lemmas have some continuity assumptions, so we end up proving a lot of continuity results and there is a <span class="pre">`continuity`</span> tactic devoted to this task. Let’s prove a continuity statement that will be needed in an exercise below. Notice that Lean knows how to treat a product of two metric spaces as a metric space, so it makes sense to consider continuous functions from <span class="pre">`X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`X`</span> to <span class="pre">`ℝ`</span>. In particular the (uncurried version of the) distance function is such a function.

    example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
        Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by continuity

This tactic is a bit slow, so it is also useful to know how to do it by hand. We first need to use that <span class="pre">`fun`</span>` `<span class="pre">`p`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`X`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`f`</span>` `<span class="pre">`p.1`</span> is continuous because it is the composition of <span class="pre">`f`</span>, which is continuous by assumption <span class="pre">`hf`</span>, and the projection <span class="pre">`prod.fst`</span> whose continuity is the content of the lemma <span class="pre">`continuous_fst`</span>. The composition property is <span class="pre">`Continuous.comp`</span> which is in the <span class="pre">`Continuous`</span> namespace so we can use dot notation to compress <span class="pre">`Continuous.comp`</span>` `<span class="pre">`hf`</span>` `<span class="pre">`continuous_fst`</span> into <span class="pre">`hf.comp`</span>` `<span class="pre">`continuous_fst`</span> which is actually more readable since it really reads as composing our assumption and our lemma. We can do the same for the second component to get continuity of <span class="pre">`fun`</span>` `<span class="pre">`p`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`X`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`f`</span>` `<span class="pre">`p.2`</span>. We then assemble those two continuities using <span class="pre">`Continuous.prod_mk`</span> to get <span class="pre">`(hf.comp`</span>` `<span class="pre">`continuous_fst).prod_mk`</span>` `<span class="pre">`(hf.comp`</span>` `<span class="pre">`continuous_snd)`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Continuous`</span>` `<span class="pre">`(fun`</span>` `<span class="pre">`p`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`X`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`p.1,`</span>` `<span class="pre">`f`</span>` `<span class="pre">`p.2))`</span> and compose once more to get our full proof.

    example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
        Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
      continuous_dist.comp ((hf.comp continuous_fst).prodMk (hf.comp continuous_snd))

The combination of <span class="pre">`Continuous.prod_mk`</span> and <span class="pre">`continuous_dist`</span> via <span class="pre">`Continuous.comp`</span> feels clunky, even when heavily using dot notation as above. A more serious issue is that this nice proof requires a lot of planning. Lean accepts the above proof term because it is a full term proving a statement which is definitionally equivalent to our goal, the crucial definition to unfold being that of a composition of functions. Indeed our target function <span class="pre">`fun`</span>` `<span class="pre">`p`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`X`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`dist`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`p.1)`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`p.2)`</span> is not presented as a composition. The proof term we provided proves continuity of <span class="pre">`dist`</span>` `<span class="pre">`∘`</span>` `<span class="pre">`(fun`</span>` `<span class="pre">`p`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`X`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`p.1,`</span>` `<span class="pre">`f`</span>` `<span class="pre">`p.2))`</span> which happens to be definitionally equal to our target function. But if we try to build this proof gradually using tactics starting with <span class="pre">`apply`</span>` `<span class="pre">`continuous_dist.comp`</span> then Lean’s elaborator will fail to recognize a composition and refuse to apply this lemma. It is especially bad at this when products of types are involved.

A better lemma to apply here is <span class="pre">`Continuous.dist`</span>` `<span class="pre">`{f`</span>` `<span class="pre">`g`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Y}`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Continuous`</span>` `<span class="pre">`f`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Continuous`</span>` `<span class="pre">`g`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Continuous`</span>` `<span class="pre">`(fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`dist`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`(g`</span>` `<span class="pre">`x))`</span> which is nicer to Lean’s elaborator and also provides a shorter proof when directly providing a full proof term, as can be seen from the following two new proofs of the above statement:

    example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
        Continuous fun p : X × X ↦ dist (f p.1) (f p.2) := by
      apply Continuous.dist
      exact hf.comp continuous_fst
      exact hf.comp continuous_snd

    example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
        Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
      (hf.comp continuous_fst).dist (hf.comp continuous_snd)

Note that, without the elaboration issue coming from composition, another way to compress our proof would be to use <span class="pre">`Continuous.prod_map`</span> which is sometimes useful and gives as an alternate proof term <span class="pre">`continuous_dist.comp`</span>` `<span class="pre">`(hf.prod_map`</span>` `<span class="pre">`hf)`</span> which even shorter to type.

Since it is sad to decide between a version which is better for elaboration and a version which is shorter to type, let us wrap this discussion with a last bit of compression offered by <span class="pre">`Continuous.fst'`</span> which allows to compress <span class="pre">`hf.comp`</span>` `<span class="pre">`continuous_fst`</span> to <span class="pre">`hf.fst'`</span> (and the same with <span class="pre">`snd`</span>) and get our final proof, now bordering obfuscation.

    example {X Y : Type*} [MetricSpace X] [MetricSpace Y] {f : X → Y} (hf : Continuous f) :
        Continuous fun p : X × X ↦ dist (f p.1) (f p.2) :=
      hf.fst'.dist hf.snd'

It’s your turn now to prove some continuity lemma. After trying the continuity tactic, you will need <span class="pre">`Continuous.add`</span>, <span class="pre">`continuous_pow`</span> and <span class="pre">`continuous_id`</span> to do it by hand.

    example {f : ℝ → X} (hf : Continuous f) : Continuous fun x : ℝ ↦ f (x ^ 2 + x) :=
      sorry

So far we saw continuity as a global notion, but one can also define continuity at a point.

    example {X Y : Type*} [MetricSpace X] [MetricSpace Y] (f : X → Y) (a : X) :
        ContinuousAt f a ↔ ∀ ε > 0, ∃ δ > 0, ∀ {x}, dist x a < δ → dist (f x) (f a) < ε :=
      Metric.continuousAt_iff

### <span class="section-number">11.2.2. </span>Balls, open sets and closed sets<a href="#balls-open-sets-and-closed-sets" class="headerlink" title="Link to this heading"></a>

Once we have a distance function, the most important geometric definitions are (open) balls and closed balls.

    variable (r : ℝ)

    example : Metric.ball a r = { b | dist b a < r } :=
      rfl

    example : Metric.closedBall a r = { b | dist b a ≤ r } :=
      rfl

Note that r is any real number here, there is no sign restriction. Of course some statements do require a radius condition.

    example (hr : 0 < r) : a ∈ Metric.ball a r :=
      Metric.mem_ball_self hr

    example (hr : 0 ≤ r) : a ∈ Metric.closedBall a r :=
      Metric.mem_closedBall_self hr

Once we have balls, we can define open sets. They are actually defined in a more general setting covered in the next section, but we have lemmas recasting the definition in terms of balls.

    example (s : Set X) : IsOpen s ↔ ∀ x ∈ s, ∃ ε > 0, Metric.ball x ε ⊆ s :=
      Metric.isOpen_iff

Then closed sets are sets whose complement is open. Their important property is they are closed under limits. The closure of a set is the smallest closed set containing it.

    example {s : Set X} : IsClosed s ↔ IsOpen (sᶜ) :=
      isOpen_compl_iff.symm

    example {s : Set X} (hs : IsClosed s) {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a))
        (hus : ∀ n, u n ∈ s) : a ∈ s :=
      hs.mem_of_tendsto hu (Eventually.of_forall hus)

    example {s : Set X} : a ∈ closure s ↔ ∀ ε > 0, ∃ b ∈ s, a ∈ Metric.ball b ε :=
      Metric.mem_closure_iff

Do the next exercise without using mem\_closure\_iff\_seq\_limit

    example {u : ℕ → X} (hu : Tendsto u atTop (𝓝 a)) {s : Set X} (hs : ∀ n, u n ∈ s) :
        a ∈ closure s := by
      sorry

Remember from the filters sections that neighborhood filters play a big role in Mathlib. In the metric space context, the crucial point is that balls provide bases for those filters. The main lemmas here are <span class="pre">`Metric.nhds_basis_ball`</span> and <span class="pre">`Metric.nhds_basis_closedBall`</span> that claim this for open and closed balls with positive radius. The center point is an implicit argument so we can invoke <span class="pre">`Filter.HasBasis.mem_iff`</span> as in the following example.

    example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.ball x ε ⊆ s :=
      Metric.nhds_basis_ball.mem_iff

    example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ ε > 0, Metric.closedBall x ε ⊆ s :=
      Metric.nhds_basis_closedBall.mem_iff

### <span class="section-number">11.2.3. </span>Compactness<a href="#compactness" class="headerlink" title="Link to this heading"></a>

Compactness is an important topological notion. It distinguishes subsets of a metric space that enjoy the same kind of properties as segments in the reals compared to other intervals:

- Any sequence with values in a compact set has a subsequence that converges in this set.

- Any continuous function on a nonempty compact set with values in real numbers is bounded and attains its bounds somewhere (this is called the extreme value theorem).

- Compact sets are closed sets.

Let us first check that the unit interval in the reals is indeed a compact set, and then check the above claims for compact sets in general metric spaces. In the second statement we only need continuity on the given set so we will use <span class="pre">`ContinuousOn`</span> instead of <span class="pre">`Continuous`</span>, and we will give separate statements for the minimum and the maximum. Of course all these results are deduced from more general versions, some of which will be discussed in later sections.

    example : IsCompact (Set.Icc 0 1 : Set ℝ) :=
      isCompact_Icc

    example {s : Set X} (hs : IsCompact s) {u : ℕ → X} (hu : ∀ n, u n ∈ s) :
        ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
      hs.tendsto_subseq hu

    example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
          (hfs : ContinuousOn f s) :
        ∃ x ∈ s, ∀ y ∈ s, f x ≤ f y :=
      hs.exists_isMinOn hs' hfs

    example {s : Set X} (hs : IsCompact s) (hs' : s.Nonempty) {f : X → ℝ}
          (hfs : ContinuousOn f s) :
        ∃ x ∈ s, ∀ y ∈ s, f y ≤ f x :=
      hs.exists_isMaxOn hs' hfs

    example {s : Set X} (hs : IsCompact s) : IsClosed s :=
      hs.isClosed

We can also specify that a metric spaces is globally compact, using an extra <span class="pre">`Prop`</span>-valued type class:

    example {X : Type*} [MetricSpace X] [CompactSpace X] : IsCompact (univ : Set X) :=
      isCompact_univ

In a compact metric space any closed set is compact, this is <span class="pre">`IsClosed.isCompact`</span>.

### <span class="section-number">11.2.4. </span>Uniformly continuous functions<a href="#uniformly-continuous-functions" class="headerlink" title="Link to this heading"></a>

We now turn to uniformity notions on metric spaces : uniformly continuous functions, Cauchy sequences and completeness. Again those are defined in a more general context but we have lemmas in the metric name space to access their elementary definitions. We start with uniform continuity.

    example {X : Type*} [MetricSpace X] {Y : Type*} [MetricSpace Y] {f : X → Y} :
        UniformContinuous f ↔
          ∀ ε > 0, ∃ δ > 0, ∀ {a b : X}, dist a b < δ → dist (f a) (f b) < ε :=
      Metric.uniformContinuous_iff

In order to practice manipulating all those definitions, we will prove that continuous functions from a compact metric space to a metric space are uniformly continuous (we will see a more general version in a later section).

We will first give an informal sketch. Let <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Y`</span> be a continuous function from a compact metric space to a metric space. We fix <span class="pre">`ε`</span>` `<span class="pre">`>`</span>` `<span class="pre">`0`</span> and start looking for some <span class="pre">`δ`</span>.

Let <span class="pre">`φ`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`:=`</span>` `<span class="pre">`fun`</span>` `<span class="pre">`p`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`dist`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`p.1)`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`p.2)`</span> and let <span class="pre">`K`</span>` `<span class="pre">`:=`</span>` `<span class="pre">`{`</span>` `<span class="pre">`p`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`×`</span>` `<span class="pre">`X`</span>` `<span class="pre">`|`</span>` `<span class="pre">`ε`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`φ`</span>` `<span class="pre">`p`</span>` `<span class="pre">`}`</span>. Observe <span class="pre">`φ`</span> is continuous since <span class="pre">`f`</span> and distance are continuous. And <span class="pre">`K`</span> is clearly closed (use <span class="pre">`isClosed_le`</span>) hence compact since <span class="pre">`X`</span> is compact.

Then we discuss two possibilities using <span class="pre">`eq_empty_or_nonempty`</span>. If <span class="pre">`K`</span> is empty then we are clearly done (we can set <span class="pre">`δ`</span>` `<span class="pre">`=`</span>` `<span class="pre">`1`</span> for instance). So let’s assume <span class="pre">`K`</span> is not empty, and use the extreme value theorem to choose <span class="pre">`(x₀,`</span>` `<span class="pre">`x₁)`</span> attaining the infimum of the distance function on <span class="pre">`K`</span>. We can then set <span class="pre">`δ`</span>` `<span class="pre">`=`</span>` `<span class="pre">`dist`</span>` `<span class="pre">`x₀`</span>` `<span class="pre">`x₁`</span> and check everything works.

    example {X : Type*} [MetricSpace X] [CompactSpace X]
          {Y : Type*} [MetricSpace Y] {f : X → Y}
        (hf : Continuous f) : UniformContinuous f := by
      sorry

### <span class="section-number">11.2.5. </span>Completeness<a href="#completeness" class="headerlink" title="Link to this heading"></a>

A Cauchy sequence in a metric space is a sequence whose terms get closer and closer to each other. There are a couple of equivalent ways to state that idea. In particular converging sequences are Cauchy. The converse is true only in so-called *complete* spaces.

    example (u : ℕ → X) :
        CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N, dist (u m) (u n) < ε :=
      Metric.cauchySeq_iff

    example (u : ℕ → X) :
        CauchySeq u ↔ ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, dist (u n) (u N) < ε :=
      Metric.cauchySeq_iff'

    example [CompleteSpace X] (u : ℕ → X) (hu : CauchySeq u) :
        ∃ x, Tendsto u atTop (𝓝 x) :=
      cauchySeq_tendsto_of_complete hu

We’ll practice using this definition by proving a convenient criterion which is a special case of a criterion appearing in Mathlib. This is also a good opportunity to practice using big sums in a geometric context. In addition to the explanations from the filters section, you will probably need <span class="pre">`tendsto_pow_atTop_nhds_zero_of_lt_one`</span>, <span class="pre">`Tendsto.mul`</span> and <span class="pre">`dist_le_range_sum_dist`</span>.

    theorem cauchySeq_of_le_geometric_two' {u : ℕ → X}
        (hu : ∀ n : ℕ, dist (u n) (u (n + 1)) ≤ (1 / 2) ^ n) : CauchySeq u := by
      rw [Metric.cauchySeq_iff']
      intro ε ε_pos
      obtain ⟨N, hN⟩ : ∃ N : ℕ, 1 / 2 ^ N * 2 < ε := by sorry
      use N
      intro n hn
      obtain ⟨k, rfl : n = N + k⟩ := le_iff_exists_add.mp hn
      calc
        dist (u (N + k)) (u N) = dist (u (N + 0)) (u (N + k)) := sorry
        _ ≤ ∑ i  ∈ range k, dist (u (N + i)) (u (N + (i + 1))) := sorry
        _ ≤ ∑ i  ∈ range k, (1 / 2 : ℝ) ^ (N + i) := sorry
        _ = 1 / 2 ^ N * ∑ i  ∈ range k, (1 / 2 : ℝ) ^ i := sorry
        _ ≤ 1 / 2 ^ N * 2 := sorry
        _ < ε := sorry

We are ready for the final boss of this section: Baire’s theorem for complete metric spaces! The proof skeleton below shows interesting techniques. It uses the <span class="pre">`choose`</span> tactic in its exclamation mark variant (you should experiment with removing this exclamation mark) and it shows how to define something inductively in the middle of a proof using <span class="pre">`Nat.rec_on`</span>.

    open Metric

    example [CompleteSpace X] (f : ℕ → Set X) (ho : ∀ n, IsOpen (f n)) (hd : ∀ n, Dense (f n)) :
        Dense (⋂ n, f n) := by
      let B : ℕ → ℝ := fun n ↦ (1 / 2) ^ n
      have Bpos : ∀ n, 0 < B n
      sorry
      /- Translate the density assumption into two functions `center` and `radius` associating
        to any n, x, δ, δpos a center and a positive radius such that
        `closedBall center radius` is included both in `f n` and in `closedBall x δ`.
        We can also require `radius ≤ (1/2)^(n+1)`, to ensure we get a Cauchy sequence later. -/
      have :
        ∀ (n : ℕ) (x : X),
          ∀ δ > 0, ∃ y : X, ∃ r > 0, r ≤ B (n + 1) ∧ closedBall y r ⊆ closedBall x δ ∩ f n :=
        by sorry
      choose! center radius Hpos HB Hball using this
      intro x
      rw [mem_closure_iff_nhds_basis nhds_basis_closedBall]
      intro ε εpos
      /- `ε` is positive. We have to find a point in the ball of radius `ε` around `x`
        belonging to all `f n`. For this, we construct inductively a sequence
        `F n = (c n, r n)` such that the closed ball `closedBall (c n) (r n)` is included
        in the previous ball and in `f n`, and such that `r n` is small enough to ensure
        that `c n` is a Cauchy sequence. Then `c n` converges to a limit which belongs
        to all the `f n`. -/
      let F : ℕ → X × ℝ := fun n ↦
        Nat.recOn n (Prod.mk x (min ε (B 0)))
          fun n p ↦ Prod.mk (center n p.1 p.2) (radius n p.1 p.2)
      let c : ℕ → X := fun n ↦ (F n).1
      let r : ℕ → ℝ := fun n ↦ (F n).2
      have rpos : ∀ n, 0 < r n := by sorry
      have rB : ∀ n, r n ≤ B n := by sorry
      have incl : ∀ n, closedBall (c (n + 1)) (r (n + 1)) ⊆ closedBall (c n) (r n) ∩ f n := by
        sorry
      have cdist : ∀ n, dist (c n) (c (n + 1)) ≤ B n := by sorry
      have : CauchySeq c := cauchySeq_of_le_geometric_two' cdist
      -- as the sequence `c n` is Cauchy in a complete space, it converges to a limit `y`.
      rcases cauchySeq_tendsto_of_complete this with ⟨y, ylim⟩
      -- this point `y` will be the desired point. We will check that it belongs to all
      -- `f n` and to `ball x ε`.
      use y
      have I : ∀ n, ∀ m ≥ n, closedBall (c m) (r m) ⊆ closedBall (c n) (r n) := by sorry
      have yball : ∀ n, y ∈ closedBall (c n) (r n) := by sorry
      sorry

<span id="index-4"></span><span id="id4"></span>

## <span class="section-number">11.3. </span>Topological spaces<a href="#topological-spaces" class="headerlink" title="Link to this heading"></a>

### <span class="section-number">11.3.1. </span>Fundamentals<a href="#fundamentals" class="headerlink" title="Link to this heading"></a>

We now go up in generality and introduce topological spaces. We will review the two main ways to define topological spaces and then explain how the category of topological spaces is much better behaved than the category of metric spaces. Note that we won’t be using Mathlib category theory here, only having a somewhat categorical point of view.

The first way to think about the transition from metric spaces to topological spaces is that we only remember the notion of open sets (or equivalently the notion of closed sets). From this point of view, a topological space is a type equipped with a collection of sets that are called open sets. This collection has to satisfy a number of axioms presented below (this collection is slightly redundant but we will ignore that).

    section
    variable {X : Type*} [TopologicalSpace X]

    example : IsOpen (univ : Set X) :=
      isOpen_univ

    example : IsOpen (∅ : Set X) :=
      isOpen_empty

    example {ι : Type*} {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) : IsOpen (⋃ i, s i) :=
      isOpen_iUnion hs

    example {ι : Type*} [Fintype ι] {s : ι → Set X} (hs : ∀ i, IsOpen (s i)) :
        IsOpen (⋂ i, s i) :=
      isOpen_iInter_of_finite hs

Closed sets are then defined as sets whose complement is open. A function between topological spaces is (globally) continuous if all preimages of open sets are open.

    variable {Y : Type*} [TopologicalSpace Y]

    example {f : X → Y} : Continuous f ↔ ∀ s, IsOpen s → IsOpen (f ⁻¹' s) :=
      continuous_def

With this definition we already see that, compared to metric spaces, topological spaces only remember enough information to talk about continuous functions: two topological structures on a type are the same if and only if they have the same continuous functions (indeed the identity function will be continuous in both direction if and only if the two structures have the same open sets).

However as soon as we move on to continuity at a point we see the limitations of the approach based on open sets. In Mathlib we frequently think of topological spaces as types equipped with a neighborhood filter <span class="pre">`𝓝`</span>` `<span class="pre">`x`</span> attached to each point <span class="pre">`x`</span> (the corresponding function <span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span> satisfies certain conditions explained further down). Remember from the filters section that these gadgets play two related roles. First <span class="pre">`𝓝`</span>` `<span class="pre">`x`</span> is seen as the generalized set of points of <span class="pre">`X`</span> that are close to <span class="pre">`x`</span>. And then it is seen as giving a way to say, for any predicate <span class="pre">`P`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Prop`</span>, that this predicate holds for points that are close enough to <span class="pre">`x`</span>. Let us state that <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Y`</span> is continuous at <span class="pre">`x`</span>. The purely filtery way is to say that the direct image under <span class="pre">`f`</span> of the generalized set of points that are close to <span class="pre">`x`</span> is contained in the generalized set of points that are close to <span class="pre">`f`</span>` `<span class="pre">`x`</span>. Recall this is spelled either <span class="pre">`map`</span>` `<span class="pre">`f`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`𝓝`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`x)`</span> or <span class="pre">`Tendsto`</span>` `<span class="pre">`f`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`x))`</span>.

    example {f : X → Y} {x : X} : ContinuousAt f x ↔ map f (𝓝 x) ≤ 𝓝 (f x) :=
      Iff.rfl

One can also spell it using both neighborhoods seen as ordinary sets and a neighborhood filter seen as a generalized set: “for any neighborhood <span class="pre">`U`</span> of <span class="pre">`f`</span>` `<span class="pre">`x`</span>, all points close to <span class="pre">`x`</span> are sent to <span class="pre">`U`</span>”. Note that the proof is again <span class="pre">`Iff.rfl`</span>, this point of view is definitionally equivalent to the previous one.

    example {f : X → Y} {x : X} : ContinuousAt f x ↔ ∀ U ∈ 𝓝 (f x), ∀ᶠ x in 𝓝 x, f x ∈ U :=
      Iff.rfl

We now explain how to go from one point of view to the other. In terms of open sets, we can simply define members of <span class="pre">`𝓝`</span>` `<span class="pre">`x`</span> as sets that contain an open set containing <span class="pre">`x`</span>.

    example {x : X} {s : Set X} : s ∈ 𝓝 x ↔ ∃ t, t ⊆ s ∧ IsOpen t ∧ x ∈ t :=
      mem_nhds_iff

To go in the other direction we need to discuss the condition that <span class="pre">`𝓝`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span> must satisfy in order to be the neighborhood function of a topology.

The first constraint is that <span class="pre">`𝓝`</span>` `<span class="pre">`x`</span>, seen as a generalized set, contains the set <span class="pre">`{x}`</span> seen as the generalized set <span class="pre">`pure`</span>` `<span class="pre">`x`</span> (explaining this weird name would be too much of a digression, so we simply accept it for now). Another way to say it is that if a predicate holds for points close to <span class="pre">`x`</span> then it holds at <span class="pre">`x`</span>.

    example (x : X) : pure x ≤ 𝓝 x :=
      pure_le_nhds x

    example (x : X) (P : X → Prop) (h : ∀ᶠ y in 𝓝 x, P y) : P x :=
      h.self_of_nhds

Then a more subtle requirement is that, for any predicate <span class="pre">`P`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Prop`</span> and any <span class="pre">`x`</span>, if <span class="pre">`P`</span>` `<span class="pre">`y`</span> holds for <span class="pre">`y`</span> close to <span class="pre">`x`</span> then for <span class="pre">`y`</span> close to <span class="pre">`x`</span> and <span class="pre">`z`</span> close to <span class="pre">`y`</span>, <span class="pre">`P`</span>` `<span class="pre">`z`</span> holds. More precisely we have:

    example {P : X → Prop} {x : X} (h : ∀ᶠ y in 𝓝 x, P y) : ∀ᶠ y in 𝓝 x, ∀ᶠ z in 𝓝 y, P z :=
      eventually_eventually_nhds.mpr h

Those two results characterize the functions <span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span> that are neighborhood functions for a topological space structure on <span class="pre">`X`</span>. There is a still a function <span class="pre">`TopologicalSpace.mkOfNhds`</span>` `<span class="pre">`:`</span>` `<span class="pre">`(X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`TopologicalSpace`</span>` `<span class="pre">`X`</span> but it will give back its input as a neighborhood function only if it satisfies the above two constraints. More precisely we have a lemma <span class="pre">`TopologicalSpace.nhds_mkOfNhds`</span> saying that in a different way and our next exercise deduces this different way from how we stated it above.

    example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
        (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
        ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' := by
      sorry
    end

Note that <span class="pre">`TopologicalSpace.mkOfNhds`</span> is not so frequently used, but it still good to know in what precise sense the neighborhood filters is all there is in a topological space structure.

The next thing to know in order to efficiently use topological spaces in Mathlib is that we use a lot of formal properties of <span class="pre">`TopologicalSpace`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type`</span>` `<span class="pre">`u`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Type`</span>` `<span class="pre">`u`</span>. From a purely mathematical point of view, those formal properties are a very clean way to explain how topological spaces solve issues that metric spaces have. From this point of view, the issues solved by topological spaces is that metric spaces enjoy very little functoriality, and have very bad categorical properties in general. This comes on top of the fact already discussed that metric spaces contain a lot of geometrical information that is not topologically relevant.

Let us focus on functoriality first. A metric space structure can be induced on a subset or, equivalently, it can be pulled back by an injective map. But that’s pretty much everything. They cannot be pulled back by general map or pushed forward, even by surjective maps.

In particular there is no sensible distance to put on a quotient of a metric space or on an uncountable product of metric spaces. Consider for instance the type <span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span>, seen as a product of copies of <span class="pre">`ℝ`</span> indexed by <span class="pre">`ℝ`</span>. We would like to say that pointwise convergence of sequences of functions is a respectable notion of convergence. But there is no distance on <span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> that gives this notion of convergence. Relatedly, there is no distance ensuring that a map <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`(ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ)`</span> is continuous if and only if <span class="pre">`fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`t`</span> is continuous for every <span class="pre">`t`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>.

We now review the data used to solve all those issues. First we can use any map <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Y`</span> to push or pull topologies from one side to the other. Those two operations form a Galois connection.

    variable {X Y : Type*}

    example (f : X → Y) : TopologicalSpace X → TopologicalSpace Y :=
      TopologicalSpace.coinduced f

    example (f : X → Y) : TopologicalSpace Y → TopologicalSpace X :=
      TopologicalSpace.induced f

    example (f : X → Y) (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) :
        TopologicalSpace.coinduced f T_X ≤ T_Y ↔ T_X ≤ TopologicalSpace.induced f T_Y :=
      coinduced_le_iff_le_induced

Those operations are compatible with composition of functions. As usual, pushing forward is covariant and pulling back is contravariant, see <span class="pre">`coinduced_compose`</span> and <span class="pre">`induced_compose`</span>. On paper we will use notations <span class="math notranslate nohighlight">\\f\_\*T\\</span> for <span class="pre">`TopologicalSpace.coinduced`</span>` `<span class="pre">`f`</span>` `<span class="pre">`T`</span> and <span class="math notranslate nohighlight">\\f^\*T\\</span> for <span class="pre">`TopologicalSpace.induced`</span>` `<span class="pre">`f`</span>` `<span class="pre">`T`</span>.

Then the next big piece is a complete lattice structure on <span class="pre">`TopologicalSpace`</span>` `<span class="pre">`X`</span> for any given structure. If you think of topologies as being primarily the data of open sets then you expect the order relation on <span class="pre">`TopologicalSpace`</span>` `<span class="pre">`X`</span> to come from <span class="pre">`Set`</span>` `<span class="pre">`(Set`</span>` `<span class="pre">`X)`</span>, i.e. you expect <span class="pre">`t`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`t'`</span> if a set <span class="pre">`u`</span> is open for <span class="pre">`t'`</span> as soon as it is open for <span class="pre">`t`</span>. However we already know that Mathlib focuses on neighborhoods more than open sets so, for any <span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span> we want the map from topological spaces to neighborhoods <span class="pre">`fun`</span>` `<span class="pre">`T`</span>` `<span class="pre">`:`</span>` `<span class="pre">`TopologicalSpace`</span>` `<span class="pre">`X`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`@nhds`</span>` `<span class="pre">`X`</span>` `<span class="pre">`T`</span>` `<span class="pre">`x`</span> to be order preserving. And we know the order relation on <span class="pre">`Filter`</span>` `<span class="pre">`X`</span> is designed to ensure an order preserving <span class="pre">`principal`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Filter`</span>` `<span class="pre">`X`</span>, allowing to see filters as generalized sets. So the order relation we do use on <span class="pre">`TopologicalSpace`</span>` `<span class="pre">`X`</span> is opposite to the one coming from <span class="pre">`Set`</span>` `<span class="pre">`(Set`</span>` `<span class="pre">`X)`</span>.

    example {T T' : TopologicalSpace X} : T ≤ T' ↔ ∀ s, T'.IsOpen s → T.IsOpen s :=
      Iff.rfl

Now we can recover continuity by combining the push-forward (or pull-back) operation with the order relation.

    example (T_X : TopologicalSpace X) (T_Y : TopologicalSpace Y) (f : X → Y) :
        Continuous f ↔ TopologicalSpace.coinduced f T_X ≤ T_Y :=
      continuous_iff_coinduced_le

With this definition and the compatibility of push-forward and composition, we get for free the universal property that, for any topological space <span class="math notranslate nohighlight">\\Z\\</span>, a function <span class="math notranslate nohighlight">\\g : Y → Z\\</span> is continuous for the topology <span class="math notranslate nohighlight">\\f\_\*T\_X\\</span> if and only if <span class="math notranslate nohighlight">\\g ∘ f\\</span> is continuous.

\\\begin{split}g \text{ continuous } &⇔ g\_\*(f\_\*T\_X) ≤ T\_Z \\ &⇔ (g ∘ f)\_\* T\_X ≤ T\_Z \\ &⇔ g ∘ f \text{ continuous}\end{split}\\

    example {Z : Type*} (f : X → Y) (T_X : TopologicalSpace X) (T_Z : TopologicalSpace Z)
          (g : Y → Z) :
        @Continuous Y Z (TopologicalSpace.coinduced f T_X) T_Z g ↔
          @Continuous X Z T_X T_Z (g ∘ f) := by
      rw [continuous_iff_coinduced_le, coinduced_compose, continuous_iff_coinduced_le]

So we already get quotient topologies (using the projection map as <span class="pre">`f`</span>). This wasn’t using that <span class="pre">`TopologicalSpace`</span>` `<span class="pre">`X`</span> is a complete lattice for all <span class="pre">`X`</span>. Let’s now see how all this structure proves the existence of the product topology by abstract non-sense. We considered the case of <span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> above, but let’s now consider the general case of <span class="pre">`Π`</span>` `<span class="pre">`i,`</span>` `<span class="pre">`X`</span>` `<span class="pre">`i`</span> for some <span class="pre">`ι`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type*`</span> and <span class="pre">`X`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ι`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Type*`</span>. We want, for any topological space <span class="pre">`Z`</span> and any function <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Z`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Π`</span>` `<span class="pre">`i,`</span>` `<span class="pre">`X`</span>` `<span class="pre">`i`</span>, that <span class="pre">`f`</span> is continuous if and only if <span class="pre">`(fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`x`</span>` `<span class="pre">`i)`</span>` `<span class="pre">`∘`</span>` `<span class="pre">`f`</span> is continuous for all <span class="pre">`i`</span>. Let us explore that constraint “on paper” using notation <span class="math notranslate nohighlight">\\p\_i\\</span> for the projection <span class="pre">`(fun`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Π`</span>` `<span class="pre">`i,`</span>` `<span class="pre">`X`</span>` `<span class="pre">`i)`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`x`</span>` `<span class="pre">`i)`</span>:

\\\begin{split}(∀ i, p\_i ∘ f \text{ continuous}) &⇔ ∀ i, (p\_i ∘ f)\_\* T\_Z ≤ T\_{X\_i} \\ &⇔ ∀ i, (p\_i)\_\* f\_\* T\_Z ≤ T\_{X\_i}\\ &⇔ ∀ i, f\_\* T\_Z ≤ (p\_i)^\*T\_{X\_i}\\ &⇔ f\_\* T\_Z ≤ \inf \left\[(p\_i)^\*T\_{X\_i}\right\]\end{split}\\

So we see that what is the topology we want on <span class="pre">`Π`</span>` `<span class="pre">`i,`</span>` `<span class="pre">`X`</span>` `<span class="pre">`i`</span>:

    example (ι : Type*) (X : ι → Type*) (T_X : ∀ i, TopologicalSpace (X i)) :
        (Pi.topologicalSpace : TopologicalSpace (∀ i, X i)) =
          ⨅ i, TopologicalSpace.induced (fun x ↦ x i) (T_X i) :=
      rfl

This ends our tour of how Mathlib thinks that topological spaces fix defects of the theory of metric spaces by being a more functorial theory and having a complete lattice structure for any fixed type.

### <span class="section-number">11.3.2. </span>Separation and countability<a href="#separation-and-countability" class="headerlink" title="Link to this heading"></a>

We saw that the category of topological spaces have very nice properties. The price to pay for this is existence of rather pathological topological spaces. There are a number of assumptions you can make on a topological space to ensure its behavior is closer to what metric spaces do. The most important is <span class="pre">`T2Space`</span>, also called “Hausdorff”, that will ensure that limits are unique. A stronger separation property is <span class="pre">`T3Space`</span> that ensures in addition the RegularSpace property: each point has a basis of closed neighborhoods.

    example [TopologicalSpace X] [T2Space X] {u : ℕ → X} {a b : X} (ha : Tendsto u atTop (𝓝 a))
        (hb : Tendsto u atTop (𝓝 b)) : a = b :=
      tendsto_nhds_unique ha hb

    example [TopologicalSpace X] [RegularSpace X] (a : X) :
        (𝓝 a).HasBasis (fun s : Set X ↦ s ∈ 𝓝 a ∧ IsClosed s) id :=
      closed_nhds_basis a

Note that, in every topological space, each point has a basis of open neighborhood, by definition.

    example [TopologicalSpace X] {x : X} :
        (𝓝 x).HasBasis (fun t : Set X ↦ t ∈ 𝓝 x ∧ IsOpen t) id :=
      nhds_basis_opens' x

Our main goal is now to prove the basic theorem which allows extension by continuity. From Bourbaki’s general topology book, I.8.5, Theorem 1 (taking only the non-trivial implication):

Let <span class="math notranslate nohighlight">\\X\\</span> be a topological space, <span class="math notranslate nohighlight">\\A\\</span> a dense subset of <span class="math notranslate nohighlight">\\X\\</span>, <span class="math notranslate nohighlight">\\f : A → Y\\</span> a continuous mapping of <span class="math notranslate nohighlight">\\A\\</span> into a <span class="math notranslate nohighlight">\\T\_3\\</span> space <span class="math notranslate nohighlight">\\Y\\</span>. If, for each <span class="math notranslate nohighlight">\\x\\</span> in <span class="math notranslate nohighlight">\\X\\</span>, <span class="math notranslate nohighlight">\\f(y)\\</span> tends to a limit in <span class="math notranslate nohighlight">\\Y\\</span> when <span class="math notranslate nohighlight">\\y\\</span> tends to <span class="math notranslate nohighlight">\\x\\</span> while remaining in <span class="math notranslate nohighlight">\\A\\</span> then there exists a continuous extension <span class="math notranslate nohighlight">\\φ\\</span> of <span class="math notranslate nohighlight">\\f\\</span> to <span class="math notranslate nohighlight">\\X\\</span>.

Actually Mathlib contains a more general version of the above lemma, <span class="pre">`IsDenseInducing.continuousAt_extend`</span>, but we’ll stick to Bourbaki’s version here.

Remember that, given <span class="pre">`A`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`X`</span>, <span class="pre">`↥A`</span> is the subtype associated to <span class="pre">`A`</span>, and Lean will automatically insert that funny up arrow when needed. And the (inclusion) coercion map is <span class="pre">`(↑)`</span>` `<span class="pre">`:`</span>` `<span class="pre">`A`</span>` `<span class="pre">`→`</span>` `<span class="pre">`X`</span>. The assumption “tends to <span class="math notranslate nohighlight">\\x\\</span> while remaining in <span class="math notranslate nohighlight">\\A\\</span>” corresponds to the pull-back filter <span class="pre">`comap`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x)`</span>.

Let’s first prove an auxiliary lemma, extracted to simplify the context (in particular we don’t need Y to be a topological space here).

    theorem aux {X Y A : Type*} [TopologicalSpace X] {c : A → X}
          {f : A → Y} {x : X} {F : Filter Y}
          (h : Tendsto f (comap c (𝓝 x)) F) {V' : Set Y} (V'_in : V' ∈ F) :
        ∃ V ∈ 𝓝 x, IsOpen V ∧ c ⁻¹' V ⊆ f ⁻¹' V' := by
      sorry

Let’s now turn to the main proof of the extension by continuity theorem.

When Lean needs a topology on <span class="pre">`↥A`</span> it will automatically use the induced topology. The only relevant lemma is <span class="pre">`nhds_induced`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`:`</span>` `<span class="pre">`∀`</span>` `<span class="pre">`a`</span>` `<span class="pre">`:`</span>` `<span class="pre">`↥A,`</span>` `<span class="pre">`𝓝`</span>` `<span class="pre">`a`</span>` `<span class="pre">`=`</span>` `<span class="pre">`comap`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`↑a)`</span> (this is actually a general lemma about induced topologies).

The proof outline is:

The main assumption and the axiom of choice give a function <span class="pre">`φ`</span> such that <span class="pre">`∀`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`Tendsto`</span>` `<span class="pre">`f`</span>` `<span class="pre">`(comap`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`x))`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`(φ`</span>` `<span class="pre">`x))`</span> (because <span class="pre">`Y`</span> is Hausdorff, <span class="pre">`φ`</span> is entirely determined, but we won’t need that until we try to prove that <span class="pre">`φ`</span> indeed extends <span class="pre">`f`</span>).

Let’s first prove <span class="pre">`φ`</span> is continuous. Fix any <span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span>. Since <span class="pre">`Y`</span> is regular, it suffices to check that for every *closed* neighborhood <span class="pre">`V'`</span> of <span class="pre">`φ`</span>` `<span class="pre">`x`</span>, <span class="pre">`φ`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`V'`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`𝓝`</span>` `<span class="pre">`x`</span>. The limit assumption gives (through the auxiliary lemma above) some <span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`𝓝`</span>` `<span class="pre">`x`</span> such <span class="pre">`IsOpen`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`V`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`f`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`V'`</span>. Since <span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`𝓝`</span>` `<span class="pre">`x`</span>, it suffices to prove <span class="pre">`V`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`φ`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`V'`</span>, i.e. <span class="pre">`∀`</span>` `<span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`V,`</span>` `<span class="pre">`φ`</span>` `<span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`V'`</span>. Let’s fix <span class="pre">`y`</span> in <span class="pre">`V`</span>. Because <span class="pre">`V`</span> is *open*, it is a neighborhood of <span class="pre">`y`</span>. In particular <span class="pre">`(↑)`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`V`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`comap`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`y)`</span> and a fortiori <span class="pre">`f`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`V'`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`comap`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`y)`</span>. In addition <span class="pre">`comap`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`⊥`</span> because <span class="pre">`A`</span> is dense. Because we know <span class="pre">`Tendsto`</span>` `<span class="pre">`f`</span>` `<span class="pre">`(comap`</span>` `<span class="pre">`(↑)`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`y))`</span>` `<span class="pre">`(𝓝`</span>` `<span class="pre">`(φ`</span>` `<span class="pre">`y))`</span> this implies <span class="pre">`φ`</span>` `<span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`closure`</span>` `<span class="pre">`V'`</span> and, since <span class="pre">`V'`</span> is closed, we have proved <span class="pre">`φ`</span>` `<span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`V'`</span>.

It remains to prove that <span class="pre">`φ`</span> extends <span class="pre">`f`</span>. This is where the continuity of <span class="pre">`f`</span> enters the discussion, together with the fact that <span class="pre">`Y`</span> is Hausdorff.

    example [TopologicalSpace X] [TopologicalSpace Y] [T3Space Y] {A : Set X}
        (hA : ∀ x, x ∈ closure A) {f : A → Y} (f_cont : Continuous f)
        (hf : ∀ x : X, ∃ c : Y, Tendsto f (comap (↑) (𝓝 x)) (𝓝 c)) :
        ∃ φ : X → Y, Continuous φ ∧ ∀ a : A, φ a = f a := by
      sorry

    #check HasBasis.tendsto_right_iff

In addition to separation property, the main kind of assumption you can make on a topological space to bring it closer to metric spaces is countability assumption. The main one is first countability asking that every point has a countable neighborhood basis. In particular this ensures that closure of sets can be understood using sequences.

    example [TopologicalSpace X] [FirstCountableTopology X]
          {s : Set X} {a : X} :
        a ∈ closure s ↔ ∃ u : ℕ → X, (∀ n, u n ∈ s) ∧ Tendsto u atTop (𝓝 a) :=
      mem_closure_iff_seq_limit

### <span class="section-number">11.3.3. </span>Compactness<a href="#id5" class="headerlink" title="Link to this heading"></a>

Let us now discuss how compactness is defined for topological spaces. As usual there are several ways to think about it and Mathlib goes for the filter version.

We first need to define cluster points of filters. Given a filter <span class="pre">`F`</span> on a topological space <span class="pre">`X`</span>, a point <span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`X`</span> is a cluster point of <span class="pre">`F`</span> if <span class="pre">`F`</span>, seen as a generalized set, has non-empty intersection with the generalized set of points that are close to <span class="pre">`x`</span>.

Then we can say that a set <span class="pre">`s`</span> is compact if every nonempty generalized set <span class="pre">`F`</span> contained in <span class="pre">`s`</span>, i.e. such that <span class="pre">`F`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`𝓟`</span>` `<span class="pre">`s`</span>, has a cluster point in <span class="pre">`s`</span>.

    variable [TopologicalSpace X]

    example {F : Filter X} {x : X} : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) :=
      Iff.rfl

    example {s : Set X} :
        IsCompact s ↔ ∀ (F : Filter X) [NeBot F], F ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a F :=
      Iff.rfl

For instance if <span class="pre">`F`</span> is <span class="pre">`map`</span>` `<span class="pre">`u`</span>` `<span class="pre">`atTop`</span>, the image under <span class="pre">`u`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℕ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`X`</span> of <span class="pre">`atTop`</span>, the generalized set of very large natural numbers, then the assumption <span class="pre">`F`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`𝓟`</span>` `<span class="pre">`s`</span> means that <span class="pre">`u`</span>` `<span class="pre">`n`</span> belongs to <span class="pre">`s`</span> for <span class="pre">`n`</span> large enough. Saying that <span class="pre">`x`</span> is a cluster point of <span class="pre">`map`</span>` `<span class="pre">`u`</span>` `<span class="pre">`atTop`</span> says the image of very large numbers intersects the set of points that are close to <span class="pre">`x`</span>. In case <span class="pre">`𝓝`</span>` `<span class="pre">`x`</span> has a countable basis, we can interpret this as saying that <span class="pre">`u`</span> has a subsequence converging to <span class="pre">`x`</span>, and we get back what compactness looks like in metric spaces.

    example [FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
        (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
      hs.tendsto_subseq hu

Cluster points behave nicely with continuous functions.

    variable [TopologicalSpace Y]

    example {x : X} {F : Filter X} {G : Filter Y} (H : ClusterPt x F) {f : X → Y}
        (hfx : ContinuousAt f x) (hf : Tendsto f F G) : ClusterPt (f x) G :=
      ClusterPt.map H hfx hf

As an exercise, we will prove that the image of a compact set under a continuous map is compact. In addition to what we saw already, you should use <span class="pre">`Filter.push_pull`</span> and <span class="pre">`NeBot.of_map`</span>.

    example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
        IsCompact (f '' s) := by
      intro F F_ne F_le
      have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by sorry
      have Hne : (𝓟 s ⊓ comap f F).NeBot := by sorry
      have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
      sorry

One can also express compactness in terms of open covers: <span class="pre">`s`</span> is compact if every family of open sets that cover <span class="pre">`s`</span> has a finite covering sub-family.

    example {ι : Type*} {s : Set X} (hs : IsCompact s) (U : ι → Set X) (hUo : ∀ i, IsOpen (U i))
        (hsU : s ⊆ ⋃ i, U i) : ∃ t : Finset ι, s ⊆ ⋃ i ∈ t, U i :=
      hs.elim_finite_subcover U hUo hsU
