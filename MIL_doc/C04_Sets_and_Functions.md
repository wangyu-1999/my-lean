<span id="id1"></span>

# <span class="section-number">4. </span>Sets and Functions<a href="#sets-and-functions" class="headerlink" title="Link to this heading"></a>

The vocabulary of sets, relations, and functions provides a uniform language for carrying out constructions in all the branches of mathematics. Since functions and relations can be defined in terms of sets, axiomatic set theory can be used as a foundation for mathematics.

Lean’s foundation is based instead on the primitive notion of a *type*, and it includes ways of defining functions between types. Every expression in Lean has a type: there are natural numbers, real numbers, functions from reals to reals, groups, vector spaces, and so on. Some expressions *are* types, which is to say, their type is <span class="pre">`Type`</span>. Lean and Mathlib provide ways of defining new types, and ways of defining objects of those types.

Conceptually, you can think of a type as just a set of objects. Requiring every object to have a type has some advantages. For example, it makes it possible to overload notation like <span class="pre">`+`</span>, and it sometimes makes input less verbose because Lean can infer a lot of information from an object’s type. The type system also enables Lean to flag errors when you apply a function to the wrong number of arguments, or apply a function to arguments of the wrong type.

Lean’s library does define elementary set-theoretic notions. In contrast to set theory, in Lean a set is always a set of objects of some type, such as a set of natural numbers or a set of functions from real numbers to real numbers. The distinction between types and sets takes some getting used to, but this chapter will take you through the essentials.

<span id="id2"></span>

## <span class="section-number">4.1. </span>Sets<a href="#sets" class="headerlink" title="Link to this heading"></a>

If <span class="pre">`α`</span> is any type, the type <span class="pre">`Set`</span>` `<span class="pre">`α`</span> consists of sets of elements of <span class="pre">`α`</span>. This type supports the usual set-theoretic operations and relations. For example, <span class="pre">`s`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`t`</span> says that <span class="pre">`s`</span> is a subset of <span class="pre">`t`</span>, <span class="pre">`s`</span>` `<span class="pre">`∩`</span>` `<span class="pre">`t`</span> denotes the intersection of <span class="pre">`s`</span> and <span class="pre">`t`</span>, and <span class="pre">`s`</span>` `<span class="pre">`∪`</span>` `<span class="pre">`t`</span> denotes their union. The subset relation can be typed with <span class="pre">`\ss`</span> or <span class="pre">`\sub`</span>, intersection can be typed with <span class="pre">`\i`</span> or <span class="pre">`\cap`</span>, and union can be typed with <span class="pre">`\un`</span> or <span class="pre">`\cup`</span>. The library also defines the set <span class="pre">`univ`</span>, which consists of all the elements of type <span class="pre">`α`</span>, and the empty set, <span class="pre">`∅`</span>, which can be typed as <span class="pre">`\empty`</span>. Given <span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span> and <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`α`</span>, the expression <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span> says that <span class="pre">`x`</span> is a member of <span class="pre">`s`</span>. Theorems that mention set membership often include <span class="pre">`mem`</span> in their name. The expression <span class="pre">`x`</span>` `<span class="pre">`∉`</span>` `<span class="pre">`s`</span> abbreviates <span class="pre">`¬`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>. You can type <span class="pre">`∈`</span> as <span class="pre">`\in`</span> or <span class="pre">`\mem`</span> and <span class="pre">`∉`</span> as <span class="pre">`\notin`</span>.

One way to prove things about sets is to use <span class="pre">`rw`</span> or the simplifier to expand the definitions. In the second example below, we use <span class="pre">`simp`</span>` `<span class="pre">`only`</span> to tell the simplifier to use only the list of identities we give it, and not its full database of identities. Unlike <span class="pre">`rw`</span>, <span class="pre">`simp`</span> can perform simplifications inside a universal or existential quantifier. If you step through the proof, you can see the effects of these commands.

    variable {α : Type*}
    variable (s t u : Set α)
    open Set

    example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
      rw [subset_def, inter_def, inter_def]
      rw [subset_def] at h
      simp only [mem_setOf]
      rintro x ⟨xs, xu⟩
      exact ⟨h _ xs, xu⟩

    example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
      simp only [subset_def, mem_inter_iff] at *
      rintro x ⟨xs, xu⟩
      exact ⟨h _ xs, xu⟩

In this example, we open the <span class="pre">`set`</span> namespace to have access to the shorter names for the theorems. But, in fact, we can delete the calls to <span class="pre">`rw`</span> and <span class="pre">`simp`</span> entirely:

    example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
      intro x xsu
      exact ⟨h xsu.1, xsu.2⟩

What is going on here is known as *definitional reduction*: to make sense of the <span class="pre">`intro`</span> command and the anonymous constructors Lean is forced to expand the definitions. The following example also illustrate the phenomenon:

    example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
      fun x ⟨xs, xu⟩ ↦ ⟨h xs, xu⟩

To deal with unions, we can use <span class="pre">`Set.union_def`</span> and <span class="pre">`Set.mem_union`</span>. Since <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`∪`</span>` `<span class="pre">`t`</span> unfolds to <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`∨`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`t`</span>, we can also use the <span class="pre">`cases`</span> tactic to force a definitional reduction.

    example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
      intro x hx
      have xs : x ∈ s := hx.1
      have xtu : x ∈ t ∪ u := hx.2
      rcases xtu with xt | xu
      · left
        show x ∈ s ∩ t
        exact ⟨xs, xt⟩
      · right
        show x ∈ s ∩ u
        exact ⟨xs, xu⟩

Since intersection binds tighter than union, the use of parentheses in the expression <span class="pre">`(s`</span>` `<span class="pre">`∩`</span>` `<span class="pre">`t)`</span>` `<span class="pre">`∪`</span>` `<span class="pre">`(s`</span>` `<span class="pre">`∩`</span>` `<span class="pre">`u)`</span> is unnecessary, but they make the meaning of the expression clearer. The following is a shorter proof of the same fact:

    example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by
      rintro x ⟨xs, xt | xu⟩
      · left; exact ⟨xs, xt⟩
      · right; exact ⟨xs, xu⟩

As an exercise, try proving the other inclusion:

    example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by
      sorry

It might help to know that when using <span class="pre">`rintro`</span>, sometimes we need to use parentheses around a disjunctive pattern <span class="pre">`h1`</span>` `<span class="pre">`|`</span>` `<span class="pre">`h2`</span> to get Lean to parse it correctly.

The library also defines set difference, <span class="pre">`s`</span>` `<span class="pre">`\`</span>` `<span class="pre">`t`</span>, where the backslash is a special unicode character entered as <span class="pre">`\\`</span>. The expression <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`\`</span>` `<span class="pre">`t`</span> expands to <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∉`</span>` `<span class="pre">`t`</span>. (The <span class="pre">`∉`</span> can be entered as <span class="pre">`\notin`</span>.) It can be rewritten manually using <span class="pre">`Set.diff_eq`</span> and <span class="pre">`dsimp`</span> or <span class="pre">`Set.mem_diff`</span>, but the following two proofs of the same inclusion show how to avoid using them.

    example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
      intro x xstu
      have xs : x ∈ s := xstu.1.1
      have xnt : x ∉ t := xstu.1.2
      have xnu : x ∉ u := xstu.2
      constructor
      · exact xs
      intro xtu
      -- x ∈ t ∨ x ∈ u
      rcases xtu with xt | xu
      · show False; exact xnt xt
      · show False; exact xnu xu

    example : (s \ t) \ u ⊆ s \ (t ∪ u) := by
      rintro x ⟨⟨xs, xnt⟩, xnu⟩
      use xs
      rintro (xt | xu) <;> contradiction

As an exercise, prove the reverse inclusion:

    example : s \ (t ∪ u) ⊆ (s \ t) \ u := by
      sorry

To prove that two sets are equal, it suffices to show that every element of one is an element of the other. This principle is known as “extensionality,” and, unsurprisingly, the <span class="pre">`ext`</span> tactic is equipped to handle it.

    example : s ∩ t = t ∩ s := by
      ext x
      simp only [mem_inter_iff]
      constructor
      · rintro ⟨xs, xt⟩; exact ⟨xt, xs⟩
      · rintro ⟨xt, xs⟩; exact ⟨xs, xt⟩

Once again, deleting the line <span class="pre">`simp`</span>` `<span class="pre">`only`</span>` `<span class="pre">`[mem_inter_iff]`</span> does not harm the proof. In fact, if you like inscrutable proof terms, the following one-line proof is for you:

    example : s ∩ t = t ∩ s :=
      Set.ext fun x ↦ ⟨fun ⟨xs, xt⟩ ↦ ⟨xt, xs⟩, fun ⟨xt, xs⟩ ↦ ⟨xs, xt⟩⟩

Here is an even shorter proof, using the simplifier:

    example : s ∩ t = t ∩ s := by ext x; simp [and_comm]

An alternative to using <span class="pre">`ext`</span> is to use the theorem <span class="pre">`Subset.antisymm`</span> which allows us to prove an equation <span class="pre">`s`</span>` `<span class="pre">`=`</span>` `<span class="pre">`t`</span> between sets by proving <span class="pre">`s`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`t`</span> and <span class="pre">`t`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`s`</span>.

    example : s ∩ t = t ∩ s := by
      apply Subset.antisymm
      · rintro x ⟨xs, xt⟩; exact ⟨xt, xs⟩
      · rintro x ⟨xt, xs⟩; exact ⟨xs, xt⟩

Try finishing this proof term:

    example : s ∩ t = t ∩ s :=
        Subset.antisymm sorry sorry

Remember that you can replace sorry by an underscore, and when you hover over it, Lean will show you what it expects at that point.

Here are some set-theoretic identities you might enjoy proving:

    example : s ∩ (s ∪ t) = s := by
      sorry

    example : s ∪ s ∩ t = s := by
      sorry

    example : s \ t ∪ t = s ∪ t := by
      sorry

    example : s \ t ∪ t \ s = (s ∪ t) \ (s ∩ t) := by
      sorry

When it comes to representing sets, here is what is going on underneath the hood. In type theory, a *property* or *predicate* on a type <span class="pre">`α`</span> is just a function <span class="pre">`P`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Prop`</span>. This makes sense: given <span class="pre">`a`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span>, <span class="pre">`P`</span>` `<span class="pre">`a`</span> is just the proposition that <span class="pre">`P`</span> holds of <span class="pre">`a`</span>. In the library, <span class="pre">`Set`</span>` `<span class="pre">`α`</span> is defined to be <span class="pre">`α`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Prop`</span> and <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span> is defined to be <span class="pre">`s`</span>` `<span class="pre">`x`</span>. In other words, sets are really properties, treated as objects.

The library also defines set-builder notation. The expression <span class="pre">`{`</span>` `<span class="pre">`y`</span>` `<span class="pre">`|`</span>` `<span class="pre">`P`</span>` `<span class="pre">`y`</span>` `<span class="pre">`}`</span> unfolds to <span class="pre">`(fun`</span>` `<span class="pre">`y`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`P`</span>` `<span class="pre">`y)`</span>, so <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`{`</span>` `<span class="pre">`y`</span>` `<span class="pre">`|`</span>` `<span class="pre">`P`</span>` `<span class="pre">`y`</span>` `<span class="pre">`}`</span> reduces to <span class="pre">`P`</span>` `<span class="pre">`x`</span>. So we can turn the property of being even into the set of even numbers:

    def evens : Set ℕ :=
      { n | Even n }

    def odds : Set ℕ :=
      { n | ¬Even n }

    example : evens ∪ odds = univ := by
      rw [evens, odds]
      ext n
      simp [-Nat.not_even_iff_odd]
      apply Classical.em

You should step through this proof and make sure you understand what is going on. Note we tell the simplifier to *not* use the lemma <span class="pre">`Nat.not_even_iff`</span> because we want to keep <span class="pre">`¬`</span>` `<span class="pre">`Even`</span>` `<span class="pre">`n`</span> in our goal. Try deleting the line <span class="pre">`rw`</span>` `<span class="pre">`[evens,`</span>` `<span class="pre">`odds]`</span> and confirm that the proof still works.

In fact, set-builder notation is used to define

- <span class="pre">`s`</span>` `<span class="pre">`∩`</span>` `<span class="pre">`t`</span> as <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`t}`</span>,

- <span class="pre">`s`</span>` `<span class="pre">`∪`</span>` `<span class="pre">`t`</span> as <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`∨`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`t}`</span>,

- <span class="pre">`∅`</span> as <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`False}`</span>, and

- <span class="pre">`univ`</span> as <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`True}`</span>.

We often need to indicate the type of <span class="pre">`∅`</span> and <span class="pre">`univ`</span> explicitly, because Lean has trouble guessing which ones we mean. The following examples show how Lean unfolds the last two definitions when needed. In the second one, <span class="pre">`trivial`</span> is the canonical proof of <span class="pre">`True`</span> in the library.

    example (x : ℕ) (h : x ∈ (∅ : Set ℕ)) : False :=
      h

    example (x : ℕ) : x ∈ (univ : Set ℕ) :=
      trivial

As an exercise, prove the following inclusion. Use <span class="pre">`intro`</span>` `<span class="pre">`n`</span> to unfold the definition of subset, and use the simplifier to reduce the set-theoretic constructions to logic. We also recommend using the theorems <span class="pre">`Nat.Prime.eq_two_or_odd`</span> and <span class="pre">`Nat.odd_iff`</span>.

    example : { n | Nat.Prime n } ∩ { n | n > 2 } ⊆ { n | ¬Even n } := by
      sorry

Be careful: it is somewhat confusing that the library has multiple versions of the predicate <span class="pre">`Prime`</span>. The most general one makes sense in any commutative monoid with a zero element. The predicate <span class="pre">`Nat.Prime`</span> is specific to the natural numbers. Fortunately, there is a theorem that says that in the specific case, the two notions agree, so you can always rewrite one to the other.

    #print Prime

    #print Nat.Prime

    example (n : ℕ) : Prime n ↔ Nat.Prime n :=
      Nat.prime_iff.symm

    example (n : ℕ) (h : Prime n) : Nat.Prime n := by
      rw [Nat.prime_iff]
      exact h

The rwa tactic follows a rewrite with the assumption tactic.

    example (n : ℕ) (h : Prime n) : Nat.Prime n := by
      rwa [Nat.prime_iff]

Lean introduces the notation <span class="pre">`∀`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s,`</span>` `<span class="pre">`...`</span>, “for every <span class="pre">`x`</span> in <span class="pre">`s`</span> .,” as an abbreviation for <span class="pre">`∀`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`→`</span>` `<span class="pre">`...`</span>. It also introduces the notation <span class="pre">`∃`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s,`</span>` `<span class="pre">`...,`</span> “there exists an <span class="pre">`x`</span> in <span class="pre">`s`</span> such that ..” These are sometimes known as *bounded quantifiers*, because the construction serves to restrict their significance to the set <span class="pre">`s`</span>. As a result, theorems in the library that make use of them often contain <span class="pre">`ball`</span> or <span class="pre">`bex`</span> in the name. The theorem <span class="pre">`bex_def`</span> asserts that <span class="pre">`∃`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s,`</span>` `<span class="pre">`...`</span> is equivalent to <span class="pre">`∃`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`...,`</span> but when they are used with <span class="pre">`rintro`</span>, <span class="pre">`use`</span>, and anonymous constructors, these two expressions behave roughly the same. As a result, we usually don’t need to use <span class="pre">`bex_def`</span> to transform them explicitly. Here are some examples of how they are used:

    variable (s t : Set ℕ)

    example (h₀ : ∀ x ∈ s, ¬Even x) (h₁ : ∀ x ∈ s, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
      intro x xs
      constructor
      · apply h₀ x xs
      apply h₁ x xs

    example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ s, Prime x := by
      rcases h with ⟨x, xs, _, prime_x⟩
      use x, xs

See if you can prove these slight variations:

    section
    variable (ssubt : s ⊆ t)

    example (h₀ : ∀ x ∈ t, ¬Even x) (h₁ : ∀ x ∈ t, Prime x) : ∀ x ∈ s, ¬Even x ∧ Prime x := by
      sorry

    example (h : ∃ x ∈ s, ¬Even x ∧ Prime x) : ∃ x ∈ t, Prime x := by
      sorry

    end

Indexed unions and intersections are another important set-theoretic construction. We can model a sequence <span class="math notranslate nohighlight">\\A\_0, A\_1, A\_2, \ldots\\</span> of sets of elements of <span class="pre">`α`</span> as a function <span class="pre">`A`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℕ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`α`</span>, in which case <span class="pre">`⋃`</span>` `<span class="pre">`i,`</span>` `<span class="pre">`A`</span>` `<span class="pre">`i`</span> denotes their union, and <span class="pre">`⋂`</span>` `<span class="pre">`i,`</span>` `<span class="pre">`A`</span>` `<span class="pre">`i`</span> denotes their intersection. There is nothing special about the natural numbers here, so <span class="pre">`ℕ`</span> can be replaced by any type <span class="pre">`I`</span> used to index the sets. The following illustrates their use.

    variable {α I : Type*}
    variable (A B : I → Set α)
    variable (s : Set α)

    open Set

    example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by
      ext x
      simp only [mem_inter_iff, mem_iUnion]
      constructor
      · rintro ⟨xs, ⟨i, xAi⟩⟩
        exact ⟨i, xAi, xs⟩
      rintro ⟨i, xAi, xs⟩
      exact ⟨xs, ⟨i, xAi⟩⟩

    example : (⋂ i, A i ∩ B i) = (⋂ i, A i) ∩ ⋂ i, B i := by
      ext x
      simp only [mem_inter_iff, mem_iInter]
      constructor
      · intro h
        constructor
        · intro i
          exact (h i).1
        intro i
        exact (h i).2
      rintro ⟨h1, h2⟩ i
      constructor
      · exact h1 i
      exact h2 i

Parentheses are often needed with an indexed union or intersection because, as with the quantifiers, the scope of the bound variable extends as far as it can.

Try proving the following identity. One direction requires classical logic! We recommend using <span class="pre">`by_cases`</span>` `<span class="pre">`xs`</span>` `<span class="pre">`:`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span> at an appropriate point in the proof.

    example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by
      sorry

Mathlib also has bounded unions and intersections, which are analogous to the bounded quantifiers. You can unpack their meaning with <span class="pre">`mem_iUnion₂`</span> and <span class="pre">`mem_iInter₂`</span>. As the following examples show, Lean’s simplifier carries out these replacements as well.

    def primes : Set ℕ :=
      { x | Nat.Prime x }

    example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } :=by
      ext
      rw [mem_iUnion₂]
      simp

    example : (⋃ p ∈ primes, { x | p ^ 2 ∣ x }) = { x | ∃ p ∈ primes, p ^ 2 ∣ x } := by
      ext
      simp

    example : (⋂ p ∈ primes, { x | ¬p ∣ x }) ⊆ { x | x = 1 } := by
      intro x
      contrapose!
      simp
      apply Nat.exists_prime_and_dvd

Try solving the following example, which is similar. If you start typing <span class="pre">`eq_univ`</span>, tab completion will tell you that <span class="pre">`apply`</span>` `<span class="pre">`eq_univ_of_forall`</span> is a good way to start the proof. We also recommend using the theorem <span class="pre">`Nat.exists_infinite_primes`</span>.

    example : (⋃ p ∈ primes, { x | x ≤ p }) = univ := by
      sorry

Give a collection of sets, <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`(Set`</span>` `<span class="pre">`α)`</span>, their union, <span class="pre">`⋃₀`</span>` `<span class="pre">`s`</span>, has type <span class="pre">`Set`</span>` `<span class="pre">`α`</span> and is defined as <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`∃`</span>` `<span class="pre">`t`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`t}`</span>. Similarly, their intersection, <span class="pre">`⋂₀`</span>` `<span class="pre">`s`</span>, is defined as <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`∀`</span>` `<span class="pre">`t`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`t}`</span>. These operations are called <span class="pre">`sUnion`</span> and <span class="pre">`sInter`</span>, respectively. The following examples show their relationship to bounded union and intersection.

    variable {α : Type*} (s : Set (Set α))

    example : ⋃₀ s = ⋃ t ∈ s, t := by
      ext x
      rw [mem_iUnion₂]
      simp

    example : ⋂₀ s = ⋂ t ∈ s, t := by
      ext x
      rw [mem_iInter₂]
      rfl

In the library, these identities are called <span class="pre">`sUnion_eq_biUnion`</span> and <span class="pre">`sInter_eq_biInter`</span>.

<span id="id3"></span>

## <span class="section-number">4.2. </span>Functions<a href="#functions" class="headerlink" title="Link to this heading"></a>

If <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span>` `<span class="pre">`→`</span>` `<span class="pre">`β`</span> is a function and <span class="pre">`p`</span> is a set of elements of type <span class="pre">`β`</span>, the library defines <span class="pre">`preimage`</span>` `<span class="pre">`f`</span>` `<span class="pre">`p`</span>, written <span class="pre">`f`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`p`</span>, to be <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`p}`</span>. The expression <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`f`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`p`</span> reduces to <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`p`</span>. This is often convenient, as in the following example:

    variable {α β : Type*}
    variable (f : α → β)
    variable (s t : Set α)
    variable (u v : Set β)

    open Function
    open Set

    example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by
      ext
      rfl

If <span class="pre">`s`</span> is a set of elements of type <span class="pre">`α`</span>, the library also defines <span class="pre">`image`</span>` `<span class="pre">`f`</span>` `<span class="pre">`s`</span>, written <span class="pre">`f`</span>` `<span class="pre">`''`</span>` `<span class="pre">`s`</span>, to be <span class="pre">`{y`</span>` `<span class="pre">`|`</span>` `<span class="pre">`∃`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y}`</span>. So a hypothesis <span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`f`</span>` `<span class="pre">`''`</span>` `<span class="pre">`s`</span> decomposes to a triple <span class="pre">`⟨x,`</span>` `<span class="pre">`xs,`</span>` `<span class="pre">`xeq⟩`</span> with <span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span> satisfying the hypotheses <span class="pre">`xs`</span>` `<span class="pre">`:`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span> and <span class="pre">`xeq`</span>` `<span class="pre">`:`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y`</span>. The <span class="pre">`rfl`</span> tag in the <span class="pre">`rintro`</span> tactic (see <a href="C03_Logic.html#the-existential-quantifier" class="reference internal"><span class="std std-numref">Section 3.2</span></a>) was made precisely for this sort of situation.

    example : f '' (s ∪ t) = f '' s ∪ f '' t := by
      ext y; constructor
      · rintro ⟨x, xs | xt, rfl⟩
        · left
          use x, xs
        right
        use x, xt
      rintro (⟨x, xs, rfl⟩ | ⟨x, xt, rfl⟩)
      · use x, Or.inl xs
      use x, Or.inr xt

Notice also that the <span class="pre">`use`</span> tactic applies <span class="pre">`rfl`</span> to close goals when it can.

Here is another example:

    example : s ⊆ f ⁻¹' (f '' s) := by
      intro x xs
      show f x ∈ f '' s
      use x, xs

We can replace the line <span class="pre">`use`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`xs`</span> by <span class="pre">`apply`</span>` `<span class="pre">`mem_image_of_mem`</span>` `<span class="pre">`f`</span>` `<span class="pre">`xs`</span> if we want to use a theorem specifically designed for that purpose. But knowing that the image is defined in terms of an existential quantifier is often convenient.

The following equivalence is a good exercise:

    example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by
      sorry

It shows that <span class="pre">`image`</span>` `<span class="pre">`f`</span> and <span class="pre">`preimage`</span>` `<span class="pre">`f`</span> are an instance of what is known as a *Galois connection* between <span class="pre">`Set`</span>` `<span class="pre">`α`</span> and <span class="pre">`Set`</span>` `<span class="pre">`β`</span>, each partially ordered by the subset relation. In the library, this equivalence is named <span class="pre">`image_subset_iff`</span>. In practice, the right-hand side is often the more useful representation, because <span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`f`</span>` `<span class="pre">`⁻¹'`</span>` `<span class="pre">`t`</span> unfolds to <span class="pre">`f`</span>` `<span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`t`</span> whereas working with <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`f`</span>` `<span class="pre">`''`</span>` `<span class="pre">`s`</span> requires decomposing an existential quantifier.

Here is a long list of set-theoretic identities for you to enjoy. You don’t have to do all of them at once; do a few of them, and set the rest aside for a rainy day.

    example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by
      sorry

    example : f '' (f ⁻¹' u) ⊆ u := by
      sorry

    example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by
      sorry

    example (h : s ⊆ t) : f '' s ⊆ f '' t := by
      sorry

    example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by
      sorry

    example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by
      sorry

    example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by
      sorry

    example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by
      sorry

    example : f '' s \ f '' t ⊆ f '' (s \ t) := by
      sorry

    example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by
      sorry

    example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by
      sorry

    example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by
      sorry

    example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by
      sorry

    example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by
      sorry

You can also try your hand at the next group of exercises, which characterize the behavior of images and preimages with respect to indexed unions and intersections. In the third exercise, the argument <span class="pre">`i`</span>` `<span class="pre">`:`</span>` `<span class="pre">`I`</span> is needed to guarantee that the index set is nonempty. To prove any of these, we recommend using <span class="pre">`ext`</span> or <span class="pre">`intro`</span> to unfold the meaning of an equation or inclusion between sets, and then calling <span class="pre">`simp`</span> to unpack the conditions for membership.

    variable {I : Type*} (A : I → Set α) (B : I → Set β)

    example : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by
      sorry

    example : (f '' ⋂ i, A i) ⊆ ⋂ i, f '' A i := by
      sorry

    example (i : I) (injf : Injective f) : (⋂ i, f '' A i) ⊆ f '' ⋂ i, A i := by
      sorry

    example : (f ⁻¹' ⋃ i, B i) = ⋃ i, f ⁻¹' B i := by
      sorry

    example : (f ⁻¹' ⋂ i, B i) = ⋂ i, f ⁻¹' B i := by
      sorry

The library defines a predicate <span class="pre">`InjOn`</span>` `<span class="pre">`f`</span>` `<span class="pre">`s`</span> to say that <span class="pre">`f`</span> is injective on <span class="pre">`s`</span>. It is defined as follows:

    example : InjOn f s ↔ ∀ x₁ ∈ s, ∀ x₂ ∈ s, f x₁ = f x₂ → x₁ = x₂ :=
      Iff.refl _

The statement <span class="pre">`Injective`</span>` `<span class="pre">`f`</span> is provably equivalent to <span class="pre">`InjOn`</span>` `<span class="pre">`f`</span>` `<span class="pre">`univ`</span>. Similarly, the library defines <span class="pre">`range`</span>` `<span class="pre">`f`</span> to be <span class="pre">`{x`</span>` `<span class="pre">`|`</span>` `<span class="pre">`∃y,`</span>` `<span class="pre">`f`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`x}`</span>, so <span class="pre">`range`</span>` `<span class="pre">`f`</span> is provably equal to <span class="pre">`f`</span>` `<span class="pre">`''`</span>` `<span class="pre">`univ`</span>. This is a common theme in Mathlib: although many properties of functions are defined relative to their full domain, there are often relativized versions that restrict the statements to a subset of the domain type.

Here are some examples of <span class="pre">`InjOn`</span> and <span class="pre">`range`</span> in use:

    open Set Real

    example : InjOn log { x | x > 0 } := by
      intro x xpos y ypos
      intro e
      -- log x = log y
      calc
        x = exp (log x) := by rw [exp_log xpos]
        _ = exp (log y) := by rw [e]
        _ = y := by rw [exp_log ypos]


    example : range exp = { y | y > 0 } := by
      ext y; constructor
      · rintro ⟨x, rfl⟩
        apply exp_pos
      intro ypos
      use log y
      rw [exp_log ypos]

Try proving these:

    example : InjOn sqrt { x | x ≥ 0 } := by
      sorry

    example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by
      sorry

    example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by
      sorry

    example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by
      sorry

To define the inverse of a function <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span>` `<span class="pre">`→`</span>` `<span class="pre">`β`</span>, we will use two new ingredients. First, we need to deal with the fact that an arbitrary type in Lean may be empty. To define the inverse to <span class="pre">`f`</span> at <span class="pre">`y`</span> when there is no <span class="pre">`x`</span> satisfying <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y`</span>, we want to assign a default value in <span class="pre">`α`</span>. Adding the annotation <span class="pre">`[Inhabited`</span>` `<span class="pre">`α]`</span> as a variable is tantamount to assuming that <span class="pre">`α`</span> has a preferred element, which is denoted <span class="pre">`default`</span>. Second, in the case where there is more than one <span class="pre">`x`</span> such that <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y`</span>, the inverse function needs to *choose* one of them. This requires an appeal to the *axiom of choice*. Lean allows various ways of accessing it; one convenient method is to use the classical <span class="pre">`choose`</span> operator, illustrated below.

    variable {α β : Type*} [Inhabited α]

    #check (default : α)

    variable (P : α → Prop) (h : ∃ x, P x)

    #check Classical.choose h

    example : P (Classical.choose h) :=
      Classical.choose_spec h

Given <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`∃`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span>, the value of <span class="pre">`Classical.choose`</span>` `<span class="pre">`h`</span> is some <span class="pre">`x`</span> satisfying <span class="pre">`P`</span>` `<span class="pre">`x`</span>. The theorem <span class="pre">`Classical.choose_spec`</span>` `<span class="pre">`h`</span> says that <span class="pre">`Classical.choose`</span>` `<span class="pre">`h`</span> meets this specification.

With these in hand, we can define the inverse function as follows:

    noncomputable section

    open Classical

    def inverse (f : α → β) : β → α := fun y : β ↦
      if h : ∃ x, f x = y then Classical.choose h else default

    theorem inverse_spec {f : α → β} (y : β) (h : ∃ x, f x = y) : f (inverse f y) = y := by
      rw [inverse, dif_pos h]
      exact Classical.choose_spec h

The lines <span class="pre">`noncomputable`</span>` `<span class="pre">`section`</span> and <span class="pre">`open`</span>` `<span class="pre">`Classical`</span> are needed because we are using classical logic in an essential way. On input <span class="pre">`y`</span>, the function <span class="pre">`inverse`</span>` `<span class="pre">`f`</span> returns some value of <span class="pre">`x`</span> satisfying <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y`</span> if there is one, and a default element of <span class="pre">`α`</span> otherwise. This is an instance of a *dependent if* construction, since in the positive case, the value returned, <span class="pre">`Classical.choose`</span>` `<span class="pre">`h`</span>, depends on the assumption <span class="pre">`h`</span>. The identity <span class="pre">`dif_pos`</span>` `<span class="pre">`h`</span> rewrites <span class="pre">`if`</span>` `<span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`e`</span>` `<span class="pre">`then`</span>` `<span class="pre">`a`</span>` `<span class="pre">`else`</span>` `<span class="pre">`b`</span> to <span class="pre">`a`</span> given <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`e`</span>, and, similarly, <span class="pre">`dif_neg`</span>` `<span class="pre">`h`</span> rewrites it to <span class="pre">`b`</span> given <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`e`</span>. There are also versions <span class="pre">`if_pos`</span> and <span class="pre">`if_neg`</span> that works for non-dependent if constructions and will be used in the next section. The theorem <span class="pre">`inverse_spec`</span> says that <span class="pre">`inverse`</span>` `<span class="pre">`f`</span> meets the first part of this specification.

Don’t worry if you do not fully understand how these work. The theorem <span class="pre">`inverse_spec`</span> alone should be enough to show that <span class="pre">`inverse`</span>` `<span class="pre">`f`</span> is a left inverse if and only if <span class="pre">`f`</span> is injective and a right inverse if and only if <span class="pre">`f`</span> is surjective. Look up the definition of <span class="pre">`LeftInverse`</span> and <span class="pre">`RightInverse`</span> by double-clicking or right-clicking on them in VS Code, or using the commands <span class="pre">`#print`</span>` `<span class="pre">`LeftInverse`</span> and <span class="pre">`#print`</span>` `<span class="pre">`RightInverse`</span>. Then try to prove the two theorems. They are tricky! It helps to do the proofs on paper before you start hacking through the details. You should be able to prove each of them with about a half-dozen short lines. If you are looking for an extra challenge, try to condense each proof to a single-line proof term.

    variable (f : α → β)

    open Function

    example : Injective f ↔ LeftInverse (inverse f) f :=
      sorry

    example : Surjective f ↔ RightInverse (inverse f) f :=
      sorry

We close this section with a type-theoretic statement of Cantor’s famous theorem that there is no surjective function from a set to its power set. See if you can understand the proof, and then fill in the two lines that are missing.

    theorem Cantor : ∀ f : α → Set α, ¬Surjective f := by
      intro f surjf
      let S := { i | i ∉ f i }
      rcases surjf S with ⟨j, h⟩
      have h₁ : j ∉ f j := by
        intro h'
        have : j ∉ f j := by rwa [h] at h'
        contradiction
      have h₂ : j ∈ S
      sorry
      have h₃ : j ∉ S
      sorry
      contradiction

<span id="the-schroeder-bernstein-theorem"></span>

## <span class="section-number">4.3. </span>The Schröder-Bernstein Theorem<a href="#the-schroder-bernstein-theorem" class="headerlink" title="Link to this heading"></a>

We close this chapter with an elementary but nontrivial theorem of set theory. Let <span class="math notranslate nohighlight">\\\alpha\\</span> and <span class="math notranslate nohighlight">\\\beta\\</span> be sets. (In our formalization, they will actually be types.) Suppose <span class="math notranslate nohighlight">\\f : \alpha → \beta\\</span> and <span class="math notranslate nohighlight">\\g : \beta → \alpha\\</span> are both injective. Intuitively, this means that <span class="math notranslate nohighlight">\\\alpha\\</span> is no bigger than <span class="math notranslate nohighlight">\\\beta\\</span> and vice-versa. If <span class="math notranslate nohighlight">\\\alpha\\</span> and <span class="math notranslate nohighlight">\\\beta\\</span> are finite, this implies that they have the same cardinality, which is equivalent to saying that there is a bijection between them. In the nineteenth century, Cantor stated that same result holds even in the case where <span class="math notranslate nohighlight">\\\alpha\\</span> and <span class="math notranslate nohighlight">\\\beta\\</span> are infinite. This was eventually established by Dedekind, Schröder, and Bernstein independently.

Our formalization will introduce some new methods that we will explain in greater detail in chapters to come. Don’t worry if they go by too quickly here. Our goal is to show you that you already have the skills to contribute to the formal proof of a real mathematical result.

To understand the idea behind the proof, consider the image of the map <span class="math notranslate nohighlight">\\g\\</span> in <span class="math notranslate nohighlight">\\\alpha\\</span>. On that image, the inverse of <span class="math notranslate nohighlight">\\g\\</span> is defined and is a bijection with <span class="math notranslate nohighlight">\\\beta\\</span>.

<a href="_images/schroeder_bernstein1.png" class="reference internal image-reference"><img src="_images/schroeder_bernstein1.png" class="align-center" style="height: 150px;" alt="the Schröder Bernstein theorem" /></a>

The problem is that the bijection does not include the shaded region in the diagram, which is nonempty if <span class="math notranslate nohighlight">\\g\\</span> is not surjective. Alternatively, we can use <span class="math notranslate nohighlight">\\f\\</span> to map all of <span class="math notranslate nohighlight">\\\alpha\\</span> to <span class="math notranslate nohighlight">\\\beta\\</span>, but in that case the problem is that if <span class="math notranslate nohighlight">\\f\\</span> is not surjective, it will miss some elements of <span class="math notranslate nohighlight">\\\beta\\</span>.

<a href="_images/schroeder_bernstein2.png" class="reference internal image-reference"><img src="_images/schroeder_bernstein2.png" class="align-center" style="height: 150px;" alt="the Schröder Bernstein theorem" /></a>

But now consider the composition <span class="math notranslate nohighlight">\\g \circ f\\</span> from <span class="math notranslate nohighlight">\\\alpha\\</span> to itself. Because the composition is injective, it forms a bijection between <span class="math notranslate nohighlight">\\\alpha\\</span> and its image, yielding a scaled-down copy of <span class="math notranslate nohighlight">\\\alpha\\</span> inside itself.

<a href="_images/schroeder_bernstein3.png" class="reference internal image-reference"><img src="_images/schroeder_bernstein3.png" class="align-center" style="height: 150px;" alt="the Schröder Bernstein theorem" /></a>

This composition maps the inner shaded ring to yet another such set, which we can think of as an even smaller concentric shaded ring, and so on. This yields a concentric sequence of shaded rings, each of which is in bijective correspondence with the next. If we map each ring to the next and leave the unshaded parts of <span class="math notranslate nohighlight">\\\alpha\\</span> alone, we have a bijection of <span class="math notranslate nohighlight">\\\alpha\\</span> with the image of <span class="math notranslate nohighlight">\\g\\</span>. Composing with <span class="math notranslate nohighlight">\\g^{-1}\\</span>, this yields the desired bijection between <span class="math notranslate nohighlight">\\\alpha\\</span> and <span class="math notranslate nohighlight">\\\beta\\</span>.

We can describe this bijection more simply. Let <span class="math notranslate nohighlight">\\A\\</span> be the union of the sequence of shaded regions, and define <span class="math notranslate nohighlight">\\h : \alpha \to \beta\\</span> as follows:

\\\begin{split}h(x) = \begin{cases} f(x) & \text{if $x \in A$} \\ g^{-1}(x) & \text{otherwise.} \end{cases}\end{split}\\

In other words, we use <span class="math notranslate nohighlight">\\f\\</span> on the shaded parts, and we use the inverse of <span class="math notranslate nohighlight">\\g\\</span> everywhere else. The resulting map <span class="math notranslate nohighlight">\\h\\</span> is injective because each component is injective and the images of the two components are disjoint. To see that it is surjective, suppose we are given a <span class="math notranslate nohighlight">\\y\\</span> in <span class="math notranslate nohighlight">\\\beta\\</span>, and consider <span class="math notranslate nohighlight">\\g(y)\\</span>. If <span class="math notranslate nohighlight">\\g(y)\\</span> is in one of the shaded regions, it cannot be in the first ring, so we have <span class="math notranslate nohighlight">\\g(y) = g(f(x))\\</span> for some <span class="math notranslate nohighlight">\\x\\</span> is in the previous ring. By the injectivity of <span class="math notranslate nohighlight">\\g\\</span>, we have <span class="math notranslate nohighlight">\\h(x) = f(x) = y\\</span>. If <span class="math notranslate nohighlight">\\g(y)\\</span> is not in the shaded region, then by the definition of <span class="math notranslate nohighlight">\\h\\</span>, we have <span class="math notranslate nohighlight">\\h(g(y))= y\\</span>. Either way, <span class="math notranslate nohighlight">\\y\\</span> is in the image of <span class="math notranslate nohighlight">\\h\\</span>.

This argument should sound plausible, but the details are delicate. Formalizing the proof will not only improve our confidence in the result, but also help us understand it better. Because the proof uses classical logic, we tell Lean that our definitions will generally not be computable.

    noncomputable section
    open Classical
    variable {α β : Type*} [Nonempty β]

The annotation <span class="pre">`[Nonempty`</span>` `<span class="pre">`β]`</span> specifies that <span class="pre">`β`</span> is nonempty. We use it because the Mathlib primitive that we will use to construct <span class="math notranslate nohighlight">\\g^{-1}\\</span> requires it. The case of the theorem where <span class="math notranslate nohighlight">\\\beta\\</span> is empty is trivial, and even though it would not be hard to generalize the formalization to cover that case as well, we will not bother. Specifically, we need the hypothesis <span class="pre">`[Nonempty`</span>` `<span class="pre">`β]`</span> for the operation <span class="pre">`invFun`</span> that is defined in Mathlib. Given <span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span>, <span class="pre">`invFun`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x`</span> chooses a preimage of <span class="pre">`x`</span> in <span class="pre">`β`</span> if there is one, and returns an arbitrary element of <span class="pre">`β`</span> otherwise. The function <span class="pre">`invFun`</span>` `<span class="pre">`g`</span> is always a left inverse if <span class="pre">`g`</span> is injective and a right inverse if <span class="pre">`g`</span> is surjective.

    #check (invFun g : α → β)
    #check (leftInverse_invFun : Injective g → LeftInverse (invFun g) g)
    #check (leftInverse_invFun : Injective g → ∀ y, invFun g (g y) = y)
    #check (invFun_eq : (∃ y, g y = x) → g (invFun g x) = x)

We define the set corresponding to the union of the shaded regions as follows.

    variable (f : α → β) (g : β → α)

    def sbAux : ℕ → Set α
      | 0 => univ \ g '' univ
      | n + 1 => g '' (f '' sbAux n)

    def sbSet :=
      ⋃ n, sbAux f g n

The definition <span class="pre">`sbAux`</span> is an example of a *recursive definition*, which we will explain in the next chapter. It defines a sequence of sets

\\\begin{split}S\_0 &= \alpha ∖ g(\beta) \\ S\_{n+1} &= g(f(S\_n)).\end{split}\\

The definition <span class="pre">`sbSet`</span> corresponds to the set <span class="math notranslate nohighlight">\\A = \bigcup\_{n \in \mathbb{N}} S\_n\\</span> in our proof sketch. The function <span class="math notranslate nohighlight">\\h\\</span> described above is now defined as follows:

    def sbFun (x : α) : β :=
      if x ∈ sbSet f g then f x else invFun g x

We will need the fact that our definition of <span class="math notranslate nohighlight">\\g^{-1}\\</span> is a right inverse on the complement of <span class="math notranslate nohighlight">\\A\\</span>, which is to say, on the non-shaded regions of <span class="math notranslate nohighlight">\\\alpha\\</span>. This is so because the outermost ring, <span class="math notranslate nohighlight">\\S\_0\\</span>, is equal to <span class="math notranslate nohighlight">\\\alpha \setminus g(\beta)\\</span>, so the complement of <span class="math notranslate nohighlight">\\A\\</span> is contained in <span class="math notranslate nohighlight">\\g(\beta)\\</span>. As a result, for every <span class="math notranslate nohighlight">\\x\\</span> in the complement of <span class="math notranslate nohighlight">\\A\\</span>, there is a <span class="math notranslate nohighlight">\\y\\</span> such that <span class="math notranslate nohighlight">\\g(y) = x\\</span>. (By the injectivity of <span class="math notranslate nohighlight">\\g\\</span>, this <span class="math notranslate nohighlight">\\y\\</span> is unique, but next theorem says only that <span class="pre">`invFun`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x`</span> returns some <span class="pre">`y`</span> such that <span class="pre">`g`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`x`</span>.)

Step through the proof below, make sure you understand what is going on, and fill in the remaining parts. You will need to use <span class="pre">`invFun_eq`</span> at the end. Notice that rewriting with <span class="pre">`sbAux`</span> here replaces <span class="pre">`sbAux`</span>` `<span class="pre">`f`</span>` `<span class="pre">`g`</span>` `<span class="pre">`0`</span> with the right-hand side of the corresponding defining equation.

    theorem sb_right_inv {x : α} (hx : x ∉ sbSet f g) : g (invFun g x) = x := by
      have : x ∈ g '' univ := by
        contrapose! hx
        rw [sbSet, mem_iUnion]
        use 0
        rw [sbAux, mem_diff]
        sorry
      have : ∃ y, g y = x := by
        sorry
      sorry

We now turn to the proof that <span class="math notranslate nohighlight">\\h\\</span> is injective. Informally, the proof goes as follows. First, suppose <span class="math notranslate nohighlight">\\h(x\_1) = h(x\_2)\\</span>. If <span class="math notranslate nohighlight">\\x\_1\\</span> is in <span class="math notranslate nohighlight">\\A\\</span>, then <span class="math notranslate nohighlight">\\h(x\_1) = f(x\_1)\\</span>, and we can show that <span class="math notranslate nohighlight">\\x\_2\\</span> is in <span class="math notranslate nohighlight">\\A\\</span> as follows. If it isn’t, then we have <span class="math notranslate nohighlight">\\h(x\_2) = g^{-1}(x\_2)\\</span>. From <span class="math notranslate nohighlight">\\f(x\_1) = h(x\_1) = h(x\_2)\\</span> we have <span class="math notranslate nohighlight">\\g(f(x\_1)) = x\_2\\</span>. From the definition of <span class="math notranslate nohighlight">\\A\\</span>, since <span class="math notranslate nohighlight">\\x\_1\\</span> is in <span class="math notranslate nohighlight">\\A\\</span>, <span class="math notranslate nohighlight">\\x\_2\\</span> is in <span class="math notranslate nohighlight">\\A\\</span> as well, a contradiction. Hence, if <span class="math notranslate nohighlight">\\x\_1\\</span> is in <span class="math notranslate nohighlight">\\A\\</span>, so is <span class="math notranslate nohighlight">\\x\_2\\</span>, in which case we have <span class="math notranslate nohighlight">\\f(x\_1) = h(x\_1) = h(x\_2) = f(x\_2)\\</span>. The injectivity of <span class="math notranslate nohighlight">\\f\\</span> then implies <span class="math notranslate nohighlight">\\x\_1 = x\_2\\</span>. The symmetric argument shows that if <span class="math notranslate nohighlight">\\x\_2\\</span> is in <span class="math notranslate nohighlight">\\A\\</span>, then so is <span class="math notranslate nohighlight">\\x\_1\\</span>, which again implies <span class="math notranslate nohighlight">\\x\_1 = x\_2\\</span>.

The only remaining possibility is that neither <span class="math notranslate nohighlight">\\x\_1\\</span> nor <span class="math notranslate nohighlight">\\x\_2\\</span> is in <span class="math notranslate nohighlight">\\A\\</span>. In that case, we have <span class="math notranslate nohighlight">\\g^{-1}(x\_1) = h(x\_1) = h(x\_2) = g^{-1}(x\_2)\\</span>. Applying <span class="math notranslate nohighlight">\\g\\</span> to both sides yields <span class="math notranslate nohighlight">\\x\_1 = x\_2\\</span>.

Once again, we encourage you to step through the following proof to see how the argument plays out in Lean. See if you can finish off the proof using <span class="pre">`sb_right_inv`</span>.

    theorem sb_injective (hf : Injective f) : Injective (sbFun f g) := by
      set A := sbSet f g with A_def
      set h := sbFun f g with h_def
      intro x₁ x₂
      intro (hxeq : h x₁ = h x₂)
      show x₁ = x₂
      simp only [h_def, sbFun, ← A_def] at hxeq
      by_cases xA : x₁ ∈ A ∨ x₂ ∈ A
      · wlog x₁A : x₁ ∈ A generalizing x₁ x₂ hxeq xA
        · symm
          apply this hxeq.symm xA.symm (xA.resolve_left x₁A)
        have x₂A : x₂ ∈ A := by
          apply _root_.not_imp_self.mp
          intro (x₂nA : x₂ ∉ A)
          rw [if_pos x₁A, if_neg x₂nA] at hxeq
          rw [A_def, sbSet, mem_iUnion] at x₁A
          have x₂eq : x₂ = g (f x₁) := by
            sorry
          rcases x₁A with ⟨n, hn⟩
          rw [A_def, sbSet, mem_iUnion]
          use n + 1
          simp [sbAux]
          exact ⟨x₁, hn, x₂eq.symm⟩
        sorry
      push_neg at xA
      sorry

The proof introduces some new tactics. To start with, notice the <span class="pre">`set`</span> tactic, which introduces abbreviations <span class="pre">`A`</span> and <span class="pre">`h`</span> for <span class="pre">`sbSet`</span>` `<span class="pre">`f`</span>` `<span class="pre">`g`</span> and <span class="pre">`sb_fun`</span>` `<span class="pre">`f`</span>` `<span class="pre">`g`</span> respectively. We name the corresponding defining equations <span class="pre">`A_def`</span> and <span class="pre">`h_def`</span>. The abbreviations are definitional, which is to say, Lean will sometimes unfold them automatically when needed. But not always; for example, when using <span class="pre">`rw`</span>, we generally need to use <span class="pre">`A_def`</span> and <span class="pre">`h_def`</span> explicitly. So the definitions bring a tradeoff: they can make expressions shorter and more readable, but they sometimes require us to do more work.

A more interesting tactic is the <span class="pre">`wlog`</span> tactic, which encapsulates the symmetry argument in the informal proof above. We will not dwell on it now, but notice that it does exactly what we want. If you hover over the tactic you can take a look at its documentation.

The argument for surjectivity is even easier. Given <span class="math notranslate nohighlight">\\y\\</span> in <span class="math notranslate nohighlight">\\\beta\\</span>, we consider two cases, depending on whether <span class="math notranslate nohighlight">\\g(y)\\</span> is in <span class="math notranslate nohighlight">\\A\\</span>. If it is, it can’t be in <span class="math notranslate nohighlight">\\S\_0\\</span>, the outermost ring, because by definition that is disjoint from the image of <span class="math notranslate nohighlight">\\g\\</span>. Thus it is an element of <span class="math notranslate nohighlight">\\S\_{n+1}\\</span> for some <span class="math notranslate nohighlight">\\n\\</span>. This means that it is of the form <span class="math notranslate nohighlight">\\g(f(x))\\</span> for some <span class="math notranslate nohighlight">\\x\\</span> in <span class="math notranslate nohighlight">\\S\_n\\</span>. By the injectivity of <span class="math notranslate nohighlight">\\g\\</span>, we have <span class="math notranslate nohighlight">\\f(x) = y\\</span>. In the case where <span class="math notranslate nohighlight">\\g(y)\\</span> is in the complement of <span class="math notranslate nohighlight">\\A\\</span>, we immediately have <span class="math notranslate nohighlight">\\h(g(y))= y\\</span>, and we are done.

Once again, we encourage you to step through the proof and fill in the missing parts. The tactic <span class="pre">`rcases`</span>` `<span class="pre">`n`</span>` `<span class="pre">`with`</span>` `<span class="pre">`_`</span>` `<span class="pre">`|`</span>` `<span class="pre">`n`</span> splits on the cases <span class="pre">`g`</span>` `<span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`sbAux`</span>` `<span class="pre">`f`</span>` `<span class="pre">`g`</span>` `<span class="pre">`0`</span> and <span class="pre">`g`</span>` `<span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`sbAux`</span>` `<span class="pre">`f`</span>` `<span class="pre">`g`</span>` `<span class="pre">`(n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1)`</span>. In both cases, calling the simplifier with <span class="pre">`simp`</span>` `<span class="pre">`[sbAux]`</span> applies the corresponding defining equation of <span class="pre">`sbAux`</span>.

    theorem sb_surjective (hg : Injective g) : Surjective (sbFun f g) := by
      set A := sbSet f g with A_def
      set h := sbFun f g with h_def
      intro y
      by_cases gyA : g y ∈ A
      · rw [A_def, sbSet, mem_iUnion] at gyA
        rcases gyA with ⟨n, hn⟩
        rcases n with _ | n
        · simp [sbAux] at hn
        simp [sbAux] at hn
        rcases hn with ⟨x, xmem, hx⟩
        use x
        have : x ∈ A := by
          rw [A_def, sbSet, mem_iUnion]
          exact ⟨n, xmem⟩
        rw [h_def, sbFun, if_pos this]
        apply hg hx

      sorry

We can now put it all together. The final statement is short and sweet, and the proof uses the fact that <span class="pre">`Bijective`</span>` `<span class="pre">`h`</span> unfolds to <span class="pre">`Injective`</span>` `<span class="pre">`h`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`Surjective`</span>` `<span class="pre">`h`</span>.

    theorem schroeder_bernstein {f : α → β} {g : β → α} (hf : Injective f) (hg : Injective g) :
        ∃ h : α → β, Bijective h :=
      ⟨sbFun f g, sb_injective f g hf, sb_surjective f g hg⟩
