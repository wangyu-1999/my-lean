<span id="number-theory"></span>

# <span class="section-number">5. </span>Elementary Number Theory<a href="#elementary-number-theory" class="headerlink" title="Link to this heading"></a>

In this chapter, we show you how to formalize some elementary results in number theory. As we deal with more substantive mathematical content, the proofs will get longer and more involved, building on the skills you have already mastered.

<span id="section-irrational-roots"></span>

## <span class="section-number">5.1. </span>Irrational Roots<a href="#irrational-roots" class="headerlink" title="Link to this heading"></a>

Let’s start with a fact known to the ancient Greeks, namely, that the square root of 2 is irrational. If we suppose otherwise, we can write <span class="math notranslate nohighlight">\\\sqrt{2} = a / b\\</span> as a fraction in lowest terms. Squaring both sides yields <span class="math notranslate nohighlight">\\a^2 = 2 b^2\\</span>, which implies that <span class="math notranslate nohighlight">\\a\\</span> is even. If we write <span class="math notranslate nohighlight">\\a = 2c\\</span>, then we get <span class="math notranslate nohighlight">\\4c^2 = 2 b^2\\</span> and hence <span class="math notranslate nohighlight">\\b^2 = 2 c^2\\</span>. This implies that <span class="math notranslate nohighlight">\\b\\</span> is also even, contradicting the fact that we have assumed that <span class="math notranslate nohighlight">\\a / b\\</span> has been reduced to lowest terms.

Saying that <span class="math notranslate nohighlight">\\a / b\\</span> is a fraction in lowest terms means that <span class="math notranslate nohighlight">\\a\\</span> and <span class="math notranslate nohighlight">\\b\\</span> do not have any factors in common, which is to say, they are *coprime*. Mathlib defines the predicate <span class="pre">`Nat.Coprime`</span>` `<span class="pre">`m`</span>` `<span class="pre">`n`</span> to be <span class="pre">`Nat.gcd`</span>` `<span class="pre">`m`</span>` `<span class="pre">`n`</span>` `<span class="pre">`=`</span>` `<span class="pre">`1`</span>. Using Lean’s anonymous projection notation, if <span class="pre">`s`</span> and <span class="pre">`t`</span> are expressions of type <span class="pre">`Nat`</span>, we can write <span class="pre">`s.Coprime`</span>` `<span class="pre">`t`</span> instead of <span class="pre">`Nat.Coprime`</span>` `<span class="pre">`s`</span>` `<span class="pre">`t`</span>, and similarly for <span class="pre">`Nat.gcd`</span>. As usual, Lean will often unfold the definition of <span class="pre">`Nat.Coprime`</span> automatically when necessary, but we can also do it manually by rewriting or simplifying with the identifier <span class="pre">`Nat.Coprime`</span>. The <span class="pre">`norm_num`</span> tactic is smart enough to compute concrete values.

    #print Nat.Coprime

    example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 :=
      h

    example (m n : Nat) (h : m.Coprime n) : m.gcd n = 1 := by
      rw [Nat.Coprime] at h
      exact h

    example : Nat.Coprime 12 7 := by norm_num

    example : Nat.gcd 12 8 = 4 := by norm_num

We have already encountered the <span class="pre">`gcd`</span> function in <a href="C02_Basics.html#more-on-order-and-divisibility" class="reference internal"><span class="std std-numref">Section 2.4</span></a>. There is also a version of <span class="pre">`gcd`</span> for the integers; we will return to a discussion of the relationship between different number systems below. There are even a generic <span class="pre">`gcd`</span> function and generic notions of <span class="pre">`Prime`</span> and <span class="pre">`Coprime`</span> that make sense in general classes of algebraic structures. We will come to understand how Lean manages this generality in the next chapter. In the meanwhile, in this section, we will restrict attention to the natural numbers.

We also need the notion of a prime number, <span class="pre">`Nat.Prime`</span>. The theorem <span class="pre">`Nat.prime_def_lt`</span> provides one familiar characterization, and <span class="pre">`Nat.Prime.eq_one_or_self_of_dvd`</span> provides another.

    #check Nat.prime_def_lt

    example (p : ℕ) (prime_p : Nat.Prime p) : 2 ≤ p ∧ ∀ m : ℕ, m < p → m ∣ p → m = 1 := by
      rwa [Nat.prime_def_lt] at prime_p

    #check Nat.Prime.eq_one_or_self_of_dvd

    example (p : ℕ) (prime_p : Nat.Prime p) : ∀ m : ℕ, m ∣ p → m = 1 ∨ m = p :=
      prime_p.eq_one_or_self_of_dvd

    example : Nat.Prime 17 := by norm_num

    -- commonly used
    example : Nat.Prime 2 :=
      Nat.prime_two

    example : Nat.Prime 3 :=
      Nat.prime_three

In the natural numbers, a prime number has the property that it cannot be written as a product of nontrivial factors. In a broader mathematical context, an element of a ring that has this property is said to be *irreducible*. An element of a ring is said to be *prime* if whenever it divides a product, it divides one of the factors. It is an important property of the natural numbers that in that setting the two notions coincide, giving rise to the theorem <span class="pre">`Nat.Prime.dvd_mul`</span>.

We can use this fact to establish a key property in the argument above: if the square of a number is even, then that number is even as well. Mathlib defines the predicate <span class="pre">`Even`</span> in <span class="pre">`Algebra.Group.Even`</span>, but for reasons that will become clear below, we will simply use <span class="pre">`2`</span>` `<span class="pre">`∣`</span>` `<span class="pre">`m`</span> to express that <span class="pre">`m`</span> is even.

    #check Nat.Prime.dvd_mul
    #check Nat.Prime.dvd_mul Nat.prime_two
    #check Nat.prime_two.dvd_mul

    theorem even_of_even_sqr {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m := by
      rw [pow_two, Nat.prime_two.dvd_mul] at h
      cases h <;> assumption

    example {m : ℕ} (h : 2 ∣ m ^ 2) : 2 ∣ m :=
      Nat.Prime.dvd_of_dvd_pow Nat.prime_two h

As we proceed, you will need to become proficient at finding the facts you need. Remember that if you can guess the prefix of the name and you have imported the relevant library, you can use tab completion (sometimes with <span class="pre">`ctrl-tab`</span>) to find what you are looking for. You can use <span class="pre">`ctrl-click`</span> on any identifier to jump to the file where it is defined, which enables you to browse definitions and theorems nearby. You can also use the search engine on the <a href="https://leanprover-community.github.io/" class="reference external">Lean community web pages</a>, and if all else fails, don’t hesitate to ask on <a href="https://leanprover.zulipchat.com/" class="reference external">Zulip</a>.

    example (a b c : Nat) (h : a * b = a * c) (h' : a ≠ 0) : b = c :=
      -- apply? suggests the following:
      (mul_right_inj' h').mp h

The heart of our proof of the irrationality of the square root of two is contained in the following theorem. See if you can fill out the proof sketch, using <span class="pre">`even_of_even_sqr`</span> and the theorem <span class="pre">`Nat.dvd_gcd`</span>.

    example {m n : ℕ} (coprime_mn : m.Coprime n) : m ^ 2 ≠ 2 * n ^ 2 := by
      intro sqr_eq
      have : 2 ∣ m := by
        sorry
      obtain ⟨k, meq⟩ := dvd_iff_exists_eq_mul_left.mp this
      have : 2 * (2 * k ^ 2) = 2 * n ^ 2 := by
        rw [← sqr_eq, meq]
        ring
      have : 2 * k ^ 2 = n ^ 2 :=
        sorry
      have : 2 ∣ n := by
        sorry
      have : 2 ∣ m.gcd n := by
        sorry
      have : 2 ∣ 1 := by
        sorry
      norm_num at this

In fact, with very few changes, we can replace <span class="pre">`2`</span> by an arbitrary prime. Give it a try in the next example. At the end of the proof, you’ll need to derive a contradiction from <span class="pre">`p`</span>` `<span class="pre">`∣`</span>` `<span class="pre">`1`</span>. You can use <span class="pre">`Nat.Prime.two_le`</span>, which says that any prime number is greater than or equal to two, and <span class="pre">`Nat.le_of_dvd`</span>.

    example {m n p : ℕ} (coprime_mn : m.Coprime n) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
      sorry

Let us consider another approach. Here is a quick proof that if <span class="math notranslate nohighlight">\\p\\</span> is prime, then <span class="math notranslate nohighlight">\\m^2 \ne p n^2\\</span>: if we assume <span class="math notranslate nohighlight">\\m^2 = p n^2\\</span> and consider the factorization of <span class="math notranslate nohighlight">\\m\\</span> and <span class="math notranslate nohighlight">\\n\\</span> into primes, then <span class="math notranslate nohighlight">\\p\\</span> occurs an even number of times on the left side of the equation and an odd number of times on the right, a contradiction. Note that this argument requires that <span class="math notranslate nohighlight">\\n\\</span> and hence <span class="math notranslate nohighlight">\\m\\</span> are not equal to zero. The formalization below confirms that this assumption is sufficient.

The unique factorization theorem says that any natural number other than zero can be written as the product of primes in a unique way. Mathlib contains a formal version of this, expressed in terms of a function <span class="pre">`Nat.primeFactorsList`</span>, which returns the list of prime factors of a number in nondecreasing order. The library proves that all the elements of <span class="pre">`Nat.primeFactorsList`</span>` `<span class="pre">`n`</span> are prime, that any <span class="pre">`n`</span> greater than zero is equal to the product of its factors, and that if <span class="pre">`n`</span> is equal to the product of another list of prime numbers, then that list is a permutation of <span class="pre">`Nat.primeFactorsList`</span>` `<span class="pre">`n`</span>.

    #check Nat.primeFactorsList
    #check Nat.prime_of_mem_primeFactorsList
    #check Nat.prod_primeFactorsList
    #check Nat.primeFactorsList_unique

You can browse these theorems and others nearby, even though we have not talked about list membership, products, or permutations yet. We won’t need any of that for the task at hand. We will instead use the fact that Mathlib has a function <span class="pre">`Nat.factorization`</span>, that represents the same data as a function. Specifically, <span class="pre">`Nat.factorization`</span>` `<span class="pre">`n`</span>` `<span class="pre">`p`</span>, which we can also write <span class="pre">`n.factorization`</span>` `<span class="pre">`p`</span>, returns the multiplicity of <span class="pre">`p`</span> in the prime factorization of <span class="pre">`n`</span>. We will use the following three facts.

    theorem factorization_mul' {m n : ℕ} (mnez : m ≠ 0) (nnez : n ≠ 0) (p : ℕ) :
        (m * n).factorization p = m.factorization p + n.factorization p := by
      rw [Nat.factorization_mul mnez nnez]
      rfl

    theorem factorization_pow' (n k p : ℕ) :
        (n ^ k).factorization p = k * n.factorization p := by
      rw [Nat.factorization_pow]
      rfl

    theorem Nat.Prime.factorization' {p : ℕ} (prime_p : p.Prime) :
        p.factorization p = 1 := by
      rw [prime_p.factorization]
      simp

In fact, <span class="pre">`n.factorization`</span> is defined in Lean as a function of finite support, which explains the strange notation you will see as you step through the proofs above. Don’t worry about this now. For our purposes here, we can use the three theorems above as a black box.

The next example shows that the simplifier is smart enough to replace <span class="pre">`n^2`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`0`</span> by <span class="pre">`n`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`0`</span>. The tactic <span class="pre">`simpa`</span> just calls <span class="pre">`simp`</span> followed by <span class="pre">`assumption`</span>.

See if you can use the identities above to fill in the missing parts of the proof.

    example {m n p : ℕ} (nnz : n ≠ 0) (prime_p : p.Prime) : m ^ 2 ≠ p * n ^ 2 := by
      intro sqr_eq
      have nsqr_nez : n ^ 2 ≠ 0 := by simpa
      have eq1 : Nat.factorization (m ^ 2) p = 2 * m.factorization p := by
        sorry
      have eq2 : (p * n ^ 2).factorization p = 2 * n.factorization p + 1 := by
        sorry
      have : 2 * m.factorization p % 2 = (2 * n.factorization p + 1) % 2 := by
        rw [← eq1, sqr_eq, eq2]
      rw [add_comm, Nat.add_mul_mod_self_left, Nat.mul_mod_right] at this
      norm_num at this

A nice thing about this proof is that it also generalizes. There is nothing special about <span class="pre">`2`</span>; with small changes, the proof shows that whenever we write <span class="pre">`m^k`</span>` `<span class="pre">`=`</span>` `<span class="pre">`r`</span>` `<span class="pre">`*`</span>` `<span class="pre">`n^k`</span>, the multiplicity of any prime <span class="pre">`p`</span> in <span class="pre">`r`</span> has to be a multiple of <span class="pre">`k`</span>.

To use <span class="pre">`Nat.count_factors_mul_of_pos`</span> with <span class="pre">`r`</span>` `<span class="pre">`*`</span>` `<span class="pre">`n^k`</span>, we need to know that <span class="pre">`r`</span> is positive. But when <span class="pre">`r`</span> is zero, the theorem below is trivial, and easily proved by the simplifier. So the proof is carried out in cases. The line <span class="pre">`rcases`</span>` `<span class="pre">`r`</span>` `<span class="pre">`with`</span>` `<span class="pre">`_`</span>` `<span class="pre">`|`</span>` `<span class="pre">`r`</span> replaces the goal with two versions: one in which <span class="pre">`r`</span> is replaced by <span class="pre">`0`</span>, and the other in which <span class="pre">`r`</span> is replaces by <span class="pre">`r`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1`</span>. In the second case, we can use the theorem <span class="pre">`r.succ_ne_zero`</span>, which establishes <span class="pre">`r`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`0`</span> (<span class="pre">`succ`</span> stands for successor).

Notice also that the line that begins <span class="pre">`have`</span>` `<span class="pre">`:`</span>` `<span class="pre">`npow_nz`</span> provides a short proof-term proof of <span class="pre">`n^k`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`0`</span>. To understand how it works, try replacing it with a tactic proof, and then think about how the tactics describe the proof term.

See if you can fill in the missing parts of the proof below. At the very end, you can use <span class="pre">`Nat.dvd_sub'`</span> and <span class="pre">`Nat.dvd_mul_right`</span> to finish it off.

Note that this example does not assume that <span class="pre">`p`</span> is prime, but the conclusion is trivial when <span class="pre">`p`</span> is not prime since <span class="pre">`r.factorization`</span>` `<span class="pre">`p`</span> is then zero by definition, and the proof works in all cases anyway.

    example {m n k r : ℕ} (nnz : n ≠ 0) (pow_eq : m ^ k = r * n ^ k) {p : ℕ} :
        k ∣ r.factorization p := by
      rcases r with _ | r
      · simp
      have npow_nz : n ^ k ≠ 0 := fun npowz ↦ nnz (pow_eq_zero npowz)
      have eq1 : (m ^ k).factorization p = k * m.factorization p := by
        sorry
      have eq2 : ((r + 1) * n ^ k).factorization p =
          k * n.factorization p + (r + 1).factorization p := by
        sorry
      have : r.succ.factorization p = k * m.factorization p - k * n.factorization p := by
        rw [← eq1, pow_eq, eq2, add_comm, Nat.add_sub_cancel]
      rw [this]
      sorry

There are a number of ways in which we might want to improve on these results. To start with, a proof that the square root of two is irrational should say something about the square root of two, which can be understood as an element of the real or complex numbers. And stating that it is irrational should say something about the rational numbers, namely, that no rational number is equal to it. Moreover, we should extend the theorems in this section to the integers. Although it is mathematically obvious that if we could write the square root of two as a quotient of two integers then we could write it as a quotient of two natural numbers, proving this formally requires some effort.

In Mathlib, the natural numbers, the integers, the rationals, the reals, and the complex numbers are represented by separate data types. Restricting attention to the separate domains is often helpful: we will see that it is easy to do induction on the natural numbers, and it is easiest to reason about divisibility of integers when the real numbers are not part of the picture. But having to mediate between the different domains is a headache, one we will have to contend with. We will return to this issue later in this chapter.

We should also expect to be able to strengthen the conclusion of the last theorem to say that the number <span class="pre">`r`</span> is a <span class="pre">`k`</span>-th power, since its <span class="pre">`k`</span>-th root is just the product of each prime dividing <span class="pre">`r`</span> raised to its multiplicity in <span class="pre">`r`</span> divided by <span class="pre">`k`</span>. To be able to do that we will need better means for reasoning about products and sums over a finite set, which is also a topic we will return to.

In fact, the results in this section are all established in much greater generality in Mathlib, in <span class="pre">`Data.Real.Irrational`</span>. The notion of <span class="pre">`multiplicity`</span> is defined for an arbitrary commutative monoid, and that it takes values in the extended natural numbers <span class="pre">`enat`</span>, which adds the value infinity to the natural numbers. In the next chapter, we will begin to develop the means to appreciate the way that Lean supports this sort of generality.

<span id="section-induction-and-recursion"></span>

## <span class="section-number">5.2. </span>Induction and Recursion<a href="#induction-and-recursion" class="headerlink" title="Link to this heading"></a>

The set of natural numbers <span class="math notranslate nohighlight">\\\mathbb{N} = \\ 0, 1, 2, \ldots \\\\</span> is not only fundamentally important in its own right, but also a plays a central role in the construction of new mathematical objects. Lean’s foundation allows us to declare *inductive types*, which are types generated inductively by a given list of *constructors*. In Lean, the natural numbers are declared as follows.

    inductive Nat where
      | zero : Nat
      | succ (n : Nat) : Nat

You can find this in the library by writing <span class="pre">`#check`</span>` `<span class="pre">`Nat`</span> and then using <span class="pre">`ctrl-click`</span> on the identifier <span class="pre">`Nat`</span>. The command specifies that <span class="pre">`Nat`</span> is the datatype generated freely and inductively by the two constructors <span class="pre">`zero`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Nat`</span> and <span class="pre">`succ`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Nat`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Nat`</span>. Of course, the library introduces notation <span class="pre">`ℕ`</span> and <span class="pre">`0`</span> for <span class="pre">`nat`</span> and <span class="pre">`zero`</span> respectively. (Numerals are translated to binary representations, but we don’t have to worry about the details of that now.)

What “freely” means for the working mathematician is that the type <span class="pre">`Nat`</span> has an element <span class="pre">`zero`</span> and an injective successor function <span class="pre">`succ`</span> whose image does not include <span class="pre">`zero`</span>.

    example (n : Nat) : n.succ ≠ Nat.zero :=
      Nat.succ_ne_zero n

    example (m n : Nat) (h : m.succ = n.succ) : m = n :=
      Nat.succ.inj h

What the word “inductively” means for the working mathematician is that the natural numbers comes with a principle of proof by induction and a principle of definition by recursion. This section will show you how to use these.

Here is an example of a recursive definition of the factorial function.

    def fac : ℕ → ℕ
      | 0 => 1
      | n + 1 => (n + 1) * fac n

The syntax takes some getting used to. Notice that there is no <span class="pre">`:=`</span> on the first line. The next two lines provide the base case and inductive step for a recursive definition. These equations hold definitionally, but they can also be used manually by giving the name <span class="pre">`fac`</span> to <span class="pre">`simp`</span> or <span class="pre">`rw`</span>.

    example : fac 0 = 1 :=
      rfl

    example : fac 0 = 1 := by
      rw [fac]

    example : fac 0 = 1 := by
      simp [fac]

    example (n : ℕ) : fac (n + 1) = (n + 1) * fac n :=
      rfl

    example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
      rw [fac]

    example (n : ℕ) : fac (n + 1) = (n + 1) * fac n := by
      simp [fac]

The factorial function is actually already defined in Mathlib as <span class="pre">`Nat.factorial`</span>. Once again, you can jump to it by typing <span class="pre">`#check`</span>` `<span class="pre">`Nat.factorial`</span> and using <span class="pre">`ctrl-click.`</span> For illustrative purposes, we will continue using <span class="pre">`fac`</span> in the examples. The annotation <span class="pre">`@[simp]`</span> before the definition of <span class="pre">`Nat.factorial`</span> specifies that the defining equation should be added to the database of identities that the simplifier uses by default.

The principle of induction says that we can prove a general statement about the natural numbers by proving that the statement holds of 0 and that whenever it holds of a natural number <span class="math notranslate nohighlight">\\n\\</span>, it also holds of <span class="math notranslate nohighlight">\\n + 1\\</span>. The line <span class="pre">`induction'`</span>` `<span class="pre">`n`</span>` `<span class="pre">`with`</span>` `<span class="pre">`n`</span>` `<span class="pre">`ih`</span> in the proof below therefore results in two goals: in the first we need to prove <span class="pre">`0`</span>` `<span class="pre">`<`</span>` `<span class="pre">`fac`</span>` `<span class="pre">`0`</span>, and in the second we have the added assumption <span class="pre">`ih`</span>` `<span class="pre">`:`</span>` `<span class="pre">`0`</span>` `<span class="pre">`<`</span>` `<span class="pre">`fac`</span>` `<span class="pre">`n`</span> and a required to prove <span class="pre">`0`</span>` `<span class="pre">`<`</span>` `<span class="pre">`fac`</span>` `<span class="pre">`(n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1)`</span>. The phrase <span class="pre">`with`</span>` `<span class="pre">`n`</span>` `<span class="pre">`ih`</span> serves to name the variable and the assumption for the inductive hypothesis, and you can choose whatever names you want for them.

    theorem fac_pos (n : ℕ) : 0 < fac n := by
      induction' n with n ih
      · rw [fac]
        exact zero_lt_one
      rw [fac]
      exact mul_pos n.succ_pos ih

The <span class="pre">`induction'`</span> tactic is smart enough to include hypotheses that depend on the induction variable as part of the induction hypothesis. Step through the next example to see what is going on.

    theorem dvd_fac {i n : ℕ} (ipos : 0 < i) (ile : i ≤ n) : i ∣ fac n := by
      induction' n with n ih
      · exact absurd ipos (not_lt_of_ge ile)
      rw [fac]
      rcases Nat.of_le_succ ile with h | h
      · apply dvd_mul_of_dvd_right (ih h)
      rw [h]
      apply dvd_mul_right

The following example provides a crude lower bound for the factorial function. It turns out to be easier to start with a proof by cases, so that the remainder of the proof starts with the case <span class="math notranslate nohighlight">\\n = 1\\</span>. See if you can complete the argument with a proof by induction using <span class="pre">`pow_succ`</span> or <span class="pre">`pow_succ'`</span>.

    theorem pow_two_le_fac (n : ℕ) : 2 ^ (n - 1) ≤ fac n := by
      rcases n with _ | n
      · simp [fac]
      sorry

Induction is often used to prove identities involving finite sums and products. Mathlib defines the expressions <span class="pre">`Finset.sum`</span>` `<span class="pre">`s`</span>` `<span class="pre">`f`</span> where <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Finset`</span>` `<span class="pre">`α`</span> is a finite set of elements of the type <span class="pre">`α`</span> and <span class="pre">`f`</span> is a function defined on <span class="pre">`α`</span>. The codomain of <span class="pre">`f`</span> can be any type that supports a commutative, associative addition operation with a zero element. If you import <span class="pre">`Algebra.BigOperators.Ring`</span> and issue the command <span class="pre">`open`</span>` `<span class="pre">`BigOperators`</span>, you can use the more suggestive notation <span class="pre">`∑`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s,`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>. Of course, there is an analogous operation and notation for finite products.

We will talk about the <span class="pre">`Finset`</span> type and the operations it supports in the next section, and again in a later chapter. For now, we will only make use of <span class="pre">`Finset.range`</span>` `<span class="pre">`n`</span>, which is the finite set of natural numbers less than <span class="pre">`n`</span>.

    variable {α : Type*} (s : Finset ℕ) (f : ℕ → ℕ) (n : ℕ)

    #check Finset.sum s f
    #check Finset.prod s f

    open BigOperators
    open Finset

    example : s.sum f = ∑ x ∈ s, f x :=
      rfl

    example : s.prod f = ∏ x ∈ s, f x :=
      rfl

    example : (range n).sum f = ∑ x ∈ range n, f x :=
      rfl

    example : (range n).prod f = ∏ x ∈ range n, f x :=
      rfl

The facts <span class="pre">`Finset.sum_range_zero`</span> and <span class="pre">`Finset.sum_range_succ`</span> provide a recursive description of summation up to <span class="math notranslate nohighlight">\\n\\</span>, and similarly for products.

    example (f : ℕ → ℕ) : ∑ x ∈ range 0, f x = 0 :=
      Finset.sum_range_zero f

    example (f : ℕ → ℕ) (n : ℕ) : ∑ x ∈ range n.succ, f x = ∑ x ∈ range n, f x + f n :=
      Finset.sum_range_succ f n

    example (f : ℕ → ℕ) : ∏ x ∈ range 0, f x = 1 :=
      Finset.prod_range_zero f

    example (f : ℕ → ℕ) (n : ℕ) : ∏ x ∈ range n.succ, f x = (∏ x ∈ range n, f x) * f n :=
      Finset.prod_range_succ f n

The first identity in each pair holds definitionally, which is to say, you can replace the proofs by <span class="pre">`rfl`</span>.

The following expresses the factorial function that we defined as a product.

    example (n : ℕ) : fac n = ∏ i ∈ range n, (i + 1) := by
      induction' n with n ih
      · simp [fac, prod_range_zero]
      simp [fac, ih, prod_range_succ, mul_comm]

The fact that we include <span class="pre">`mul_comm`</span> as a simplification rule deserves comment. It should seem dangerous to simplify with the identity <span class="pre">`x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y`</span>` `<span class="pre">`*`</span>` `<span class="pre">`x`</span>, which would ordinarily loop indefinitely. Lean’s simplifier is smart enough to recognize that, and applies the rule only in the case where the resulting term has a smaller value in some fixed but arbitrary ordering of the terms. The following example shows that simplifying using the three rules <span class="pre">`mul_assoc`</span>, <span class="pre">`mul_comm`</span>, and <span class="pre">`mul_left_comm`</span> manages to identify products that are the same up to the placement of parentheses and ordering of variables.

    example (a b c d e f : ℕ) : a * (b * c * f * (d * e)) = d * (a * f * e) * (c * b) := by
      simp [mul_assoc, mul_comm, mul_left_comm]

Roughly, the rules work by pushing parentheses to the right and then re-ordering the expressions on both sides until they both follow the same canonical order. Simplifying with these rules, and the corresponding rules for addition, is a handy trick.

Returning to summation identities, we suggest stepping through the following proof that the sum of the natural numbers up to and including <span class="math notranslate nohighlight">\\n\\</span> is <span class="math notranslate nohighlight">\\n (n + 1) / 2\\</span>. The first step of the proof clears the denominator. This is generally useful when formalizing identities, because calculations with division generally have side conditions. (It is similarly useful to avoid using subtraction on the natural numbers when possible.)

    theorem sum_id (n : ℕ) : ∑ i ∈ range (n + 1), i = n * (n + 1) / 2 := by
      symm; apply Nat.div_eq_of_eq_mul_right (by norm_num : 0 < 2)
      induction' n with n ih
      · simp
      rw [Finset.sum_range_succ, mul_add 2, ← ih]
      ring

We encourage you to prove the analogous identity for sums of squares, and other identities you can find on the web.

    theorem sum_sqr (n : ℕ) : ∑ i ∈ range (n + 1), i ^ 2 = n * (n + 1) * (2 * n + 1) / 6 := by
      sorry

In Lean’s core library, addition and multiplication are themselves defined using recursive definitions, and their fundamental properties are established using induction. If you like thinking about foundational topics like that, you might enjoy working through proofs of the commutativity and associativity of multiplication and addition and the distributivity of multiplication over addition. You can do this on a copy of the natural numbers following the outline below. Notice that we can use the <span class="pre">`induction`</span> tactic with <span class="pre">`MyNat`</span>; Lean is smart enough to know to use the relevant induction principle (which is, of course, the same as that for <span class="pre">`Nat`</span>).

We start you off with the commutativity of addition. A good rule of thumb is that because addition and multiplication are defined by recursion on the second argument, it is generally advantageous to do proofs by induction on a variable that occurs in that position. It is a bit tricky to decide which variable to use in the proof of associativity.

It can be confusing to write things without the usual notation for zero, one, addition, and multiplication. We will learn how to define such notation later. Working in the namespace <span class="pre">`MyNat`</span> means that we can write <span class="pre">`zero`</span> and <span class="pre">`succ`</span> rather than <span class="pre">`MyNat.zero`</span> and <span class="pre">`MyNat.succ`</span>, and that these interpretations of the names take precedence over others. Outside the namespace, the full name of the <span class="pre">`add`</span> defined below, for example, is <span class="pre">`MyNat.add`</span>.

If you find that you *really* enjoy this sort of thing, try defining truncated subtraction and exponentiation and proving some of their properties as well. Remember that truncated subtraction cuts off at zero. To define that, it is useful to define a predecessor function, <span class="pre">`pred`</span>, that subtracts one from any nonzero number and fixes zero. The function <span class="pre">`pred`</span> can be defined by a simple instance of recursion.

    inductive MyNat where
      | zero : MyNat
      | succ : MyNat → MyNat

    namespace MyNat

    def add : MyNat → MyNat → MyNat
      | x, zero => x
      | x, succ y => succ (add x y)

    def mul : MyNat → MyNat → MyNat
      | x, zero => zero
      | x, succ y => add (mul x y) x

    theorem zero_add (n : MyNat) : add zero n = n := by
      induction' n with n ih
      · rfl
      rw [add, ih]

    theorem succ_add (m n : MyNat) : add (succ m) n = succ (add m n) := by
      induction' n with n ih
      · rfl
      rw [add, ih]
      rfl

    theorem add_comm (m n : MyNat) : add m n = add n m := by
      induction' n with n ih
      · rw [zero_add]
        rfl
      rw [add, succ_add, ih]

    theorem add_assoc (m n k : MyNat) : add (add m n) k = add m (add n k) := by
      sorry
    theorem mul_add (m n k : MyNat) : mul m (add n k) = add (mul m n) (mul m k) := by
      sorry
    theorem zero_mul (n : MyNat) : mul zero n = zero := by
      sorry
    theorem succ_mul (m n : MyNat) : mul (succ m) n = add (mul m n) n := by
      sorry
    theorem mul_comm (m n : MyNat) : mul m n = mul n m := by
      sorry
    end MyNat

<span id="section-infinitely-many-primes"></span>

## <span class="section-number">5.3. </span>Infinitely Many Primes<a href="#infinitely-many-primes" class="headerlink" title="Link to this heading"></a>

Let us continue our exploration of induction and recursion with another mathematical standard: a proof that there are infinitely many primes. One way to formulate this is as the statement that for every natural number <span class="math notranslate nohighlight">\\n\\</span>, there is a prime number greater than <span class="math notranslate nohighlight">\\n\\</span>. To prove this, let <span class="math notranslate nohighlight">\\p\\</span> be any prime factor of <span class="math notranslate nohighlight">\\n! + 1\\</span>. If <span class="math notranslate nohighlight">\\p\\</span> is less than or equal to <span class="math notranslate nohighlight">\\n\\</span>, it divides <span class="math notranslate nohighlight">\\n!\\</span>. Since it also divides <span class="math notranslate nohighlight">\\n! + 1\\</span>, it divides 1, a contradiction. Hence <span class="math notranslate nohighlight">\\p\\</span> is greater than <span class="math notranslate nohighlight">\\n\\</span>.

To formalize that proof, we need to show that any number greater than or equal to 2 has a prime factor. To do that, we will need to show that any natural number that is not equal to 0 or 1 is greater-than or equal to 2. And this brings us to a quirky feature of formalization: it is often trivial statements like this that are among the most annoying to formalize. Here we consider a few ways to do it.

To start with, we can use the <span class="pre">`cases`</span> tactic and the fact that the successor function respects the ordering on the natural numbers.

    theorem two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
      cases m; contradiction
      case succ m =>
        cases m; contradiction
        repeat apply Nat.succ_le_succ
        apply zero_le

Another strategy is to use the tactic <span class="pre">`interval_cases`</span>, which automatically splits the goal into cases when the variable in question is contained in an interval of natural numbers or integers. Remember that you can hover over it to see its documentation.

    example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
      by_contra h
      push_neg at h
      interval_cases m <;> contradiction

Recall that the semicolon after <span class="pre">`interval_cases`</span>` `<span class="pre">`m`</span> means that the next tactic is applied to each of the cases that it generates. Yet another option is to use the tactic <span class="pre">`decide`</span>, which tries to find a decision procedure to solve the problem. Lean knows that you can decide the truth value of a statement that begins with a bounded quantifier <span class="pre">`∀`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`<`</span>` `<span class="pre">`n`</span>` `<span class="pre">`→`</span>` `<span class="pre">`...`</span> or <span class="pre">`∃`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`<`</span>` `<span class="pre">`n`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`...`</span> by deciding each of the finitely many instances.

    example {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
      by_contra h
      push_neg at h
      revert h0 h1
      revert h m
      decide

With the theorem <span class="pre">`two_le`</span> in hand, let’s start by showing that every natural number greater than two has a prime divisor. Mathlib contains a function <span class="pre">`Nat.minFac`</span> that returns the smallest prime divisor, but for the sake of learning new parts of the library, we’ll avoid using it and prove the theorem directly.

Here, ordinary induction isn’t enough. We want to use *strong induction*, which allows us to prove that every natural number <span class="math notranslate nohighlight">\\n\\</span> has a property <span class="math notranslate nohighlight">\\P\\</span> by showing that for every number <span class="math notranslate nohighlight">\\n\\</span>, if <span class="math notranslate nohighlight">\\P\\</span> holds of all values less than <span class="math notranslate nohighlight">\\n\\</span>, it holds at <span class="math notranslate nohighlight">\\n\\</span> as well. In Lean, this principle is called <span class="pre">`Nat.strong_induction_on`</span>, and we can use the <span class="pre">`using`</span> keyword to tell the induction tactic to use it. Notice that when we do that, there is no base case; it is subsumed by the general induction step.

The argument is simply as follows. Assuming <span class="math notranslate nohighlight">\\n ≥ 2\\</span>, if <span class="math notranslate nohighlight">\\n\\</span> is prime, we’re done. If it isn’t, then by one of the characterizations of what it means to be a prime number, it has a nontrivial factor, <span class="math notranslate nohighlight">\\m\\</span>, and we can apply the inductive hypothesis to that. Step through the next proof to see how that plays out.

    theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
      by_cases np : n.Prime
      · use n, np
      induction' n using Nat.strong_induction_on with n ih
      rw [Nat.prime_def_lt] at np
      push_neg at np
      rcases np h with ⟨m, mltn, mdvdn, mne1⟩
      have : m ≠ 0 := by
        intro mz
        rw [mz, zero_dvd_iff] at mdvdn
        linarith
      have mgt2 : 2 ≤ m := two_le this mne1
      by_cases mp : m.Prime
      · use m, mp
      · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
        use p, pp
        apply pdvd.trans mdvdn

We can now prove the following formulation of our theorem. See if you can fill out the sketch. You can use <span class="pre">`Nat.factorial_pos`</span>, <span class="pre">`Nat.dvd_factorial`</span>, and <span class="pre">`Nat.dvd_sub'`</span>.

    theorem primes_infinite : ∀ n, ∃ p > n, Nat.Prime p := by
      intro n
      have : 2 ≤ Nat.factorial n + 1 := by
        sorry
      rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
      refine ⟨p, ?_, pp⟩
      show p > n
      by_contra ple
      push_neg at ple
      have : p ∣ Nat.factorial n := by
        sorry
      have : p ∣ 1 := by
        sorry
      show False
      sorry

Let’s consider a variation of the proof above, where instead of using the factorial function, we suppose that we are given by a finite set <span class="math notranslate nohighlight">\\\\ p\_1, \ldots, p\_n \\\\</span> and we consider a prime factor of <span class="math notranslate nohighlight">\\\prod\_{i = 1}^n p\_i + 1\\</span>. That prime factor has to be distinct from each <span class="math notranslate nohighlight">\\p\_i\\</span>, showing that there is no finite set that contains all the prime numbers.

Formalizing this argument requires us to reason about finite sets. In Lean, for any type <span class="pre">`α`</span>, the type <span class="pre">`Finset`</span>` `<span class="pre">`α`</span> represents finite sets of elements of type <span class="pre">`α`</span>. Reasoning about finite sets computationally requires having a procedure to test equality on <span class="pre">`α`</span>, which is why the snippet below includes the assumption <span class="pre">`[DecidableEq`</span>` `<span class="pre">`α]`</span>. For concrete data types like <span class="pre">`ℕ`</span>, <span class="pre">`ℤ`</span>, and <span class="pre">`ℚ`</span>, the assumption is satisfied automatically. When reasoning about the real numbers, it can be satisfied using classical logic and abandoning the computational interpretation.

We use the command <span class="pre">`open`</span>` `<span class="pre">`Finset`</span> to avail ourselves of shorter names for the relevant theorems. Unlike the case with sets, most equivalences involving finsets do not hold definitionally, so they need to be expanded manually using equivalences like <span class="pre">`Finset.subset_iff`</span>, <span class="pre">`Finset.mem_union`</span>, <span class="pre">`Finset.mem_inter`</span>, and <span class="pre">`Finset.mem_sdiff`</span>. The <span class="pre">`ext`</span> tactic can still be used to show that two finite sets are equal by showing that every element of one is an element of the other.

    open Finset

    section
    variable {α : Type*} [DecidableEq α] (r s t : Finset α)

    example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
      rw [subset_iff]
      intro x
      rw [mem_inter, mem_union, mem_union, mem_inter, mem_inter]
      tauto

    example : r ∩ (s ∪ t) ⊆ r ∩ s ∪ r ∩ t := by
      simp [subset_iff]
      intro x
      tauto

    example : r ∩ s ∪ r ∩ t ⊆ r ∩ (s ∪ t) := by
      simp [subset_iff]
      intro x
      tauto

    example : r ∩ s ∪ r ∩ t = r ∩ (s ∪ t) := by
      ext x
      simp
      tauto

    end

We have used a new trick: the <span class="pre">`tauto`</span> tactic (and a strengthened version, <span class="pre">`tauto!`</span>, which uses classical logic) can be used to dispense with propositional tautologies. See if you can use these methods to prove the two examples below.

    example : (r ∪ s) ∩ (r ∪ t) = r ∪ s ∩ t := by
      sorry
    example : (r \ s) \ t = r \ (s ∪ t) := by
      sorry

The theorem <span class="pre">`Finset.dvd_prod_of_mem`</span> tells us that if an <span class="pre">`n`</span> is an element of a finite set <span class="pre">`s`</span>, then <span class="pre">`n`</span> divides <span class="pre">`∏`</span>` `<span class="pre">`i`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s,`</span>` `<span class="pre">`i`</span>.

    example (s : Finset ℕ) (n : ℕ) (h : n ∈ s) : n ∣ ∏ i ∈ s, i :=
      Finset.dvd_prod_of_mem _ h

We also need to know that the converse holds in the case where <span class="pre">`n`</span> is prime and <span class="pre">`s`</span> is a set of primes. To show that, we need the following lemma, which you should be able to prove using the theorem <span class="pre">`Nat.Prime.eq_one_or_self_of_dvd`</span>.

    theorem _root_.Nat.Prime.eq_of_dvd_of_prime {p q : ℕ}
          (prime_p : Nat.Prime p) (prime_q : Nat.Prime q) (h : p ∣ q) :
        p = q := by
      sorry

We can use this lemma to show that if a prime <span class="pre">`p`</span> divides a product of a finite set of primes, then it is equal to one of them. Mathlib provides a useful principle of induction on finite sets: to show that a property holds of an arbitrary finite set <span class="pre">`s`</span>, show that it holds of the empty set, and show that it is preserved when we add a single new element <span class="pre">`a`</span>` `<span class="pre">`∉`</span>` `<span class="pre">`s`</span>. The principle is known as <span class="pre">`Finset.induction_on`</span>. When we tell the induction tactic to use it, we can also specify the names <span class="pre">`a`</span> and <span class="pre">`s`</span>, the name for the assumption <span class="pre">`a`</span>` `<span class="pre">`∉`</span>` `<span class="pre">`s`</span> in the inductive step, and the name of the inductive hypothesis. The expression <span class="pre">`Finset.insert`</span>` `<span class="pre">`a`</span>` `<span class="pre">`s`</span> denotes the union of <span class="pre">`s`</span> with the singleton <span class="pre">`a`</span>. The identities <span class="pre">`Finset.prod_empty`</span> and <span class="pre">`Finset.prod_insert`</span> then provide the relevant rewrite rules for the product. In the proof below, the first <span class="pre">`simp`</span> applies <span class="pre">`Finset.prod_empty`</span>. Step through the beginning of the proof to see the induction unfold, and then finish it off.

    theorem mem_of_dvd_prod_primes {s : Finset ℕ} {p : ℕ} (prime_p : p.Prime) :
        (∀ n ∈ s, Nat.Prime n) → (p ∣ ∏ n ∈ s, n) → p ∈ s := by
      intro h₀ h₁
      induction' s using Finset.induction_on with a s ans ih
      · simp at h₁
        linarith [prime_p.two_le]
      simp [Finset.prod_insert ans, prime_p.dvd_mul] at h₀ h₁
      rw [mem_insert]
      sorry

We need one last property of finite sets. Given an element <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Set`</span>` `<span class="pre">`α`</span> and a predicate <span class="pre">`P`</span> on <span class="pre">`α`</span>, in <a href="C04_Sets_and_Functions.html#sets-and-functions" class="reference internal"><span class="std std-numref">Chapter 4</span></a> we wrote <span class="pre">`{`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`|`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span>` `<span class="pre">`}`</span> for the set of elements of <span class="pre">`s`</span> that satisfy <span class="pre">`P`</span>. Given <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Finset`</span>` `<span class="pre">`α`</span>, the analogous notion is written <span class="pre">`s.filter`</span>` `<span class="pre">`P`</span>.

    example (s : Finset ℕ) (x : ℕ) : x ∈ s.filter Nat.Prime ↔ x ∈ s ∧ x.Prime :=
      mem_filter

We now prove an alternative formulation of the statement that there are infinitely many primes, namely, that given any <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Finset`</span>` `<span class="pre">`ℕ`</span>, there is a prime <span class="pre">`p`</span> that is not an element of <span class="pre">`s`</span>. Aiming for a contradiction, we assume that all the primes are in <span class="pre">`s`</span>, and then cut down to a set <span class="pre">`s'`</span> that contains all and only the primes. Taking the product of that set, adding one, and finding a prime factor of the result leads to the contradiction we are looking for. See if you can complete the sketch below. You can use <span class="pre">`Finset.prod_pos`</span> in the proof of the first <span class="pre">`have`</span>.

    theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
      intro s
      by_contra h
      push_neg at h
      set s' := s.filter Nat.Prime with s'_def
      have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
        intro n
        simp [s'_def]
        apply h
      have : 2 ≤ (∏ i ∈ s', i) + 1 := by
        sorry
      rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
      have : p ∣ ∏ i ∈ s', i := by
        sorry
      have : p ∣ 1 := by
        convert Nat.dvd_sub pdvd this
        simp
      show False
      sorry

We have thus seen two ways of saying that there are infinitely many primes: saying that they are not bounded by any <span class="pre">`n`</span>, and saying that they are not contained in any finite set <span class="pre">`s`</span>. The two proofs below show that these formulations are equivalent. In the second, in order to form <span class="pre">`s.filter`</span>` `<span class="pre">`Q`</span>, we have to assume that there is a procedure for deciding whether or not <span class="pre">`Q`</span> holds. Lean knows that there is a procedure for <span class="pre">`Nat.Prime`</span>. In general, if we use classical logic by writing <span class="pre">`open`</span>` `<span class="pre">`Classical`</span>, we can dispense with the assumption.

In Mathlib, <span class="pre">`Finset.sup`</span>` `<span class="pre">`s`</span>` `<span class="pre">`f`</span> denotes the supremum of the values of <span class="pre">`f`</span>` `<span class="pre">`x`</span> as <span class="pre">`x`</span> ranges over <span class="pre">`s`</span>, returning <span class="pre">`0`</span> in the case where <span class="pre">`s`</span> is empty and the codomain of <span class="pre">`f`</span> is <span class="pre">`ℕ`</span>. In the first proof, we use <span class="pre">`s.sup`</span>` `<span class="pre">`id`</span>, where <span class="pre">`id`</span> is the identity function, to refer to the maximum value in <span class="pre">`s`</span>.

    theorem bounded_of_ex_finset (Q : ℕ → Prop) :
        (∃ s : Finset ℕ, ∀ k, Q k → k ∈ s) → ∃ n, ∀ k, Q k → k < n := by
      rintro ⟨s, hs⟩
      use s.sup id + 1
      intro k Qk
      apply Nat.lt_succ_of_le
      show id k ≤ s.sup id
      apply le_sup (hs k Qk)

    theorem ex_finset_of_bounded (Q : ℕ → Prop) [DecidablePred Q] :
        (∃ n, ∀ k, Q k → k ≤ n) → ∃ s : Finset ℕ, ∀ k, Q k ↔ k ∈ s := by
      rintro ⟨n, hn⟩
      use (range (n + 1)).filter Q
      intro k
      simp [Nat.lt_succ_iff]
      exact hn k

A small variation on our second proof that there are infinitely many primes shows that there are infinitely many primes congruent to 3 modulo 4. The argument goes as follows. First, notice that if the product of two numbers <span class="math notranslate nohighlight">\\m\\</span> and <span class="math notranslate nohighlight">\\n\\</span> is equal to 3 modulo 4, then one of the two numbers is congruent to 3 modulo 4. After all, both have to be odd, and if they are both congruent to 1 modulo 4, so is their product. We can use this observation to show that if some number greater than 2 is congruent to 3 modulo 4, then that number has a prime divisor that is also congruent to 3 modulo 4.

Now suppose there are only finitely many prime numbers congruent to 3 modulo 4, say, <span class="math notranslate nohighlight">\\p\_1, \ldots, p\_k\\</span>. Without loss of generality, we can assume that <span class="math notranslate nohighlight">\\p\_1 = 3\\</span>. Consider the product <span class="math notranslate nohighlight">\\4 \prod\_{i = 2}^k p\_i + 3\\</span>. It is easy to see that this is congruent to 3 modulo 4, so it has a prime factor <span class="math notranslate nohighlight">\\p\\</span> congruent to 3 modulo 4. It can’t be the case that <span class="math notranslate nohighlight">\\p = 3\\</span>; since <span class="math notranslate nohighlight">\\p\\</span> divides <span class="math notranslate nohighlight">\\4 \prod\_{i = 2}^k p\_i + 3\\</span>, if <span class="math notranslate nohighlight">\\p\\</span> were equal to 3 then it would also divide <span class="math notranslate nohighlight">\\\prod\_{i = 2}^k p\_i\\</span>, which implies that <span class="math notranslate nohighlight">\\p\\</span> is equal to one of the <span class="math notranslate nohighlight">\\p\_i\\</span> for <span class="math notranslate nohighlight">\\i = 2, \ldots, k\\</span>; and we have excluded 3 from this list. So <span class="math notranslate nohighlight">\\p\\</span> has to be one of the other elements <span class="math notranslate nohighlight">\\p\_i\\</span>. But in that case, <span class="math notranslate nohighlight">\\p\\</span> divides <span class="math notranslate nohighlight">\\4 \prod\_{i = 2}^k p\_i\\</span> and hence 3, which contradicts the fact that it is not 3.

In Lean, the notation <span class="pre">`n`</span>` `<span class="pre">`%`</span>` `<span class="pre">`m`</span>, read “<span class="pre">`n`</span> modulo <span class="pre">`m`</span>,” denotes the remainder of the division of <span class="pre">`n`</span> by <span class="pre">`m`</span>.

    example : 27 % 4 = 3 := by norm_num

We can then render the statement “<span class="pre">`n`</span> is congruent to 3 modulo 4” as <span class="pre">`n`</span>` `<span class="pre">`%`</span>` `<span class="pre">`4`</span>` `<span class="pre">`=`</span>` `<span class="pre">`3`</span>. The following example and theorems sum up the facts about this function that we will need to use below. The first named theorem is another illustration of reasoning by a small number of cases. In the second named theorem, remember that the semicolon means that the subsequent tactic block is applied to all the goals created by the preceding tactic.

    example (n : ℕ) : (4 * n + 3) % 4 = 3 := by
      rw [add_comm, Nat.add_mul_mod_self_left]

    theorem mod_4_eq_3_or_mod_4_eq_3 {m n : ℕ} (h : m * n % 4 = 3) : m % 4 = 3 ∨ n % 4 = 3 := by
      revert h
      rw [Nat.mul_mod]
      have : m % 4 < 4 := Nat.mod_lt m (by norm_num)
      interval_cases m % 4 <;> simp [-Nat.mul_mod_mod]
      have : n % 4 < 4 := Nat.mod_lt n (by norm_num)
      interval_cases n % 4 <;> simp

    theorem two_le_of_mod_4_eq_3 {n : ℕ} (h : n % 4 = 3) : 2 ≤ n := by
      apply two_le <;>
        · intro neq
          rw [neq] at h
          norm_num at h

We will also need the following fact, which says that if <span class="pre">`m`</span> is a nontrivial divisor of <span class="pre">`n`</span>, then so is <span class="pre">`n`</span>` `<span class="pre">`/`</span>` `<span class="pre">`m`</span>. See if you can complete the proof using <span class="pre">`Nat.div_dvd_of_dvd`</span> and <span class="pre">`Nat.div_lt_self`</span>.

    theorem aux {m n : ℕ} (h₀ : m ∣ n) (h₁ : 2 ≤ m) (h₂ : m < n) : n / m ∣ n ∧ n / m < n := by
      sorry

Now put all the pieces together to prove that any number congruent to 3 modulo 4 has a prime divisor with that same property.

    theorem exists_prime_factor_mod_4_eq_3 {n : Nat} (h : n % 4 = 3) :
        ∃ p : Nat, p.Prime ∧ p ∣ n ∧ p % 4 = 3 := by
      by_cases np : n.Prime
      · use n
      induction' n using Nat.strong_induction_on with n ih
      rw [Nat.prime_def_lt] at np
      push_neg at np
      rcases np (two_le_of_mod_4_eq_3 h) with ⟨m, mltn, mdvdn, mne1⟩
      have mge2 : 2 ≤ m := by
        apply two_le _ mne1
        intro mz
        rw [mz, zero_dvd_iff] at mdvdn
        linarith
      have neq : m * (n / m) = n := Nat.mul_div_cancel' mdvdn
      have : m % 4 = 3 ∨ n / m % 4 = 3 := by
        apply mod_4_eq_3_or_mod_4_eq_3
        rw [neq, h]
      rcases this with h1 | h1
      . sorry
      . sorry

We are in the home stretch. Given a set <span class="pre">`s`</span> of prime numbers, we need to talk about the result of removing 3 from that set, if it is present. The function <span class="pre">`Finset.erase`</span> handles that.

    example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
      rwa [mem_erase] at h

    example (m n : ℕ) (s : Finset ℕ) (h : m ∈ erase s n) : m ≠ n ∧ m ∈ s := by
      simp at h
      assumption

We are now ready to prove that there are infinitely many primes congruent to 3 modulo 4. Fill in the missing parts below. Our solution uses <span class="pre">`Nat.dvd_add_iff_left`</span> and <span class="pre">`Nat.dvd_sub'`</span> along the way.

    theorem primes_mod_4_eq_3_infinite : ∀ n, ∃ p > n, Nat.Prime p ∧ p % 4 = 3 := by
      by_contra h
      push_neg at h
      rcases h with ⟨n, hn⟩
      have : ∃ s : Finset Nat, ∀ p : ℕ, p.Prime ∧ p % 4 = 3 ↔ p ∈ s := by
        apply ex_finset_of_bounded
        use n
        contrapose! hn
        rcases hn with ⟨p, ⟨pp, p4⟩, pltn⟩
        exact ⟨p, pltn, pp, p4⟩
      rcases this with ⟨s, hs⟩
      have h₁ : ((4 * ∏ i ∈ erase s 3, i) + 3) % 4 = 3 := by
        sorry
      rcases exists_prime_factor_mod_4_eq_3 h₁ with ⟨p, pp, pdvd, p4eq⟩
      have ps : p ∈ s := by
        sorry
      have pne3 : p ≠ 3 := by
        sorry
      have : p ∣ 4 * ∏ i ∈ erase s 3, i := by
        sorry
      have : p ∣ 3 := by
        sorry
      have : p = 3 := by
        sorry
      contradiction

If you managed to complete the proof, congratulations! This has been a serious feat of formalization.

<span id="id1"></span>

## <span class="section-number">5.4. </span>More Induction<a href="#more-induction" class="headerlink" title="Link to this heading"></a>

In <a href="#section-induction-and-recursion" class="reference internal"><span class="std std-numref">Section 5.2</span></a>, we saw how to define the factorial function by recursion on the natural numbers.

    def fac : ℕ → ℕ
      | 0 => 1
      | n + 1 => (n + 1) * fac n

We also saw how to prove theorems using the <span class="pre">`induction'`</span> tactic.

    theorem fac_pos (n : ℕ) : 0 < fac n := by
      induction' n with n ih
      · rw [fac]
        exact zero_lt_one
      rw [fac]
      exact mul_pos n.succ_pos ih

The <span class="pre">`induction`</span> tactic (without the prime tick mark) allows for more structured syntax.

    example (n : ℕ) : 0 < fac n := by
      induction n
      case zero =>
        rw [fac]
        exact zero_lt_one
      case succ n ih =>
        rw [fac]
        exact mul_pos n.succ_pos ih

    example (n : ℕ) : 0 < fac n := by
      induction n with
      | zero =>
        rw [fac]
        exact zero_lt_one
      | succ n ih =>
        rw [fac]
        exact mul_pos n.succ_pos ih

As usual, you can hover over the <span class="pre">`induction`</span> keyword to read the documentation. The names of the cases, <span class="pre">`zero`</span> and <span class="pre">`succ`</span>, are taken from the definition of the type ℕ. Notice that the <span class="pre">`succ`</span> case allows you to choose whatever names you want for the induction variable and the inductive hypothesis, here <span class="pre">`n`</span> and <span class="pre">`ih`</span>. You can even prove a theorem with the same notation used to define a recursive function.

    theorem fac_pos' : ∀ n, 0 < fac n
      | 0 => by
        rw [fac]
        exact zero_lt_one
      | n + 1 => by
        rw [fac]
        exact mul_pos n.succ_pos (fac_pos' n)

Notice also the absence of the <span class="pre">`:=`</span>, the <span class="pre">`∀`</span>` `<span class="pre">`n`</span> after the colon, the <span class="pre">`by`</span> keyword in each case, and the inductive appeal to <span class="pre">`fac_pos'`</span>` `<span class="pre">`n`</span>. It is as though the theorem is a recursive function of <span class="pre">`n`</span> and in the inductive step we make a recursive call.

This style of definition is remarkably flexible. Lean’s designers have built in elaborate means of defining recursive functions, and these extend to doing proofs by induction. For example, we can define the Fibonacci function with multiple base cases.

    @[simp] def fib : ℕ → ℕ
      | 0 => 0
      | 1 => 1
      | n + 2 => fib n + fib (n + 1)

The <span class="pre">`@[simp]`</span> annotation means that the simplifier will use the defining equations. You can also apply them by writing <span class="pre">`rw`</span>` `<span class="pre">`[fib]`</span>. Below it will be helpful to give a name to the <span class="pre">`n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`2`</span> case.

    theorem fib_add_two (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := rfl

    example (n : ℕ) : fib (n + 2) = fib n + fib (n + 1) := by rw [fib]

Using Lean’s notation for recursive functions, you can carry out proofs by induction on the natural numbers that mirror the recursive definition of <span class="pre">`fib`</span>. The following example provides an explicit formula for the nth Fibonacci number in terms of the golden mean, <span class="pre">`φ`</span>, and its conjugate, <span class="pre">`φ'`</span>. We have to tell Lean that we don’t expect our definitions to generate code because the arithmetic operations on the real numbers are not computable.

    noncomputable section

    def phi  : ℝ := (1 + √5) / 2
    def phi' : ℝ := (1 - √5) / 2

    theorem phi_sq : phi^2 = phi + 1 := by
      field_simp [phi, add_sq]; ring

    theorem phi'_sq : phi'^2 = phi' + 1 := by
      field_simp [phi', sub_sq]; ring

    theorem fib_eq : ∀ n, fib n = (phi^n - phi'^n) / √5
      | 0   => by simp
      | 1   => by field_simp [phi, phi']
      | n+2 => by field_simp [fib_eq, pow_add, phi_sq, phi'_sq]; ring

    end

Induction proofs involving the Fibonacci function do not have to be of that form. Below we reproduce the <span class="pre">`Mathlib`</span> proof that consecutive Fibonacci numbers are coprime.

    theorem fib_coprime_fib_succ (n : ℕ) : Nat.Coprime (fib n) (fib (n + 1)) := by
      induction n with
      | zero => simp
      | succ n ih =>
        simp only [fib, Nat.coprime_add_self_right]
        exact ih.symm

Using Lean’s computational interpretation, we can evaluate the Fibonacci numbers.

    #eval fib 6
    #eval List.range 20 |>.map fib

The straightforward implementation of <span class="pre">`fib`</span> is computationally inefficient. In fact, it runs in time exponential in its argument. (You should think about why.) In Lean, we can implement the following tail-recursive version, whose running time is linear in <span class="pre">`n`</span>, and prove that it computes the same function.

    def fib' (n : Nat) : Nat :=
      aux n 0 1
    where aux
      | 0,   x, _ => x
      | n+1, x, y => aux n y (x + y)

    theorem fib'.aux_eq (m n : ℕ) : fib'.aux n (fib m) (fib (m + 1)) = fib (n + m) := by
      induction n generalizing m with
      | zero => simp [fib'.aux]
      | succ n ih => rw [fib'.aux, ←fib_add_two, ih, add_assoc, add_comm 1]

    theorem fib'_eq_fib : fib' = fib := by
      ext n
      erw [fib', fib'.aux_eq 0 n]; rfl

    #eval fib' 10000

Notice the <span class="pre">`generalizing`</span> keyword in the proof of <span class="pre">`fib'.aux_eq`</span>. It serves to insert a <span class="pre">`∀`</span>` `<span class="pre">`m`</span> in front of the inductive hypothesis, so that in the induction step, <span class="pre">`m`</span> can take a different value. You can step through the proof and check that in this case, the quantifier needs to be instantiated to <span class="pre">`m`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1`</span> in the inductive step.

Notice also the use of <span class="pre">`erw`</span> (for “extended rewrite”) instead of <span class="pre">`rw`</span>. This is used because to rewrite the goal <span class="pre">`fib'.aux_eq`</span>, <span class="pre">`fib`</span>` `<span class="pre">`0`</span> and <span class="pre">`fib`</span>` `<span class="pre">`1`</span> have to be reduced to <span class="pre">`0`</span> and <span class="pre">`1`</span>, respectively. The tactic <span class="pre">`erw`</span> is more aggressive than <span class="pre">`rw`</span> in unfolding definitions to match parameters. This isn’t always a good idea; it can waste a lot of time in some cases, so use <span class="pre">`erw`</span> sparingly.

Here is another example of the <span class="pre">`generalizing`</span> keyword in use, in the proof of another identity that is found in <span class="pre">`Mathlib`</span>. An informal proof of the identity can be found <a href="https://proofwiki.org/wiki/Fibonacci_Number_in_terms_of_Smaller_Fibonacci_Numbers" class="reference external">here</a>. We provide two variants of the formal proof.

    theorem fib_add (m n : ℕ) : fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1) := by
      induction n generalizing m with
      | zero => simp
      | succ n ih =>
        specialize ih (m + 1)
        rw [add_assoc m 1 n, add_comm 1 n] at ih
        simp only [fib_add_two, Nat.succ_eq_add_one, ih]
        ring

    theorem fib_add' : ∀ m n, fib (m + n + 1) = fib m * fib n + fib (m + 1) * fib (n + 1)
      | _, 0     => by simp
      | m, n + 1 => by
        have := fib_add' (m + 1) n
        rw [add_assoc m 1 n, add_comm 1 n] at this
        simp only [fib_add_two, Nat.succ_eq_add_one, this]
        ring

As an exercise, use <span class="pre">`fib_add`</span> to prove the following.

    example (n : ℕ): (fib n) ^ 2 + (fib (n + 1)) ^ 2 = fib (2 * n + 1) := by sorry

Lean’s mechanisms for defining recursive functions are flexible enough to allow arbitrary recursive calls, as long the complexity of the arguments decrease according to some well-founded measure. In the next example, we show that every natural number <span class="pre">`n`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`1`</span> has a prime divisor, using the fact that if <span class="pre">`n`</span> is nonzero and not prime, it has a smaller divisor. (You can check that Mathlib has a theorem of the same name in the <span class="pre">`Nat`</span> namespace, though it has a different proof than the one we give here.)

    #check (@Nat.not_prime_iff_exists_dvd_lt :
      ∀ {n : ℕ}, 2 ≤ n → (¬Nat.Prime n ↔ ∃ m, m ∣ n ∧ 2 ≤ m ∧ m < n))

    theorem ne_one_iff_exists_prime_dvd : ∀ {n}, n ≠ 1 ↔ ∃ p : ℕ, p.Prime ∧ p ∣ n
      | 0 => by simpa using Exists.intro 2 Nat.prime_two
      | 1 => by simp [Nat.not_prime_one]
      | n + 2 => by
        have hn : n+2 ≠ 1 := by omega
        simp only [Ne, not_false_iff, true_iff, hn]
        by_cases h : Nat.Prime (n + 2)
        · use n+2, h
        · have : 2 ≤ n + 2 := by omega
          rw [Nat.not_prime_iff_exists_dvd_lt this] at h
          rcases h with ⟨m, mdvdn, mge2, -⟩
          have : m ≠ 1 := by omega
          rw [ne_one_iff_exists_prime_dvd] at this
          rcases this with ⟨p, primep, pdvdm⟩
          use p, primep
          exact pdvdm.trans mdvdn

The line <span class="pre">`rw`</span>` `<span class="pre">`[ne_one_iff_exists_prime_dvd]`</span>` `<span class="pre">`at`</span>` `<span class="pre">`this`</span> is like a magic trick: we are using the very theorem we are proving in its own proof. What makes it work is that the inductive call is instantiated at <span class="pre">`m`</span>, the current case is <span class="pre">`n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`2`</span>, and the context has <span class="pre">`m`</span>` `<span class="pre">`<`</span>` `<span class="pre">`n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`2`</span>. Lean can find the hypothesis and use it to show that the induction is well-founded. Lean is pretty good at figuring out what is decreasing; in this case, the choice of <span class="pre">`n`</span> in the statement of the theorem and the less-than relation is obvious. In more complicated cases, Lean provides mechanisms to provide this information explicitly. See the section on <a href="https://lean-lang.org/doc/reference/latest//Definitions/Recursive-Definitions/#well-founded-recursion" class="reference external">well-founded recursion</a> in the Lean Reference Manual.

Sometimes, in a proof, you need to split on cases depending on whether a natural number <span class="pre">`n`</span> is zero or a successor, without requiring an inductive hypothesis in the successor case. For that, you can use the <span class="pre">`cases`</span> and <span class="pre">`rcases`</span> tactics.

    theorem zero_lt_of_mul_eq_one (m n : ℕ) : n * m = 1 → 0 < n ∧ 0 < m := by
      cases n <;> cases m <;> simp

    example (m n : ℕ) : n*m = 1 → 0 < n ∧ 0 < m := by
      rcases m with (_ | m); simp
      rcases n with (_ | n) <;> simp

This is a useful trick. Often you have a theorem about a natural number <span class="pre">`n`</span> for which the zero case is easy. If you case on <span class="pre">`n`</span> and take care of the zero case quickly, you are left with the original goal with <span class="pre">`n`</span> replaced by <span class="pre">`n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1`</span>.
