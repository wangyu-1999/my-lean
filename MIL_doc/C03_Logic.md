<span id="id1"></span>

# <span class="section-number">3. </span>Logic<a href="#logic" class="headerlink" title="Link to this heading"></a>

In the last chapter, we dealt with equations, inequalities, and basic mathematical statements like “<span class="math notranslate nohighlight">\\x\\</span> divides <span class="math notranslate nohighlight">\\y\\</span>.” Complex mathematical statements are built up from simple ones like these using logical terms like “and,” “or,” “not,” and “if … then,” “every,” and “some.” In this chapter, we show you how to work with statements that are built up in this way.

<span id="id2"></span>

## <span class="section-number">3.1. </span>Implication and the Universal Quantifier<a href="#implication-and-the-universal-quantifier" class="headerlink" title="Link to this heading"></a>

Consider the statement after the <span class="pre">`#check`</span>:

    #check ∀ x : ℝ, 0 ≤ x → |x| = x

In words, we would say “for every real number <span class="pre">`x`</span>, if <span class="pre">`0`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`x`</span> then the absolute value of <span class="pre">`x`</span> equals <span class="pre">`x`</span>”. We can also have more complicated statements like:

    #check ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε

In words, we would say “for every <span class="pre">`x`</span>, <span class="pre">`y`</span>, and <span class="pre">`ε`</span>, if <span class="pre">`0`</span>` `<span class="pre">`<`</span>` `<span class="pre">`ε`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`1`</span>, the absolute value of <span class="pre">`x`</span> is less than <span class="pre">`ε`</span>, and the absolute value of <span class="pre">`y`</span> is less than <span class="pre">`ε`</span>, then the absolute value of <span class="pre">`x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span> is less than <span class="pre">`ε`</span>.” In Lean, in a sequence of implications there are implicit parentheses grouped to the right. So the expression above means “if <span class="pre">`0`</span>` `<span class="pre">`<`</span>` `<span class="pre">`ε`</span> then if <span class="pre">`ε`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`1`</span> then if <span class="pre">`|x|`</span>` `<span class="pre">`<`</span>` `<span class="pre">`ε`</span> …” As a result, the expression says that all the assumptions together imply the conclusion.

You have already seen that even though the universal quantifier in this statement ranges over objects and the implication arrows introduce hypotheses, Lean treats the two in very similar ways. In particular, if you have proved a theorem of that form, you can apply it to objects and hypotheses in the same way. We will use as an example the following statement that we will help you to prove a bit later:

    theorem my_lemma : ∀ x y ε : ℝ, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
      sorry

    section
    variable (a b δ : ℝ)
    variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
    variable (ha : |a| < δ) (hb : |b| < δ)

    #check my_lemma a b δ
    #check my_lemma a b δ h₀ h₁
    #check my_lemma a b δ h₀ h₁ ha hb

    end

You have also already seen that it is common in Lean to use curly brackets to make quantified variables implicit when they can be inferred from subsequent hypotheses. When we do that, we can just apply a lemma to the hypotheses without mentioning the objects.

    theorem my_lemma2 : ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε :=
      sorry

    section
    variable (a b δ : ℝ)
    variable (h₀ : 0 < δ) (h₁ : δ ≤ 1)
    variable (ha : |a| < δ) (hb : |b| < δ)

    #check my_lemma2 h₀ h₁ ha hb

    end

At this stage, you also know that if you use the <span class="pre">`apply`</span> tactic to apply <span class="pre">`my_lemma`</span> to a goal of the form <span class="pre">`|a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`b|`</span>` `<span class="pre">`<`</span>` `<span class="pre">`δ`</span>, you are left with new goals that require you to prove each of the hypotheses.

To prove a statement like this, use the <span class="pre">`intro`</span> tactic. Take a look at what it does in this example:

    theorem my_lemma3 :
        ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
      intro x y ε epos ele1 xlt ylt
      sorry

We can use any names we want for the universally quantified variables; they do not have to be <span class="pre">`x`</span>, <span class="pre">`y`</span>, and <span class="pre">`ε`</span>. Notice that we have to introduce the variables even though they are marked implicit: making them implicit means that we leave them out when we write an expression *using* <span class="pre">`my_lemma`</span>, but they are still an essential part of the statement that we are proving. After the <span class="pre">`intro`</span> command, the goal is what it would have been at the start if we listed all the variables and hypotheses *before* the colon, as we did in the last section. In a moment, we will see why it is sometimes necessary to introduce variables and hypotheses after the proof begins.

To help you prove the lemma, we will start you off:

    theorem my_lemma4 :
        ∀ {x y ε : ℝ}, 0 < ε → ε ≤ 1 → |x| < ε → |y| < ε → |x * y| < ε := by
      intro x y ε epos ele1 xlt ylt
      calc
        |x * y| = |x| * |y| := sorry
        _ ≤ |x| * ε := sorry
        _ < 1 * ε := sorry
        _ = ε := sorry

Finish the proof using the theorems <span class="pre">`abs_mul`</span>, <span class="pre">`mul_le_mul`</span>, <span class="pre">`abs_nonneg`</span>, <span class="pre">`mul_lt_mul_right`</span>, and <span class="pre">`one_mul`</span>. Remember that you can find theorems like these using Ctrl-space completion (or Cmd-space completion on a Mac). Remember also that you can use <span class="pre">`.mp`</span> and <span class="pre">`.mpr`</span> or <span class="pre">`.1`</span> and <span class="pre">`.2`</span> to extract the two directions of an if-and-only-if statement.

Universal quantifiers are often hidden in definitions, and Lean will unfold definitions to expose them when necessary. For example, let’s define two predicates, <span class="pre">`FnUb`</span>` `<span class="pre">`f`</span>` `<span class="pre">`a`</span> and <span class="pre">`FnLb`</span>` `<span class="pre">`f`</span>` `<span class="pre">`a`</span>, where <span class="pre">`f`</span> is a function from the real numbers to the real numbers and <span class="pre">`a`</span> is a real number. The first says that <span class="pre">`a`</span> is an upper bound on the values of <span class="pre">`f`</span>, and the second says that <span class="pre">`a`</span> is a lower bound on the values of <span class="pre">`f`</span>.

    def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
      ∀ x, f x ≤ a

    def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
      ∀ x, a ≤ f x

In the next example, <span class="pre">`fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x`</span> is the function that maps <span class="pre">`x`</span> to <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x`</span>. Going from the expression <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x`</span> to this function is called a lambda abstraction in type theory.

    example (hfa : FnUb f a) (hgb : FnUb g b) : FnUb (fun x ↦ f x + g x) (a + b) := by
      intro x
      dsimp
      apply add_le_add
      apply hfa
      apply hgb

Applying <span class="pre">`intro`</span> to the goal <span class="pre">`FnUb`</span>` `<span class="pre">`(fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`(a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b)`</span> forces Lean to unfold the definition of <span class="pre">`FnUb`</span> and introduce <span class="pre">`x`</span> for the universal quantifier. The goal is then <span class="pre">`(fun`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ)`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`x`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b`</span>. But applying <span class="pre">`(fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x)`</span> to <span class="pre">`x`</span> should result in <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x`</span>, and the <span class="pre">`dsimp`</span> command performs that simplification. (The “d” stands for “definitional.”) You can delete that command and the proof still works; Lean would have to perform that contraction anyhow to make sense of the next <span class="pre">`apply`</span>. The <span class="pre">`dsimp`</span> command simply makes the goal more readable and helps us figure out what to do next. Another option is to use the <span class="pre">`change`</span> tactic by writing <span class="pre">`change`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b`</span>. This helps make the proof more readable, and gives you more control over how the goal is transformed.

The rest of the proof is routine. The last two <span class="pre">`apply`</span> commands force Lean to unfold the definitions of <span class="pre">`FnUb`</span> in the hypotheses. Try carrying out similar proofs of these:

    example (hfa : FnLb f a) (hgb : FnLb g b) : FnLb (fun x ↦ f x + g x) (a + b) :=
      sorry

    example (nnf : FnLb f 0) (nng : FnLb g 0) : FnLb (fun x ↦ f x * g x) 0 :=
      sorry

    example (hfa : FnUb f a) (hgb : FnUb g b) (nng : FnLb g 0) (nna : 0 ≤ a) :
        FnUb (fun x ↦ f x * g x) (a * b) :=
      sorry

Even though we have defined <span class="pre">`FnUb`</span> and <span class="pre">`FnLb`</span> for functions from the reals to the reals, you should recognize that the definitions and proofs are much more general. The definitions make sense for functions between any two types for which there is a notion of order on the codomain. Checking the type of the theorem <span class="pre">`add_le_add`</span> shows that it holds of any structure that is an “ordered additive commutative monoid”; the details of what that means don’t matter now, but it is worth knowing that the natural numbers, integers, rationals, and real numbers are all instances. So if we prove the theorem <span class="pre">`fnUb_add`</span> at that level of generality, it will apply in all these instances.

    variable {α : Type*} {R : Type*} [AddCommMonoid R] [PartialOrder R] [IsOrderedCancelAddMonoid R]

    #check add_le_add

    def FnUb' (f : α → R) (a : R) : Prop :=
      ∀ x, f x ≤ a

    theorem fnUb_add {f g : α → R} {a b : R} (hfa : FnUb' f a) (hgb : FnUb' g b) :
        FnUb' (fun x ↦ f x + g x) (a + b) := fun x ↦ add_le_add (hfa x) (hgb x)

You have already seen square brackets like these in Section <a href="C02_Basics.html#proving-identities-in-algebraic-structures" class="reference internal"><span class="std std-numref">Section 2.2</span></a>, though we still haven’t explained what they mean. For concreteness, we will stick to the real numbers for most of our examples, but it is worth knowing that Mathlib contains definitions and theorems that work at a high level of generality.

For another example of a hidden universal quantifier, Mathlib defines a predicate <span class="pre">`Monotone`</span>, which says that a function is nondecreasing in its arguments:

    example (f : ℝ → ℝ) (h : Monotone f) : ∀ {a b}, a ≤ b → f a ≤ f b :=
      @h

The property <span class="pre">`Monotone`</span>` `<span class="pre">`f`</span> is defined to be exactly the expression after the colon. We need to put the <span class="pre">`@`</span> symbol before <span class="pre">`h`</span> because if we don’t, Lean expands the implicit arguments to <span class="pre">`h`</span> and inserts placeholders.

Proving statements about monotonicity involves using <span class="pre">`intro`</span> to introduce two variables, say, <span class="pre">`a`</span> and <span class="pre">`b`</span>, and the hypothesis <span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`b`</span>. To *use* a monotonicity hypothesis, you can apply it to suitable arguments and hypotheses, and then apply the resulting expression to the goal. Or you can apply it to the goal and let Lean help you work backwards by displaying the remaining hypotheses as new subgoals.

    example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by
      intro a b aleb
      apply add_le_add
      apply mf aleb
      apply mg aleb

When a proof is this short, it is often convenient to give a proof term instead. To describe a proof that temporarily introduces objects <span class="pre">`a`</span> and <span class="pre">`b`</span> and a hypothesis <span class="pre">`aleb`</span>, Lean uses the notation <span class="pre">`fun`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`aleb`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`...`</span>. This is analogous to the way that an expression like <span class="pre">`fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`x^2`</span> describes a function by temporarily naming an object, <span class="pre">`x`</span>, and then using it to describe a value. So the <span class="pre">`intro`</span> command in the previous proof corresponds to the lambda abstraction in the next proof term. The <span class="pre">`apply`</span> commands then correspond to building the application of the theorem to its arguments.

    example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x :=
      fun a b aleb ↦ add_le_add (mf aleb) (mg aleb)

Here is a useful trick: if you start writing the proof term <span class="pre">`fun`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`aleb`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`_`</span> using an underscore where the rest of the expression should go, Lean will flag an error, indicating that it can’t guess the value of that expression. If you check the Lean Goal window in VS Code or hover over the squiggly error marker, Lean will show you the goal that the remaining expression has to solve.

Try proving these, with either tactics or proof terms:

    example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x :=
      sorry

    example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) :=
      sorry

Here are some more examples. A function <span class="math notranslate nohighlight">\\f\\</span> from <span class="math notranslate nohighlight">\\\Bbb R\\</span> to <span class="math notranslate nohighlight">\\\Bbb R\\</span> is said to be *even* if <span class="math notranslate nohighlight">\\f(-x) = f(x)\\</span> for every <span class="math notranslate nohighlight">\\x\\</span>, and *odd* if <span class="math notranslate nohighlight">\\f(-x) = -f(x)\\</span> for every <span class="math notranslate nohighlight">\\x\\</span>. The following example defines these two notions formally and establishes one fact about them. You can complete the proofs of the others.

    def FnEven (f : ℝ → ℝ) : Prop :=
      ∀ x, f x = f (-x)

    def FnOdd (f : ℝ → ℝ) : Prop :=
      ∀ x, f x = -f (-x)

    example (ef : FnEven f) (eg : FnEven g) : FnEven fun x ↦ f x + g x := by
      intro x
      calc
        (fun x ↦ f x + g x) x = f x + g x := rfl
        _ = f (-x) + g (-x) := by rw [ef, eg]


    example (of : FnOdd f) (og : FnOdd g) : FnEven fun x ↦ f x * g x := by
      sorry

    example (ef : FnEven f) (og : FnOdd g) : FnOdd fun x ↦ f x * g x := by
      sorry

    example (ef : FnEven f) (og : FnOdd g) : FnEven fun x ↦ f (g x) := by
      sorry

The first proof can be shortened using <span class="pre">`dsimp`</span> or <span class="pre">`change`</span> to get rid of the lambda abstraction. But you can check that the subsequent <span class="pre">`rw`</span> won’t work unless we get rid of the lambda abstraction explicitly, because otherwise it cannot find the patterns <span class="pre">`f`</span>` `<span class="pre">`x`</span> and <span class="pre">`g`</span>` `<span class="pre">`x`</span> in the expression. Contrary to some other tactics, <span class="pre">`rw`</span> operates on the syntactic level, it won’t unfold definitions or apply reductions for you (it has a variant called <span class="pre">`erw`</span> that tries a little harder in this direction, but not much harder).

You can find implicit universal quantifiers all over the place, once you know how to spot them.

Mathlib includes a good library for manipulating sets. Recall that Lean does not use foundations based on set theory, so here the word set has its mundane meaning of a collection of mathematical objects of some given type <span class="pre">`α`</span>. If <span class="pre">`x`</span> has type <span class="pre">`α`</span> and <span class="pre">`s`</span> has type <span class="pre">`Set`</span>` `<span class="pre">`α`</span>, then <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span> is a proposition that asserts that <span class="pre">`x`</span> is an element of <span class="pre">`s`</span>. If <span class="pre">`y`</span> has some different type <span class="pre">`β`</span> then the expression <span class="pre">`y`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span> makes no sense. Here “makes no sense” means “has no type hence Lean does not accept it as a well-formed statement”. This contrasts with Zermelo-Fraenkel set theory for instance where <span class="pre">`a`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`b`</span> is a well-formed statement for every mathematical objects <span class="pre">`a`</span> and <span class="pre">`b`</span>. For instance <span class="pre">`sin`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`cos`</span> is a well-formed statement in ZF. This defect of set theoretic foundations is an important motivation for not using it in a proof assistant which is meant to assist us by detecting meaningless expressions. In Lean <span class="pre">`sin`</span> has type <span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> and <span class="pre">`cos`</span> has type <span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> which is not equal to <span class="pre">`Set`</span>` `<span class="pre">`(ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ)`</span>, even after unfolding definitions, so the statement <span class="pre">`sin`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`cos`</span> makes no sense. One can also use Lean to work on set theory itself. For instance the independence of the continuum hypothesis from the axioms of Zermelo-Fraenkel has been formalized in Lean. But such a meta-theory of set theory is completely beyond the scope of this book.

If <span class="pre">`s`</span> and <span class="pre">`t`</span> are of type <span class="pre">`Set`</span>` `<span class="pre">`α`</span>, then the subset relation <span class="pre">`s`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`t`</span> is defined to mean <span class="pre">`∀`</span>` `<span class="pre">`{x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α},`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>` `<span class="pre">`→`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`t`</span>. The variable in the quantifier is marked implicit so that given <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`s`</span>` `<span class="pre">`⊆`</span>` `<span class="pre">`t`</span> and <span class="pre">`h'`</span>` `<span class="pre">`:`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`s`</span>, we can write <span class="pre">`h`</span>` `<span class="pre">`h'`</span> as justification for <span class="pre">`x`</span>` `<span class="pre">`∈`</span>` `<span class="pre">`t`</span>. The following example provides a tactic proof and a proof term justifying the reflexivity of the subset relation, and asks you to do the same for transitivity.

    variable {α : Type*} (r s t : Set α)

    example : s ⊆ s := by
      intro x xs
      exact xs

    theorem Subset.refl : s ⊆ s := fun x xs ↦ xs

    theorem Subset.trans : r ⊆ s → s ⊆ t → r ⊆ t := by
      sorry

Just as we defined <span class="pre">`FnUb`</span> for functions, we can define <span class="pre">`SetUb`</span>` `<span class="pre">`s`</span>` `<span class="pre">`a`</span> to mean that <span class="pre">`a`</span> is an upper bound on the set <span class="pre">`s`</span>, assuming <span class="pre">`s`</span> is a set of elements of some type that has an order associated with it. In the next example, we ask you to prove that if <span class="pre">`a`</span> is a bound on <span class="pre">`s`</span> and <span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`b`</span>, then <span class="pre">`b`</span> is a bound on <span class="pre">`s`</span> as well.

    variable {α : Type*} [PartialOrder α]
    variable (s : Set α) (a b : α)

    def SetUb (s : Set α) (a : α) :=
      ∀ x, x ∈ s → x ≤ a

    example (h : SetUb s a) (h' : a ≤ b) : SetUb s b :=
      sorry

We close this section with one last important example. A function <span class="math notranslate nohighlight">\\f\\</span> is said to be *injective* if for every <span class="math notranslate nohighlight">\\x\_1\\</span> and <span class="math notranslate nohighlight">\\x\_2\\</span>, if <span class="math notranslate nohighlight">\\f(x\_1) = f(x\_2)\\</span> then <span class="math notranslate nohighlight">\\x\_1 = x\_2\\</span>. Mathlib defines <span class="pre">`Function.Injective`</span>` `<span class="pre">`f`</span> with <span class="pre">`x₁`</span> and <span class="pre">`x₂`</span> implicit. The next example shows that, on the real numbers, any function that adds a constant is injective. We then ask you to show that multiplication by a nonzero constant is also injective, using the lemma name in the example as a source of inspiration. Recall you should use Ctrl-space completion after guessing the beginning of a lemma name.

    open Function

    example (c : ℝ) : Injective fun x ↦ x + c := by
      intro x₁ x₂ h'
      exact (add_left_inj c).mp h'

    example {c : ℝ} (h : c ≠ 0) : Injective fun x ↦ c * x := by
      sorry

Finally, show that the composition of two injective functions is injective:

    variable {α : Type*} {β : Type*} {γ : Type*}
    variable {g : β → γ} {f : α → β}

    example (injg : Injective g) (injf : Injective f) : Injective fun x ↦ g (f x) := by
      sorry

<span id="id3"></span>

## <span class="section-number">3.2. </span>The Existential Quantifier<a href="#the-existential-quantifier" class="headerlink" title="Link to this heading"></a>

The existential quantifier, which can be entered as <span class="pre">`\ex`</span> in VS Code, is used to represent the phrase “there exists.” The formal expression <span class="pre">`∃`</span>` `<span class="pre">`x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ,`</span>` `<span class="pre">`2`</span>` `<span class="pre">`<`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`x`</span>` `<span class="pre">`<`</span>` `<span class="pre">`3`</span> in Lean says that there is a real number between 2 and 3. (We will discuss the conjunction symbol, <span class="pre">`∧`</span>, in <a href="#conjunction-and-biimplication" class="reference internal"><span class="std std-numref">Section 3.4</span></a>.) The canonical way to prove such a statement is to exhibit a real number and show that it has the stated property. The number 2.5, which we can enter as <span class="pre">`5`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span> or <span class="pre">`(5`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ)`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span> when Lean cannot infer from context that we have the real numbers in mind, has the required property, and the <span class="pre">`norm_num`</span> tactic can prove that it meets the description.

There are a few ways we can put the information together. Given a goal that begins with an existential quantifier, the <span class="pre">`use`</span> tactic is used to provide the object, leaving the goal of proving the property.

    example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
      use 5 / 2
      norm_num

You can give the <span class="pre">`use`</span> tactic proofs as well as data:

    example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
      have h1 : 2 < (5 : ℝ) / 2 := by norm_num
      have h2 : (5 : ℝ) / 2 < 3 := by norm_num
      use 5 / 2, h1, h2

In fact, the <span class="pre">`use`</span> tactic automatically tries to use available assumptions as well.

    example : ∃ x : ℝ, 2 < x ∧ x < 3 := by
      have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
      use 5 / 2

Alternatively, we can use Lean’s *anonymous constructor* notation to construct a proof of an existential quantifier.

    example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
      have h : 2 < (5 : ℝ) / 2 ∧ (5 : ℝ) / 2 < 3 := by norm_num
      ⟨5 / 2, h⟩

Notice that there is no <span class="pre">`by`</span>; here we are giving an explicit proof term. The left and right angle brackets, which can be entered as <span class="pre">`\<`</span> and <span class="pre">`\>`</span> respectively, tell Lean to put together the given data using whatever construction is appropriate for the current goal. We can use the notation without going first into tactic mode:

    example : ∃ x : ℝ, 2 < x ∧ x < 3 :=
      ⟨5 / 2, by norm_num⟩

So now we know how to *prove* an exists statement. But how do we *use* one? If we know that there exists an object with a certain property, we should be able to give a name to an arbitrary one and reason about it. For example, remember the predicates <span class="pre">`FnUb`</span>` `<span class="pre">`f`</span>` `<span class="pre">`a`</span> and <span class="pre">`FnLb`</span>` `<span class="pre">`f`</span>` `<span class="pre">`a`</span> from the last section, which say that <span class="pre">`a`</span> is an upper bound or lower bound on <span class="pre">`f`</span>, respectively. We can use the existential quantifier to say that “<span class="pre">`f`</span> is bounded” without specifying the bound:

    def FnUb (f : ℝ → ℝ) (a : ℝ) : Prop :=
      ∀ x, f x ≤ a

    def FnLb (f : ℝ → ℝ) (a : ℝ) : Prop :=
      ∀ x, a ≤ f x

    def FnHasUb (f : ℝ → ℝ) :=
      ∃ a, FnUb f a

    def FnHasLb (f : ℝ → ℝ) :=
      ∃ a, FnLb f a

We can use the theorem <span class="pre">`FnUb_add`</span> from the last section to prove that if <span class="pre">`f`</span> and <span class="pre">`g`</span> have upper bounds, then so does <span class="pre">`fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`g`</span>` `<span class="pre">`x`</span>.

    variable {f g : ℝ → ℝ}

    example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
      rcases ubf with ⟨a, ubfa⟩
      rcases ubg with ⟨b, ubgb⟩
      use a + b
      apply fnUb_add ubfa ubgb

The <span class="pre">`rcases`</span> tactic unpacks the information in the existential quantifier. The annotations like <span class="pre">`⟨a,`</span>` `<span class="pre">`ubfa⟩`</span>, written with the same angle brackets as the anonymous constructors, are known as *patterns*, and they describe the information that we expect to find when we unpack the main argument. Given the hypothesis <span class="pre">`ubf`</span> that there is an upper bound for <span class="pre">`f`</span>, <span class="pre">`rcases`</span>` `<span class="pre">`ubf`</span>` `<span class="pre">`with`</span>` `<span class="pre">`⟨a,`</span>` `<span class="pre">`ubfa⟩`</span> adds a new variable <span class="pre">`a`</span> for an upper bound to the context, together with the hypothesis <span class="pre">`ubfa`</span> that it has the given property. The goal is left unchanged; what *has* changed is that we can now use the new object and the new hypothesis to prove the goal. This is a common method of reasoning in mathematics: we unpack objects whose existence is asserted or implied by some hypothesis, and then use it to establish the existence of something else.

Try using this method to establish the following. You might find it useful to turn some of the examples from the last section into named theorems, as we did with <span class="pre">`fn_ub_add`</span>, or you can insert the arguments directly into the proofs.

    example (lbf : FnHasLb f) (lbg : FnHasLb g) : FnHasLb fun x ↦ f x + g x := by
      sorry

    example {c : ℝ} (ubf : FnHasUb f) (h : c ≥ 0) : FnHasUb fun x ↦ c * f x := by
      sorry

The “r” in <span class="pre">`rcases`</span> stands for “recursive,” because it allows us to use arbitrarily complex patterns to unpack nested data. The <span class="pre">`rintro`</span> tactic is a combination of <span class="pre">`intro`</span> and <span class="pre">`rcases`</span>:

    example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x := by
      rintro ⟨a, ubfa⟩ ⟨b, ubgb⟩
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

In fact, Lean also supports a pattern-matching fun in expressions and proof terms:

    example : FnHasUb f → FnHasUb g → FnHasUb fun x ↦ f x + g x :=
      fun ⟨a, ubfa⟩ ⟨b, ubgb⟩ ↦ ⟨a + b, fnUb_add ubfa ubgb⟩

The task of unpacking information in a hypothesis is so important that Lean and Mathlib provide a number of ways to do it. For example, the <span class="pre">`obtain`</span> tactic provides suggestive syntax:

    example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
      obtain ⟨a, ubfa⟩ := ubf
      obtain ⟨b, ubgb⟩ := ubg
      exact ⟨a + b, fnUb_add ubfa ubgb⟩

Think of the first <span class="pre">`obtain`</span> instruction as matching the “contents” of <span class="pre">`ubf`</span> with the given pattern and assigning the components to the named variables. <span class="pre">`rcases`</span> and <span class="pre">`obtain`</span> are said to <span class="pre">`destruct`</span> their arguments.

Lean also supports syntax that is similar to that used in other functional programming languages:

    example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
      cases ubf
      case intro a ubfa =>
        cases ubg
        case intro b ubgb =>
          exact ⟨a + b, fnUb_add ubfa ubgb⟩

    example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
      cases ubf
      next a ubfa =>
        cases ubg
        next b ubgb =>
          exact ⟨a + b, fnUb_add ubfa ubgb⟩

    example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x := by
      match ubf, ubg with
        | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
          exact ⟨a + b, fnUb_add ubfa ubgb⟩

    example (ubf : FnHasUb f) (ubg : FnHasUb g) : FnHasUb fun x ↦ f x + g x :=
      match ubf, ubg with
        | ⟨a, ubfa⟩, ⟨b, ubgb⟩ =>
          ⟨a + b, fnUb_add ubfa ubgb⟩

In the first example, if you put your cursor after <span class="pre">`cases`</span>` `<span class="pre">`ubf`</span>, you will see that the tactic produces a single goal, which Lean has tagged <span class="pre">`intro`</span>. (The particular name chosen comes from the internal name for the axiomatic primitive that builds a proof of an existential statement.) The <span class="pre">`case`</span> tactic then names the components. The second example is similar, except using <span class="pre">`next`</span> instead of <span class="pre">`case`</span> means that you can avoid mentioning <span class="pre">`intro`</span>. The word <span class="pre">`match`</span> in the last two examples highlights that what we are doing here is what computer scientists call “pattern matching.” Notice that the third proof begins by <span class="pre">`by`</span>, after which the tactic version of <span class="pre">`match`</span> expects a tactic proof on the right side of the arrow. The last example is a proof term: there are no tactics in sight.

For the rest of this book, we will stick to <span class="pre">`rcases`</span>, <span class="pre">`rintro`</span>, and <span class="pre">`obtain`</span>, as the preferred ways of using an existential quantifier. But it can’t hurt to see the alternative syntax, especially if there is a chance you will find yourself in the company of computer scientists.

To illustrate one way that <span class="pre">`rcases`</span> can be used, we prove an old mathematical chestnut: if two integers <span class="pre">`x`</span> and <span class="pre">`y`</span> can each be written as a sum of two squares, then so can their product, <span class="pre">`x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span>. In fact, the statement is true for any commutative ring, not just the integers. In the next example, <span class="pre">`rcases`</span> unpacks two existential quantifiers at once. We then provide the magic values needed to express <span class="pre">`x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span> as a sum of squares as a list to the <span class="pre">`use`</span> statement, and we use <span class="pre">`ring`</span> to verify that they work.

    variable {α : Type*} [CommRing α]

    def SumOfSquares (x : α) :=
      ∃ a b, x = a ^ 2 + b ^ 2

    theorem sumOfSquares_mul {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
        SumOfSquares (x * y) := by
      rcases sosx with ⟨a, b, xeq⟩
      rcases sosy with ⟨c, d, yeq⟩
      rw [xeq, yeq]
      use a * c - b * d, a * d + b * c
      ring

This proof doesn’t provide much insight, but here is one way to motivate it. A *Gaussian integer* is a number of the form <span class="math notranslate nohighlight">\\a + bi\\</span> where <span class="math notranslate nohighlight">\\a\\</span> and <span class="math notranslate nohighlight">\\b\\</span> are integers and <span class="math notranslate nohighlight">\\i = \sqrt{-1}\\</span>. The *norm* of the Gaussian integer <span class="math notranslate nohighlight">\\a + bi\\</span> is, by definition, <span class="math notranslate nohighlight">\\a^2 + b^2\\</span>. So the norm of a Gaussian integer is a sum of squares, and any sum of squares can be expressed in this way. The theorem above reflects the fact that norm of a product of Gaussian integers is the product of their norms: if <span class="math notranslate nohighlight">\\x\\</span> is the norm of <span class="math notranslate nohighlight">\\a + bi\\</span> and <span class="math notranslate nohighlight">\\y\\</span> in the norm of <span class="math notranslate nohighlight">\\c + di\\</span>, then <span class="math notranslate nohighlight">\\xy\\</span> is the norm of <span class="math notranslate nohighlight">\\(a + bi) (c + di)\\</span>. Our cryptic proof illustrates the fact that the proof that is easiest to formalize isn’t always the most perspicuous one. In <a href="C07_Structures.html#section-building-the-gaussian-integers" class="reference internal"><span class="std std-numref">Section 7.3</span></a>, we will provide you with the means to define the Gaussian integers and use them to provide an alternative proof.

The pattern of unpacking an equation inside an existential quantifier and then using it to rewrite an expression in the goal comes up often, so much so that the <span class="pre">`rcases`</span> tactic provides an abbreviation: if you use the keyword <span class="pre">`rfl`</span> in place of a new identifier, <span class="pre">`rcases`</span> does the rewriting automatically (this trick doesn’t work with pattern-matching lambdas).

    theorem sumOfSquares_mul' {x y : α} (sosx : SumOfSquares x) (sosy : SumOfSquares y) :
        SumOfSquares (x * y) := by
      rcases sosx with ⟨a, b, rfl⟩
      rcases sosy with ⟨c, d, rfl⟩
      use a * c - b * d, a * d + b * c
      ring

As with the universal quantifier, you can find existential quantifiers hidden all over if you know how to spot them. For example, divisibility is implicitly an “exists” statement.

    example (divab : a ∣ b) (divbc : b ∣ c) : a ∣ c := by
      rcases divab with ⟨d, beq⟩
      rcases divbc with ⟨e, ceq⟩
      rw [ceq, beq]
      use d * e; ring

And once again, this provides a nice setting for using <span class="pre">`rcases`</span> with <span class="pre">`rfl`</span>. Try it out in the proof above. It feels pretty good!

Then try proving the following:

    example (divab : a ∣ b) (divac : a ∣ c) : a ∣ b + c := by
      sorry

For another important example, a function <span class="math notranslate nohighlight">\\f : \alpha \to \beta\\</span> is said to be *surjective* if for every <span class="math notranslate nohighlight">\\y\\</span> in the codomain, <span class="math notranslate nohighlight">\\\beta\\</span>, there is an <span class="math notranslate nohighlight">\\x\\</span> in the domain, <span class="math notranslate nohighlight">\\\alpha\\</span>, such that <span class="math notranslate nohighlight">\\f(x) = y\\</span>. Notice that this statement includes both a universal and an existential quantifier, which explains why the next example makes use of both <span class="pre">`intro`</span> and <span class="pre">`use`</span>.

    example {c : ℝ} : Surjective fun x ↦ x + c := by
      intro x
      use x - c
      dsimp; ring

Try this example yourself using the theorem <span class="pre">`mul_div_cancel₀`</span>.:

    example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by
      sorry

At this point, it is worth mentioning that there is a tactic, <span class="pre">`field_simp`</span>, that will often clear denominators in a useful way. It can be used in conjunction with the <span class="pre">`ring`</span> tactic.

    example (x y : ℝ) (h : x - y ≠ 0) : (x ^ 2 - y ^ 2) / (x - y) = x + y := by
      field_simp [h]
      ring

The next example uses a surjectivity hypothesis by applying it to a suitable value. Note that you can use <span class="pre">`rcases`</span> with any expression, not just a hypothesis.

    example {f : ℝ → ℝ} (h : Surjective f) : ∃ x, f x ^ 2 = 4 := by
      rcases h 2 with ⟨x, hx⟩
      use x
      rw [hx]
      norm_num

See if you can use these methods to show that the composition of surjective functions is surjective.

    variable {α : Type*} {β : Type*} {γ : Type*}
    variable {g : β → γ} {f : α → β}

    example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by
      sorry

<span id="id4"></span>

## <span class="section-number">3.3. </span>Negation<a href="#negation" class="headerlink" title="Link to this heading"></a>

The symbol <span class="pre">`¬`</span> is meant to express negation, so <span class="pre">`¬`</span>` `<span class="pre">`x`</span>` `<span class="pre">`<`</span>` `<span class="pre">`y`</span> says that <span class="pre">`x`</span> is not less than <span class="pre">`y`</span>, <span class="pre">`¬`</span>` `<span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y`</span> (or, equivalently, <span class="pre">`x`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`y`</span>) says that <span class="pre">`x`</span> is not equal to <span class="pre">`y`</span>, and <span class="pre">`¬`</span>` `<span class="pre">`∃`</span>` `<span class="pre">`z,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`<`</span>` `<span class="pre">`z`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`z`</span>` `<span class="pre">`<`</span>` `<span class="pre">`y`</span> says that there does not exist a <span class="pre">`z`</span> strictly between <span class="pre">`x`</span> and <span class="pre">`y`</span>. In Lean, the notation <span class="pre">`¬`</span>` `<span class="pre">`A`</span> abbreviates <span class="pre">`A`</span>` `<span class="pre">`→`</span>` `<span class="pre">`False`</span>, which you can think of as saying that <span class="pre">`A`</span> implies a contradiction. Practically speaking, this means that you already know something about how to work with negations: you can prove <span class="pre">`¬`</span>` `<span class="pre">`A`</span> by introducing a hypothesis <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`A`</span> and proving <span class="pre">`False`</span>, and if you have <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`A`</span> and <span class="pre">`h'`</span>` `<span class="pre">`:`</span>` `<span class="pre">`A`</span>, then applying <span class="pre">`h`</span> to <span class="pre">`h'`</span> yields <span class="pre">`False`</span>.

To illustrate, consider the irreflexivity principle <span class="pre">`lt_irrefl`</span> for a strict order, which says that we have <span class="pre">`¬`</span>` `<span class="pre">`a`</span>` `<span class="pre">`<`</span>` `<span class="pre">`a`</span> for every <span class="pre">`a`</span>. The asymmetry principle <span class="pre">`lt_asymm`</span> says that we have <span class="pre">`a`</span>` `<span class="pre">`<`</span>` `<span class="pre">`b`</span>` `<span class="pre">`→`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`b`</span>` `<span class="pre">`<`</span>` `<span class="pre">`a`</span>. Let’s show that <span class="pre">`lt_asymm`</span> follows from <span class="pre">`lt_irrefl`</span>.

    example (h : a < b) : ¬b < a := by
      intro h'
      have : a < a := lt_trans h h'
      apply lt_irrefl a this

This example introduces a couple of new tricks. First, when you use <span class="pre">`have`</span> without providing a label, Lean uses the name <span class="pre">`this`</span>, providing a convenient way to refer back to it. Because the proof is so short, we provide an explicit proof term. But what you should really be paying attention to in this proof is the result of the <span class="pre">`intro`</span> tactic, which leaves a goal of <span class="pre">`False`</span>, and the fact that we eventually prove <span class="pre">`False`</span> by applying <span class="pre">`lt_irrefl`</span> to a proof of <span class="pre">`a`</span>` `<span class="pre">`<`</span>` `<span class="pre">`a`</span>.

Here is another example, which uses the predicate <span class="pre">`FnHasUb`</span> defined in the last section, which says that a function has an upper bound.

    example (h : ∀ a, ∃ x, f x > a) : ¬FnHasUb f := by
      intro fnub
      rcases fnub with ⟨a, fnuba⟩
      rcases h a with ⟨x, hx⟩
      have : f x ≤ a := fnuba x
      linarith

Remember that it is often convenient to use <span class="pre">`linarith`</span> when a goal follows from linear equations and inequalities that are in the context.

See if you can prove these in a similar way:

    example (h : ∀ a, ∃ x, f x < a) : ¬FnHasLb f :=
      sorry

    example : ¬FnHasUb fun x ↦ x :=
      sorry

Mathlib offers a number of useful theorems for relating orders and negations:

    #check (not_le_of_gt : a > b → ¬a ≤ b)
    #check (not_lt_of_ge : a ≥ b → ¬a < b)
    #check (lt_of_not_ge : ¬a ≥ b → a < b)
    #check (le_of_not_gt : ¬a > b → a ≤ b)

Recall the predicate <span class="pre">`Monotone`</span>` `<span class="pre">`f`</span>, which says that <span class="pre">`f`</span> is nondecreasing. Use some of the theorems just enumerated to prove the following:

    example (h : Monotone f) (h' : f a < f b) : a < b := by
      sorry

    example (h : a ≤ b) (h' : f b < f a) : ¬Monotone f := by
      sorry

We can show that the first example in the last snippet cannot be proved if we replace <span class="pre">`<`</span> by <span class="pre">`≤`</span>. Notice that we can prove the negation of a universally quantified statement by giving a counterexample. Complete the proof.

    example : ¬∀ {f : ℝ → ℝ}, Monotone f → ∀ {a b}, f a ≤ f b → a ≤ b := by
      intro h
      let f := fun x : ℝ ↦ (0 : ℝ)
      have monof : Monotone f := by sorry
      have h' : f 1 ≤ f 0 := le_refl _
      sorry

This example introduces the <span class="pre">`let`</span> tactic, which adds a *local definition* to the context. If you put the cursor after the <span class="pre">`let`</span> command, in the goal window you will see that the definition <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`:=`</span>` `<span class="pre">`fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`0`</span> has been added to the context. Lean will unfold the definition of <span class="pre">`f`</span> when it has to. In particular, when we prove <span class="pre">`f`</span>` `<span class="pre">`1`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`f`</span>` `<span class="pre">`0`</span> with <span class="pre">`le_refl`</span>, Lean reduces <span class="pre">`f`</span>` `<span class="pre">`1`</span> and <span class="pre">`f`</span>` `<span class="pre">`0`</span> to <span class="pre">`0`</span>.

Use <span class="pre">`le_of_not_gt`</span> to prove the following:

    example (x : ℝ) (h : ∀ ε > 0, x < ε) : x ≤ 0 := by
      sorry

Implicit in many of the proofs we have just done is the fact that if <span class="pre">`P`</span> is any property, saying that there is nothing with property <span class="pre">`P`</span> is the same as saying that everything fails to have property <span class="pre">`P`</span>, and saying that not everything has property <span class="pre">`P`</span> is equivalent to saying that something fails to have property <span class="pre">`P`</span>. In other words, all four of the following implications are valid (but one of them cannot be proved with what we explained so far):

    variable {α : Type*} (P : α → Prop) (Q : Prop)

    example (h : ¬∃ x, P x) : ∀ x, ¬P x := by
      sorry

    example (h : ∀ x, ¬P x) : ¬∃ x, P x := by
      sorry

    example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
      sorry

    example (h : ∃ x, ¬P x) : ¬∀ x, P x := by
      sorry

The first, second, and fourth are straightforward to prove using the methods you have already seen. We encourage you to try it. The third is more difficult, however, because it concludes that an object exists from the fact that its nonexistence is contradictory. This is an instance of *classical* mathematical reasoning. We can use proof by contradiction to prove the third implication as follows.

    example (h : ¬∀ x, P x) : ∃ x, ¬P x := by
      by_contra h'
      apply h
      intro x
      show P x
      by_contra h''
      exact h' ⟨x, h''⟩

Make sure you understand how this works. The <span class="pre">`by_contra`</span> tactic allows us to prove a goal <span class="pre">`Q`</span> by assuming <span class="pre">`¬`</span>` `<span class="pre">`Q`</span> and deriving a contradiction. In fact, it is equivalent to using the equivalence <span class="pre">`not_not`</span>` `<span class="pre">`:`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`Q`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`Q`</span>. Confirm that you can prove the forward direction of this equivalence using <span class="pre">`by_contra`</span>, while the reverse direction follows from the ordinary rules for negation.

    example (h : ¬¬Q) : Q := by
      sorry

    example (h : Q) : ¬¬Q := by
      sorry

Use proof by contradiction to establish the following, which is the converse of one of the implications we proved above. (Hint: use <span class="pre">`intro`</span> first.)

    example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
      sorry

It is often tedious to work with compound statements with a negation in front, and it is a common mathematical pattern to replace such statements with equivalent forms in which the negation has been pushed inward. To facilitate this, Mathlib offers a <span class="pre">`push_neg`</span> tactic, which restates the goal in this way. The command <span class="pre">`push_neg`</span>` `<span class="pre">`at`</span>` `<span class="pre">`h`</span> restates the hypothesis <span class="pre">`h`</span>.

    example (h : ¬∀ a, ∃ x, f x > a) : FnHasUb f := by
      push_neg at h
      exact h

    example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
      dsimp only [FnHasUb, FnUb] at h
      push_neg at h
      exact h

In the second example, we use dsimp to expand the definitions of <span class="pre">`FnHasUb`</span> and <span class="pre">`FnUb`</span>. (We need to use <span class="pre">`dsimp`</span> rather than <span class="pre">`rw`</span> to expand <span class="pre">`FnUb`</span>, because it appears in the scope of a quantifier.) You can verify that in the examples above with <span class="pre">`¬∃`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span> and <span class="pre">`¬∀`</span>` `<span class="pre">`x,`</span>` `<span class="pre">`P`</span>` `<span class="pre">`x`</span>, the <span class="pre">`push_neg`</span> tactic does the expected thing. Without even knowing how to use the conjunction symbol, you should be able to use <span class="pre">`push_neg`</span> to prove the following:

    example (h : ¬Monotone f) : ∃ x y, x ≤ y ∧ f y < f x := by
      sorry

Mathlib also has a tactic, <span class="pre">`contrapose`</span>, which transforms a goal <span class="pre">`A`</span>` `<span class="pre">`→`</span>` `<span class="pre">`B`</span> to <span class="pre">`¬B`</span>` `<span class="pre">`→`</span>` `<span class="pre">`¬A`</span>. Similarly, given a goal of proving <span class="pre">`B`</span> from hypothesis <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`A`</span>, <span class="pre">`contrapose`</span>` `<span class="pre">`h`</span> leaves you with a goal of proving <span class="pre">`¬A`</span> from hypothesis <span class="pre">`¬B`</span>. Using <span class="pre">`contrapose!`</span> instead of <span class="pre">`contrapose`</span> applies <span class="pre">`push_neg`</span> to the goal and the relevant hypothesis as well.

    example (h : ¬FnHasUb f) : ∀ a, ∃ x, f x > a := by
      contrapose! h
      exact h

    example (x : ℝ) (h : ∀ ε > 0, x ≤ ε) : x ≤ 0 := by
      contrapose! h
      use x / 2
      constructor <;> linarith

We have not yet explained the <span class="pre">`constructor`</span> command or the use of the semicolon after it, but we will do that in the next section.

We close this section with the principle of *ex falso*, which says that anything follows from a contradiction. In Lean, this is represented by <span class="pre">`False.elim`</span>, which establishes <span class="pre">`False`</span>` `<span class="pre">`→`</span>` `<span class="pre">`P`</span> for any proposition <span class="pre">`P`</span>. This may seem like a strange principle, but it comes up fairly often. We often prove a theorem by splitting on cases, and sometimes we can show that one of the cases is contradictory. In that case, we need to assert that the contradiction establishes the goal so we can move on to the next one. (We will see instances of reasoning by cases in <a href="#disjunction" class="reference internal"><span class="std std-numref">Section 3.5</span></a>.)

Lean provides a number of ways of closing a goal once a contradiction has been reached.

    example (h : 0 < 0) : a > 37 := by
      exfalso
      apply lt_irrefl 0 h

    example (h : 0 < 0) : a > 37 :=
      absurd h (lt_irrefl 0)

    example (h : 0 < 0) : a > 37 := by
      have h' : ¬0 < 0 := lt_irrefl 0
      contradiction

The <span class="pre">`exfalso`</span> tactic replaces the current goal with the goal of proving <span class="pre">`False`</span>. Given <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`P`</span> and <span class="pre">`h'`</span>` `<span class="pre">`:`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`P`</span>, the term <span class="pre">`absurd`</span>` `<span class="pre">`h`</span>` `<span class="pre">`h'`</span> establishes any proposition. Finally, the <span class="pre">`contradiction`</span> tactic tries to close a goal by finding a contradiction in the hypotheses, such as a pair of the form <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`P`</span> and <span class="pre">`h'`</span>` `<span class="pre">`:`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`P`</span>. Of course, in this example, <span class="pre">`linarith`</span> also works.

<span id="conjunction-and-biimplication"></span>

## <span class="section-number">3.4. </span>Conjunction and Iff<a href="#conjunction-and-iff" class="headerlink" title="Link to this heading"></a>

You have already seen that the conjunction symbol, <span class="pre">`∧`</span>, is used to express “and.” The <span class="pre">`constructor`</span> tactic allows you to prove a statement of the form <span class="pre">`A`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`B`</span> by proving <span class="pre">`A`</span> and then proving <span class="pre">`B`</span>.

    example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y := by
      constructor
      · assumption
      intro h
      apply h₁
      rw [h]

In this example, the <span class="pre">`assumption`</span> tactic tells Lean to find an assumption that will solve the goal. Notice that the final <span class="pre">`rw`</span> finishes the goal by applying the reflexivity of <span class="pre">`≤`</span>. The following are alternative ways of carrying out the previous examples using the anonymous constructor angle brackets. The first is a slick proof-term version of the previous proof, which drops into tactic mode at the keyword <span class="pre">`by`</span>.

    example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
      ⟨h₀, fun h ↦ h₁ (by rw [h])⟩

    example {x y : ℝ} (h₀ : x ≤ y) (h₁ : ¬y ≤ x) : x ≤ y ∧ x ≠ y :=
      have h : x ≠ y := by
        contrapose! h₁
        rw [h₁]
      ⟨h₀, h⟩

*Using* a conjunction instead of proving one involves unpacking the proofs of the two parts. You can use the <span class="pre">`rcases`</span> tactic for that, as well as <span class="pre">`rintro`</span> or a pattern-matching <span class="pre">`fun`</span>, all in a manner similar to the way they are used with the existential quantifier.

    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
      rcases h with ⟨h₀, h₁⟩
      contrapose! h₁
      exact le_antisymm h₀ h₁

    example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x := by
      rintro ⟨h₀, h₁⟩ h'
      exact h₁ (le_antisymm h₀ h')

    example {x y : ℝ} : x ≤ y ∧ x ≠ y → ¬y ≤ x :=
      fun ⟨h₀, h₁⟩ h' ↦ h₁ (le_antisymm h₀ h')

In analogy to the <span class="pre">`obtain`</span> tactic, there is also a pattern-matching <span class="pre">`have`</span>:

    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
      have ⟨h₀, h₁⟩ := h
      contrapose! h₁
      exact le_antisymm h₀ h₁

In contrast to <span class="pre">`rcases`</span>, here the <span class="pre">`have`</span> tactic leaves <span class="pre">`h`</span> in the context. And even though we won’t use them, once again we have the computer scientists’ pattern-matching syntax:

    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
      cases h
      case intro h₀ h₁ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
      cases h
      next h₀ h₁ =>
        contrapose! h₁
        exact le_antisymm h₀ h₁

    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
      match h with
        | ⟨h₀, h₁⟩ =>
            contrapose! h₁
            exact le_antisymm h₀ h₁

In contrast to using an existential quantifier, you can also extract proofs of the two components of a hypothesis <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`A`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`B`</span> by writing <span class="pre">`h.left`</span> and <span class="pre">`h.right`</span>, or, equivalently, <span class="pre">`h.1`</span> and <span class="pre">`h.2`</span>.

    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x := by
      intro h'
      apply h.right
      exact le_antisymm h.left h'

    example {x y : ℝ} (h : x ≤ y ∧ x ≠ y) : ¬y ≤ x :=
      fun h' ↦ h.right (le_antisymm h.left h')

Try using these techniques to come up with various ways of proving of the following:

    example {m n : ℕ} (h : m ∣ n ∧ m ≠ n) : m ∣ n ∧ ¬n ∣ m :=
      sorry

You can nest uses of <span class="pre">`∃`</span> and <span class="pre">`∧`</span> with anonymous constructors, <span class="pre">`rintro`</span>, and <span class="pre">`rcases`</span>.

    example : ∃ x : ℝ, 2 < x ∧ x < 4 :=
      ⟨5 / 2, by norm_num, by norm_num⟩

    example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y := by
      rintro ⟨z, xltz, zlty⟩
      exact lt_trans xltz zlty

    example (x y : ℝ) : (∃ z : ℝ, x < z ∧ z < y) → x < y :=
      fun ⟨z, xltz, zlty⟩ ↦ lt_trans xltz zlty

You can also use the <span class="pre">`use`</span> tactic:

    example : ∃ x : ℝ, 2 < x ∧ x < 4 := by
      use 5 / 2
      constructor <;> norm_num

    example : ∃ m n : ℕ, 4 < m ∧ m < n ∧ n < 10 ∧ Nat.Prime m ∧ Nat.Prime n := by
      use 5
      use 7
      norm_num

    example {x y : ℝ} : x ≤ y ∧ x ≠ y → x ≤ y ∧ ¬y ≤ x := by
      rintro ⟨h₀, h₁⟩
      use h₀
      exact fun h' ↦ h₁ (le_antisymm h₀ h')

In the first example, the semicolon after the <span class="pre">`constructor`</span> command tells Lean to use the <span class="pre">`norm_num`</span> tactic on both of the goals that result.

In Lean, <span class="pre">`A`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`B`</span> is *not* defined to be <span class="pre">`(A`</span>` `<span class="pre">`→`</span>` `<span class="pre">`B)`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`(B`</span>` `<span class="pre">`→`</span>` `<span class="pre">`A)`</span>, but it could have been, and it behaves roughly the same way. You have already seen that you can write <span class="pre">`h.mp`</span> and <span class="pre">`h.mpr`</span> or <span class="pre">`h.1`</span> and <span class="pre">`h.2`</span> for the two directions of <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`A`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`B`</span>. You can also use <span class="pre">`cases`</span> and friends. To prove an if-and-only-if statement, you can use <span class="pre">`constructor`</span> or angle brackets, just as you would if you were proving a conjunction.

    example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y := by
      constructor
      · contrapose!
        rintro rfl
        rfl
      contrapose!
      exact le_antisymm h

    example {x y : ℝ} (h : x ≤ y) : ¬y ≤ x ↔ x ≠ y :=
      ⟨fun h₀ h₁ ↦ h₀ (by rw [h₁]), fun h₀ h₁ ↦ h₀ (le_antisymm h h₁)⟩

The last proof term is inscrutable. Remember that you can use underscores while writing an expression like that to see what Lean expects.

Try out the various techniques and gadgets you have just seen in order to prove the following:

    example {x y : ℝ} : x ≤ y ∧ ¬y ≤ x ↔ x ≤ y ∧ x ≠ y :=
      sorry

For a more interesting exercise, show that for any two real numbers <span class="pre">`x`</span> and <span class="pre">`y`</span>, <span class="pre">`x^2`</span>` `<span class="pre">`+`</span>` `<span class="pre">`y^2`</span>` `<span class="pre">`=`</span>` `<span class="pre">`0`</span> if and only if <span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`0`</span> and <span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`0`</span>. We suggest proving an auxiliary lemma using <span class="pre">`linarith`</span>, <span class="pre">`pow_two_nonneg`</span>, and <span class="pre">`pow_eq_zero`</span>.

    theorem aux {x y : ℝ} (h : x ^ 2 + y ^ 2 = 0) : x = 0 :=
      have h' : x ^ 2 = 0 := by sorry
      pow_eq_zero h'

    example (x y : ℝ) : x ^ 2 + y ^ 2 = 0 ↔ x = 0 ∧ y = 0 :=
      sorry

In Lean, bi-implication leads a double-life. You can treat it like a conjunction and use its two parts separately. But Lean also knows that it is a reflexive, symmetric, and transitive relation between propositions, and you can also use it with <span class="pre">`calc`</span> and <span class="pre">`rw`</span>. It is often convenient to rewrite a statement to an equivalent one. In the next example, we use <span class="pre">`abs_lt`</span> to replace an expression of the form <span class="pre">`|x|`</span>` `<span class="pre">`<`</span>` `<span class="pre">`y`</span> by the equivalent expression <span class="pre">`-`</span>` `<span class="pre">`y`</span>` `<span class="pre">`<`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`x`</span>` `<span class="pre">`<`</span>` `<span class="pre">`y`</span>, and in the one after that we use <span class="pre">`Nat.dvd_gcd_iff`</span> to replace an expression of the form <span class="pre">`m`</span>` `<span class="pre">`∣`</span>` `<span class="pre">`Nat.gcd`</span>` `<span class="pre">`n`</span>` `<span class="pre">`k`</span> by the equivalent expression <span class="pre">`m`</span>` `<span class="pre">`∣`</span>` `<span class="pre">`n`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`m`</span>` `<span class="pre">`∣`</span>` `<span class="pre">`k`</span>.

    example (x : ℝ) : |x + 3| < 5 → -8 < x ∧ x < 2 := by
      rw [abs_lt]
      intro h
      constructor <;> linarith

    example : 3 ∣ Nat.gcd 6 15 := by
      rw [Nat.dvd_gcd_iff]
      constructor <;> norm_num

See if you can use <span class="pre">`rw`</span> with the theorem below to provide a short proof that negation is not a nondecreasing function. (Note that <span class="pre">`push_neg`</span> won’t unfold definitions for you, so the <span class="pre">`rw`</span>` `<span class="pre">`[Monotone]`</span> in the proof of the theorem is needed.)

    theorem not_monotone_iff {f : ℝ → ℝ} : ¬Monotone f ↔ ∃ x y, x ≤ y ∧ f x > f y := by
      rw [Monotone]
      push_neg
      rfl

    example : ¬Monotone fun x : ℝ ↦ -x := by
      sorry

The remaining exercises in this section are designed to give you some more practice with conjunction and bi-implication. Remember that a *partial order* is a binary relation that is transitive, reflexive, and antisymmetric. An even weaker notion sometimes arises: a *preorder* is just a reflexive, transitive relation. For any pre-order <span class="pre">`≤`</span>, Lean axiomatizes the associated strict pre-order by <span class="pre">`a`</span>` `<span class="pre">`<`</span>` `<span class="pre">`b`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`b`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`b`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`a`</span>. Show that if <span class="pre">`≤`</span> is a partial order, then <span class="pre">`a`</span>` `<span class="pre">`<`</span>` `<span class="pre">`b`</span> is equivalent to <span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`b`</span>` `<span class="pre">`∧`</span>` `<span class="pre">`a`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`b`</span>:

    variable {α : Type*} [PartialOrder α]
    variable (a b : α)

    example : a < b ↔ a ≤ b ∧ a ≠ b := by
      rw [lt_iff_le_not_ge]
      sorry

Beyond logical operations, you do not need anything more than <span class="pre">`le_refl`</span> and <span class="pre">`le_trans`</span>. Show that even in the case where <span class="pre">`≤`</span> is only assumed to be a preorder, we can prove that the strict order is irreflexive and transitive. In the second example, for convenience, we use the simplifier rather than <span class="pre">`rw`</span> to express <span class="pre">`<`</span> in terms of <span class="pre">`≤`</span> and <span class="pre">`¬`</span>. We will come back to the simplifier later, but here we are only relying on the fact that it will use the indicated lemma repeatedly, even if it needs to be instantiated to different values.

    variable {α : Type*} [Preorder α]
    variable (a b c : α)

    example : ¬a < a := by
      rw [lt_iff_le_not_ge]
      sorry

    example : a < b → b < c → a < c := by
      simp only [lt_iff_le_not_ge]
      sorry

<span id="id5"></span>

## <span class="section-number">3.5. </span>Disjunction<a href="#disjunction" class="headerlink" title="Link to this heading"></a>

The canonical way to prove a disjunction <span class="pre">`A`</span>` `<span class="pre">`∨`</span>` `<span class="pre">`B`</span> is to prove <span class="pre">`A`</span> or to prove <span class="pre">`B`</span>. The <span class="pre">`left`</span> tactic chooses <span class="pre">`A`</span>, and the <span class="pre">`right`</span> tactic chooses <span class="pre">`B`</span>.

    variable {x y : ℝ}

    example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
      left
      linarith [pow_two_nonneg x]

    example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
      right
      linarith [pow_two_nonneg x]

We cannot use an anonymous constructor to construct a proof of an “or” because Lean would have to guess which disjunct we are trying to prove. When we write proof terms we can use <span class="pre">`Or.inl`</span> and <span class="pre">`Or.inr`</span> instead to make the choice explicitly. Here, <span class="pre">`inl`</span> is short for “introduction left” and <span class="pre">`inr`</span> is short for “introduction right.”

    example (h : y > 0) : y > 0 ∨ y < -1 :=
      Or.inl h

    example (h : y < -1) : y > 0 ∨ y < -1 :=
      Or.inr h

It may seem strange to prove a disjunction by proving one side or the other. In practice, which case holds usually depends on a case distinction that is implicit or explicit in the assumptions and the data. The <span class="pre">`rcases`</span> tactic allows us to make use of a hypothesis of the form <span class="pre">`A`</span>` `<span class="pre">`∨`</span>` `<span class="pre">`B`</span>. In contrast to the use of <span class="pre">`rcases`</span> with conjunction or an existential quantifier, here the <span class="pre">`rcases`</span> tactic produces *two* goals. Both have the same conclusion, but in the first case, <span class="pre">`A`</span> is assumed to be true, and in the second case, <span class="pre">`B`</span> is assumed to be true. In other words, as the name suggests, the <span class="pre">`rcases`</span> tactic carries out a proof by cases. As usual, we can tell Lean what names to use for the hypotheses. In the next example, we tell Lean to use the name <span class="pre">`h`</span> on each branch.

    example : x < |y| → x < y ∨ x < -y := by
      rcases le_or_gt 0 y with h | h
      · rw [abs_of_nonneg h]
        intro h; left; exact h
      · rw [abs_of_neg h]
        intro h; right; exact h

Notice that the pattern changes from <span class="pre">`⟨h₀,`</span>` `<span class="pre">`h₁⟩`</span> in the case of a conjunction to <span class="pre">`h₀`</span>` `<span class="pre">`|`</span>` `<span class="pre">`h₁`</span> in the case of a disjunction. Think of the first pattern as matching against data the contains *both* an <span class="pre">`h₀`</span> and a <span class="pre">`h₁`</span>, whereas second pattern, with the bar, matches against data that contains *either* an <span class="pre">`h₀`</span> or <span class="pre">`h₁`</span>. In this case, because the two goals are separate, we have chosen to use the same name, <span class="pre">`h`</span>, in each case.

The absolute value function is defined in such a way that we can immediately prove that <span class="pre">`x`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`0`</span> implies <span class="pre">`|x|`</span>` `<span class="pre">`=`</span>` `<span class="pre">`x`</span> (this is the theorem <span class="pre">`abs_of_nonneg`</span>) and <span class="pre">`x`</span>` `<span class="pre">`<`</span>` `<span class="pre">`0`</span> implies <span class="pre">`|x|`</span>` `<span class="pre">`=`</span>` `<span class="pre">`-x`</span> (this is <span class="pre">`abs_of_neg`</span>). The expression <span class="pre">`le_or_gt`</span>` `<span class="pre">`0`</span>` `<span class="pre">`x`</span> establishes <span class="pre">`0`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`x`</span>` `<span class="pre">`∨`</span>` `<span class="pre">`x`</span>` `<span class="pre">`<`</span>` `<span class="pre">`0`</span>, allowing us to split on those two cases.

Lean also supports the computer scientists’ pattern-matching syntax for disjunction. Now the <span class="pre">`cases`</span> tactic is more attractive, because it allows us to name each <span class="pre">`case`</span>, and name the hypothesis that is introduced closer to where it is used.

    example : x < |y| → x < y ∨ x < -y := by
      cases le_or_gt 0 y
      case inl h =>
        rw [abs_of_nonneg h]
        intro h; left; exact h
      case inr h =>
        rw [abs_of_neg h]
        intro h; right; exact h

The names <span class="pre">`inl`</span> and <span class="pre">`inr`</span> are short for “intro left” and “intro right,” respectively. Using <span class="pre">`case`</span> has the advantage that you can prove the cases in either order; Lean uses the tag to find the relevant goal. If you don’t care about that, you can use <span class="pre">`next`</span>, or <span class="pre">`match`</span>, or even a pattern-matching <span class="pre">`have`</span>.

    example : x < |y| → x < y ∨ x < -y := by
      cases le_or_gt 0 y
      next h =>
        rw [abs_of_nonneg h]
        intro h; left; exact h
      next h =>
        rw [abs_of_neg h]
        intro h; right; exact h

    example : x < |y| → x < y ∨ x < -y := by
      match le_or_gt 0 y with
        | Or.inl h =>
          rw [abs_of_nonneg h]
          intro h; left; exact h
        | Or.inr h =>
          rw [abs_of_neg h]
          intro h; right; exact h

In the case of <span class="pre">`match`</span>, we need to use the full names <span class="pre">`Or.inl`</span> and <span class="pre">`Or.inr`</span> of the canonical ways to prove a disjunction. In this textbook, we will generally use <span class="pre">`rcases`</span> to split on the cases of a disjunction.

Try proving the triangle inequality using the first two theorems in the next snippet. They are given the same names they have in Mathlib.

    namespace MyAbs

    theorem le_abs_self (x : ℝ) : x ≤ |x| := by
      sorry

    theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
      sorry

    theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
      sorry

In case you enjoyed these (pun intended) and you want more practice with disjunction, try these.

    theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
      sorry

    theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
      sorry

You can also use <span class="pre">`rcases`</span> and <span class="pre">`rintro`</span> with nested disjunctions. When these result in a genuine case split with multiple goals, the patterns for each new goal are separated by a vertical bar.

    example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
      rcases lt_trichotomy x 0 with xlt | xeq | xgt
      · left
        exact xlt
      · contradiction
      · right; exact xgt

You can still nest patterns and use the <span class="pre">`rfl`</span> keyword to substitute equations:

    example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
      rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
      · rw [mul_assoc]
        apply dvd_mul_right
      · rw [mul_comm, mul_assoc]
        apply dvd_mul_right

See if you can prove the following with a single (long) line. Use <span class="pre">`rcases`</span> to unpack the hypotheses and split on cases, and use a semicolon and <span class="pre">`linarith`</span> to solve each branch.

    example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
      sorry

On the real numbers, an equation <span class="pre">`x`</span>` `<span class="pre">`*`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`0`</span> tells us that <span class="pre">`x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`0`</span> or <span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`0`</span>. In Mathlib, this fact is known as <span class="pre">`eq_zero_or_eq_zero_of_mul_eq_zero`</span>, and it is another nice example of how a disjunction can arise. See if you can use it to prove the following:

    example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
      sorry

    example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
      sorry

Remember that you can use the <span class="pre">`ring`</span> tactic to help with calculations.

In an arbitrary ring <span class="math notranslate nohighlight">\\R\\</span>, an element <span class="math notranslate nohighlight">\\x\\</span> such that <span class="math notranslate nohighlight">\\x y = 0\\</span> for some nonzero <span class="math notranslate nohighlight">\\y\\</span> is called a *left zero divisor*, an element <span class="math notranslate nohighlight">\\x\\</span> such that <span class="math notranslate nohighlight">\\y x = 0\\</span> for some nonzero <span class="math notranslate nohighlight">\\y\\</span> is called a *right zero divisor*, and an element that is either a left or right zero divisor is called simply a *zero divisor*. The theorem <span class="pre">`eq_zero_or_eq_zero_of_mul_eq_zero`</span> says that the real numbers have no nontrivial zero divisors. A commutative ring with this property is called an *integral domain*. Your proofs of the two theorems above should work equally well in any integral domain:

    variable {R : Type*} [CommRing R] [IsDomain R]
    variable (x y : R)

    example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
      sorry

    example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
      sorry

In fact, if you are careful, you can prove the first theorem without using commutativity of multiplication. In that case, it suffices to assume that <span class="pre">`R`</span> is a <span class="pre">`Ring`</span> instead of an <span class="pre">`CommRing`</span>.

Sometimes in a proof we want to split on cases depending on whether some statement is true or not. For any proposition <span class="pre">`P`</span>, we can use <span class="pre">`em`</span>` `<span class="pre">`P`</span>` `<span class="pre">`:`</span>` `<span class="pre">`P`</span>` `<span class="pre">`∨`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`P`</span>. The name <span class="pre">`em`</span> is short for “excluded middle.”

    example (P : Prop) : ¬¬P → P := by
      intro h
      cases em P
      · assumption
      · contradiction

Alternatively, you can use the <span class="pre">`by_cases`</span> tactic.

    example (P : Prop) : ¬¬P → P := by
      intro h
      by_cases h' : P
      · assumption
      contradiction

Notice that the <span class="pre">`by_cases`</span> tactic lets you specify a label for the hypothesis that is introduced in each branch, in this case, <span class="pre">`h'`</span>` `<span class="pre">`:`</span>` `<span class="pre">`P`</span> in one and <span class="pre">`h'`</span>` `<span class="pre">`:`</span>` `<span class="pre">`¬`</span>` `<span class="pre">`P`</span> in the other. If you leave out the label, Lean uses <span class="pre">`h`</span> by default. Try proving the following equivalence, using <span class="pre">`by_cases`</span> to establish one direction.

    example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
      sorry

<span id="id6"></span>

## <span class="section-number">3.6. </span>Sequences and Convergence<a href="#sequences-and-convergence" class="headerlink" title="Link to this heading"></a>

We now have enough skills at our disposal to do some real mathematics. In Lean, we can represent a sequence <span class="math notranslate nohighlight">\\s\_0, s\_1, s\_2, \ldots\\</span> of real numbers as a function <span class="pre">`s`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℕ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span>. Such a sequence is said to *converge* to a number <span class="math notranslate nohighlight">\\a\\</span> if for every <span class="math notranslate nohighlight">\\\varepsilon &gt; 0\\</span> there is a point beyond which the sequence remains within <span class="math notranslate nohighlight">\\\varepsilon\\</span> of <span class="math notranslate nohighlight">\\a\\</span>, that is, there is a number <span class="math notranslate nohighlight">\\N\\</span> such that for every <span class="math notranslate nohighlight">\\n \ge N\\</span>, <span class="math notranslate nohighlight">\\| s\_n - a | &lt; \varepsilon\\</span>. In Lean, we can render this as follows:

    def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
      ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

The notation <span class="pre">`∀`</span>` `<span class="pre">`ε`</span>` `<span class="pre">`>`</span>` `<span class="pre">`0,`</span>` `<span class="pre">`...`</span> is a convenient abbreviation for <span class="pre">`∀`</span>` `<span class="pre">`ε,`</span>` `<span class="pre">`ε`</span>` `<span class="pre">`>`</span>` `<span class="pre">`0`</span>` `<span class="pre">`→`</span>` `<span class="pre">`...`</span>, and, similarly, <span class="pre">`∀`</span>` `<span class="pre">`n`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`N,`</span>` `<span class="pre">`...`</span> abbreviates <span class="pre">`∀`</span>` `<span class="pre">`n,`</span>` `<span class="pre">`n`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`N`</span>` `<span class="pre">`→`</span>`  `<span class="pre">`...`</span>. And remember that <span class="pre">`ε`</span>` `<span class="pre">`>`</span>` `<span class="pre">`0`</span>, in turn, is defined as <span class="pre">`0`</span>` `<span class="pre">`<`</span>` `<span class="pre">`ε`</span>, and <span class="pre">`n`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`N`</span> is defined as <span class="pre">`N`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`n`</span>.

In this section, we’ll establish some properties of convergence. But first, we will discuss three tactics for working with equality that will prove useful. The first, the <span class="pre">`ext`</span> tactic, gives us a way of proving that two functions are equal. Let <span class="math notranslate nohighlight">\\f(x) = x + 1\\</span> and <span class="math notranslate nohighlight">\\g(x) = 1 + x\\</span> be functions from reals to reals. Then, of course, <span class="math notranslate nohighlight">\\f = g\\</span>, because they return the same value for every <span class="math notranslate nohighlight">\\x\\</span>. The <span class="pre">`ext`</span> tactic enables us to prove an equation between functions by proving that their values are the same at all the values of their arguments.

    example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
      ext
      ring

We’ll see later that <span class="pre">`ext`</span> is actually more general, and also one can specify the name of the variables that appear. For instance you can try to replace <span class="pre">`ext`</span> with <span class="pre">`ext`</span>` `<span class="pre">`u`</span>` `<span class="pre">`v`</span> in the above proof. The second tactic, the <span class="pre">`congr`</span> tactic, allows us to prove an equation between two expressions by reconciling the parts that are different:

    example (a b : ℝ) : |a| = |a - b + b| := by
      congr
      ring

Here the <span class="pre">`congr`</span> tactic peels off the <span class="pre">`abs`</span> on each side, leaving us to prove <span class="pre">`a`</span>` `<span class="pre">`=`</span>` `<span class="pre">`a`</span>` `<span class="pre">`-`</span>` `<span class="pre">`b`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b`</span>.

Finally, the <span class="pre">`convert`</span> tactic is used to apply a theorem to a goal when the conclusion of the theorem doesn’t quite match. For example, suppose we want to prove <span class="pre">`a`</span>` `<span class="pre">`<`</span>` `<span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span> from <span class="pre">`1`</span>` `<span class="pre">`<`</span>` `<span class="pre">`a`</span>. A theorem in the library, <span class="pre">`mul_lt_mul_right`</span>, will let us prove <span class="pre">`1`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span>` `<span class="pre">`<`</span>` `<span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span>. One possibility is to work backwards and rewrite the goal so that it has that form. Instead, the <span class="pre">`convert`</span> tactic lets us apply the theorem as it is, and leaves us with the task of proving the equations that are needed to make the goal match.

    example {a : ℝ} (h : 1 < a) : a < a * a := by
      convert (mul_lt_mul_right _).2 h
      · rw [one_mul]
      exact lt_trans zero_lt_one h

This example illustrates another useful trick: when we apply an expression with an underscore and Lean can’t fill it in for us automatically, it simply leaves it for us as another goal.

The following shows that any constant sequence <span class="math notranslate nohighlight">\\a, a, a, \ldots\\</span> converges.

    theorem convergesTo_const (a : ℝ) : ConvergesTo (fun x : ℕ ↦ a) a := by
      intro ε εpos
      use 0
      intro n nge
      rw [sub_self, abs_zero]
      apply εpos

Lean has a tactic, <span class="pre">`simp`</span>, which can often save you the trouble of carrying out steps like <span class="pre">`rw`</span>` `<span class="pre">`[sub_self,`</span>` `<span class="pre">`abs_zero]`</span> by hand. We will tell you more about it soon.

For a more interesting theorem, let’s show that if <span class="pre">`s`</span> converges to <span class="pre">`a`</span> and <span class="pre">`t`</span> converges to <span class="pre">`b`</span>, then <span class="pre">`fun`</span>` `<span class="pre">`n`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`s`</span>` `<span class="pre">`n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`t`</span>` `<span class="pre">`n`</span> converges to <span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b`</span>. It is helpful to have a clear pen-and-paper proof in mind before you start writing a formal one. Given <span class="pre">`ε`</span> greater than <span class="pre">`0`</span>, the idea is to use the hypotheses to obtain an <span class="pre">`Ns`</span> such that beyond that point, <span class="pre">`s`</span> is within <span class="pre">`ε`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span> of <span class="pre">`a`</span>, and an <span class="pre">`Nt`</span> such that beyond that point, <span class="pre">`t`</span> is within <span class="pre">`ε`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span> of <span class="pre">`b`</span>. Then, whenever <span class="pre">`n`</span> is greater than or equal to the maximum of <span class="pre">`Ns`</span> and <span class="pre">`Nt`</span>, the sequence <span class="pre">`fun`</span>` `<span class="pre">`n`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`s`</span>` `<span class="pre">`n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`t`</span>` `<span class="pre">`n`</span> should be within <span class="pre">`ε`</span> of <span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b`</span>. The following example begins to implement this strategy. See if you can finish it off.

    theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
          (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
        ConvergesTo (fun n ↦ s n + t n) (a + b) := by
      intro ε εpos
      dsimp -- this line is not needed but cleans up the goal a bit.
      have ε2pos : 0 < ε / 2 := by linarith
      rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
      rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
      use max Ns Nt
      sorry

As hints, you can use <span class="pre">`le_of_max_le_left`</span> and <span class="pre">`le_of_max_le_right`</span>, and <span class="pre">`norm_num`</span> can prove <span class="pre">`ε`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span>` `<span class="pre">`+`</span>` `<span class="pre">`ε`</span>` `<span class="pre">`/`</span>` `<span class="pre">`2`</span>` `<span class="pre">`=`</span>` `<span class="pre">`ε`</span>. Also, it is helpful to use the <span class="pre">`congr`</span> tactic to show that <span class="pre">`|s`</span>` `<span class="pre">`n`</span>` `<span class="pre">`+`</span>` `<span class="pre">`t`</span>` `<span class="pre">`n`</span>` `<span class="pre">`-`</span>` `<span class="pre">`(a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b)|`</span> is equal to <span class="pre">`|(s`</span>` `<span class="pre">`n`</span>` `<span class="pre">`-`</span>` `<span class="pre">`a)`</span>` `<span class="pre">`+`</span>` `<span class="pre">`(t`</span>` `<span class="pre">`n`</span>` `<span class="pre">`-`</span>` `<span class="pre">`b)|,`</span> since then you can use the triangle inequality. Notice that we marked all the variables <span class="pre">`s`</span>, <span class="pre">`t`</span>, <span class="pre">`a`</span>, and <span class="pre">`b`</span> implicit because they can be inferred from the hypotheses.

Proving the same theorem with multiplication in place of addition is tricky. We will get there by proving some auxiliary statements first. See if you can also finish off the next proof, which shows that if <span class="pre">`s`</span> converges to <span class="pre">`a`</span>, then <span class="pre">`fun`</span>` `<span class="pre">`n`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`c`</span>` `<span class="pre">`*`</span>` `<span class="pre">`s`</span>` `<span class="pre">`n`</span> converges to <span class="pre">`c`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span>. It is helpful to split into cases depending on whether <span class="pre">`c`</span> is equal to zero or not. We have taken care of the zero case, and we have left you to prove the result with the extra assumption that <span class="pre">`c`</span> is nonzero.

    theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
        ConvergesTo (fun n ↦ c * s n) (c * a) := by
      by_cases h : c = 0
      · convert convergesTo_const 0
        · rw [h]
          ring
        rw [h]
        ring
      have acpos : 0 < |c| := abs_pos.mpr h
      sorry

The next theorem is also independently interesting: it shows that a convergent sequence is eventually bounded in absolute value. We have started you off; see if you can finish it.

    theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
        ∃ N b, ∀ n, N ≤ n → |s n| < b := by
      rcases cs 1 zero_lt_one with ⟨N, h⟩
      use N, |a| + 1
      sorry

In fact, the theorem could be strengthened to assert that there is a bound <span class="pre">`b`</span> that holds for all values of <span class="pre">`n`</span>. But this version is strong enough for our purposes, and we will see at the end of this section that it holds more generally.

The next lemma is auxiliary: we prove that if <span class="pre">`s`</span> converges to <span class="pre">`a`</span> and <span class="pre">`t`</span> converges to <span class="pre">`0`</span>, then <span class="pre">`fun`</span>` `<span class="pre">`n`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`s`</span>` `<span class="pre">`n`</span>` `<span class="pre">`*`</span>` `<span class="pre">`t`</span>` `<span class="pre">`n`</span> converges to <span class="pre">`0`</span>. To do so, we use the previous theorem to find a <span class="pre">`B`</span> that bounds <span class="pre">`s`</span> beyond some point <span class="pre">`N₀`</span>. See if you can understand the strategy we have outlined and finish the proof.

    theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
        ConvergesTo (fun n ↦ s n * t n) 0 := by
      intro ε εpos
      dsimp
      rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
      have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
      have pos₀ : ε / B > 0 := div_pos εpos Bpos
      rcases ct _ pos₀ with ⟨N₁, h₁⟩
      sorry

If you have made it this far, congratulations! We are now within striking distance of our theorem. The following proof finishes it off.

    theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
          (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
        ConvergesTo (fun n ↦ s n * t n) (a * b) := by
      have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
        apply aux cs
        convert convergesTo_add ct (convergesTo_const (-b))
        ring
      have := convergesTo_add h₁ (convergesTo_mul_const b cs)
      convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
      · ext; ring
      ring

For another challenging exercise, try filling out the following sketch of a proof that limits are unique. (If you are feeling bold, you can delete the proof sketch and try proving it from scratch.)

    theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
          (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
        a = b := by
      by_contra abne
      have : |a - b| > 0 := by sorry
      let ε := |a - b| / 2
      have εpos : ε > 0 := by
        change |a - b| / 2 > 0
        linarith
      rcases sa ε εpos with ⟨Na, hNa⟩
      rcases sb ε εpos with ⟨Nb, hNb⟩
      let N := max Na Nb
      have absa : |s N - a| < ε := by sorry
      have absb : |s N - b| < ε := by sorry
      have : |a - b| < |a - b| := by sorry
      exact lt_irrefl _ this

We close the section with the observation that our proofs can be generalized. For example, the only properties that we have used of the natural numbers is that their structure carries a partial order with <span class="pre">`min`</span> and <span class="pre">`max`</span>. You can check that everything still works if you replace <span class="pre">`ℕ`</span> everywhere by any linear order <span class="pre">`α`</span>:

    variable {α : Type*} [LinearOrder α]

    def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
      ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

In <a href="C11_Topology.html#filters" class="reference internal"><span class="std std-numref">Section 11.1</span></a>, we will see that Mathlib has mechanisms for dealing with convergence in vastly more general terms, not only abstracting away particular features of the domain and codomain, but also abstracting over different types of convergence.
