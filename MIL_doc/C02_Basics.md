<span id="id1"></span>

# <span class="section-number">2. </span>Basics<a href="#basics" class="headerlink" title="Link to this heading"></a>

This chapter is designed to introduce you to the nuts and bolts of mathematical reasoning in Lean: calculating, applying lemmas and theorems, and reasoning about generic structures.

## <span class="section-number">2.1. </span>Calculating<a href="#calculating" class="headerlink" title="Link to this heading"></a>

We generally learn to carry out mathematical calculations without thinking of them as proofs. But when we justify each step in a calculation, as Lean requires us to do, the net result is a proof that the left-hand side of the calculation is equal to the right-hand side.

In Lean, stating a theorem is tantamount to stating a goal, namely, the goal of proving the theorem. Lean provides the rewriting tactic <span class="pre">`rw`</span>, to replace the left-hand side of an identity by the right-hand side in the goal. If <span class="pre">`a`</span>, <span class="pre">`b`</span>, and <span class="pre">`c`</span> are real numbers, <span class="pre">`mul_assoc`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`c`</span> is the identity <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`b`</span>` `<span class="pre">`*`</span>` `<span class="pre">`c`</span>` `<span class="pre">`=`</span>` `<span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`(b`</span>` `<span class="pre">`*`</span>` `<span class="pre">`c)`</span> and <span class="pre">`mul_comm`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span> is the identity <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`b`</span>` `<span class="pre">`=`</span>` `<span class="pre">`b`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span>. Lean provides automation that generally eliminates the need to refer the facts like these explicitly, but they are useful for the purposes of illustration. In Lean, multiplication associates to the left, so the left-hand side of <span class="pre">`mul_assoc`</span> could also be written <span class="pre">`(a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`b)`</span>` `<span class="pre">`*`</span>` `<span class="pre">`c`</span>. However, it is generally good style to be mindful of Lean’s notational conventions and leave out parentheses when Lean does as well.

Let’s try out <span class="pre">`rw`</span>.

    example (a b c : ℝ) : a * b * c = b * (a * c) := by
      rw [mul_comm a b]
      rw [mul_assoc b a c]

The <span class="pre">`import`</span> lines at the beginning of the associated examples file import the theory of the real numbers from Mathlib, as well as useful automation. For the sake of brevity, we generally suppress information like this in the textbook.

You are welcome to make changes to see what happens. You can type the <span class="pre">`ℝ`</span> character as <span class="pre">`\R`</span> or <span class="pre">`\real`</span> in VS Code. The symbol doesn’t appear until you hit space or the tab key. If you hover over a symbol when reading a Lean file, VS Code will show you the syntax that can be used to enter it. If you are curious to see all available abbreviations, you can hit Ctrl-Shift-P and then type abbreviations to get access to the <span class="pre">`Lean`</span>` `<span class="pre">`4:`</span>` `<span class="pre">`Show`</span>` `<span class="pre">`Unicode`</span>` `<span class="pre">`Input`</span>` `<span class="pre">`Abbreviations`</span> command. If your keyboard does not have an easily accessible backslash, you can change the leading character by changing the <span class="pre">`lean4.input.leader`</span> setting.

When a cursor is in the middle of a tactic proof, Lean reports on the current *proof state* in the *Lean Infoview* window. As you move your cursor past each step of the proof, you can see the state change. A typical proof state in Lean might look as follows:

    1 goal
    x y : ℕ,
    h₁ : Prime x,
    h₂ : ¬Even x,
    h₃ : y > x
    ⊢ y ≥ 4

The lines before the one that begins with <span class="pre">`⊢`</span> denote the *context*: they are the objects and assumptions currently at play. In this example, these include two objects, <span class="pre">`x`</span> and <span class="pre">`y`</span>, each a natural number. They also include three assumptions, labelled <span class="pre">`h₁`</span>, <span class="pre">`h₂`</span>, and <span class="pre">`h₃`</span>. In Lean, everything in a context is labelled with an identifier. You can type these subscripted labels as <span class="pre">`h\1`</span>, <span class="pre">`h\2`</span>, and <span class="pre">`h\3`</span>, but any legal identifiers would do: you can use <span class="pre">`h1`</span>, <span class="pre">`h2`</span>, <span class="pre">`h3`</span> instead, or <span class="pre">`foo`</span>, <span class="pre">`bar`</span>, and <span class="pre">`baz`</span>. The last line represents the *goal*, that is, the fact to be proved. Sometimes people use *target* for the fact to be proved, and *goal* for the combination of the context and the target. In practice, the intended meaning is usually clear.

Try proving these identities, in each case replacing <span class="pre">`sorry`</span> by a tactic proof. With the <span class="pre">`rw`</span> tactic, you can use a left arrow (<span class="pre">`\l`</span>) to reverse an identity. For example, <span class="pre">`rw`</span>` `<span class="pre">`[←`</span>` `<span class="pre">`mul_assoc`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`c]`</span> replaces <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`(b`</span>` `<span class="pre">`*`</span>` `<span class="pre">`c)`</span> by <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`b`</span>` `<span class="pre">`*`</span>` `<span class="pre">`c`</span> in the current goal. Note that the left-pointing arrow refers to going from right to left in the identity provided by <span class="pre">`mul_assoc`</span>, it has nothing to do with the left or right side of the goal.

    example (a b c : ℝ) : c * b * a = b * (a * c) := by
      sorry

    example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
      sorry

You can also use identities like <span class="pre">`mul_assoc`</span> and <span class="pre">`mul_comm`</span> without arguments. In this case, the rewrite tactic tries to match the left-hand side with an expression in the goal, using the first pattern it finds.

    example (a b c : ℝ) : a * b * c = b * c * a := by
      rw [mul_assoc]
      rw [mul_comm]

You can also provide *partial* information. For example, <span class="pre">`mul_comm`</span>` `<span class="pre">`a`</span> matches any pattern of the form <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`?`</span> and rewrites it to <span class="pre">`?`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span>. Try doing the first of these examples without providing any arguments at all, and the second with only one argument.

    example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
      sorry

    example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
      sorry

You can also use <span class="pre">`rw`</span> with facts from the local context.

    example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
      rw [h']
      rw [← mul_assoc]
      rw [h]
      rw [mul_assoc]

Try these, using the theorem <span class="pre">`sub_self`</span> for the second one:

    example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
      sorry

    example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
      sorry

Multiple rewrite commands can be carried out with a single command, by listing the relevant identities separated by commas inside the square brackets.

    example (a b c d e f : ℝ) (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
      rw [h', ← mul_assoc, h, mul_assoc]

You still see the incremental progress by placing the cursor after a comma in any list of rewrites.

Another trick is that we can declare variables once and for all outside an example or theorem. Lean then includes them automatically.

    variable (a b c d e f : ℝ)

    example (h : a * b = c * d) (h' : e = f) : a * (b * e) = c * (d * f) := by
      rw [h', ← mul_assoc, h, mul_assoc]

Inspection of the tactic state at the beginning of the above proof reveals that Lean indeed included all variables. We can delimit the scope of the declaration by putting it in a <span class="pre">`section`</span>` `<span class="pre">`...`</span>` `<span class="pre">`end`</span> block. Finally, recall from the introduction that Lean provides us with a command to determine the type of an expression:

    section
    variable (a b c : ℝ)

    #check a
    #check a + b
    #check (a : ℝ)
    #check mul_comm a b
    #check (mul_comm a b : a * b = b * a)
    #check mul_assoc c a b
    #check mul_comm a
    #check mul_comm

    end

The <span class="pre">`#check`</span> command works for both objects and facts. In response to the command <span class="pre">`#check`</span>` `<span class="pre">`a`</span>, Lean reports that <span class="pre">`a`</span> has type <span class="pre">`ℝ`</span>. In response to the command <span class="pre">`#check`</span>` `<span class="pre">`mul_comm`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>, Lean reports that <span class="pre">`mul_comm`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span> is a proof of the fact <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`b`</span>` `<span class="pre">`=`</span>` `<span class="pre">`b`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span>. The command <span class="pre">`#check`</span>` `<span class="pre">`(a`</span>` `<span class="pre">`:`</span>` `<span class="pre">`ℝ)`</span> states our expectation that the type of <span class="pre">`a`</span> is <span class="pre">`ℝ`</span>, and Lean will raise an error if that is not the case. We will explain the output of the last three <span class="pre">`#check`</span> commands later, but in the meanwhile, you can take a look at them, and experiment with some <span class="pre">`#check`</span> commands of your own.

Let’s try some more examples. The theorem <span class="pre">`two_mul`</span>` `<span class="pre">`a`</span> says that <span class="pre">`2`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span>` `<span class="pre">`=`</span>` `<span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`a`</span>. The theorems <span class="pre">`add_mul`</span> and <span class="pre">`mul_add`</span> express the distributivity of multiplication over addition, and the theorem <span class="pre">`add_assoc`</span> expresses the associativity of addition. Use the <span class="pre">`#check`</span> command to see the precise statements.

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
      rw [mul_add, add_mul, add_mul]
      rw [← add_assoc, add_assoc (a * a)]
      rw [mul_comm b a, ← two_mul]

Whereas it is possible to figure out what is going on in this proof by stepping through it in the editor, it is hard to read on its own. Lean provides a more structured way of writing proofs like this using the <span class="pre">`calc`</span> keyword.

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
      calc
        (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
          rw [mul_add, add_mul, add_mul]
        _ = a * a + (b * a + a * b) + b * b := by
          rw [← add_assoc, add_assoc (a * a)]
        _ = a * a + 2 * (a * b) + b * b := by
          rw [mul_comm b a, ← two_mul]

Notice that the proof does *not* begin with <span class="pre">`by`</span>: an expression that begins with <span class="pre">`calc`</span> is a *proof term*. A <span class="pre">`calc`</span> expression can also be used inside a tactic proof, but Lean interprets it as the instruction to use the resulting proof term to solve the goal. The <span class="pre">`calc`</span> syntax is finicky: the underscores and justification have to be in the format indicated above. Lean uses indentation to determine things like where a block of tactics or a <span class="pre">`calc`</span> block begins and ends; try changing the indentation in the proof above to see what happens.

One way to write a <span class="pre">`calc`</span> proof is to outline it first using the <span class="pre">`sorry`</span> tactic for justification, make sure Lean accepts the expression modulo these, and then justify the individual steps using tactics.

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b :=
      calc
        (a + b) * (a + b) = a * a + b * a + (a * b + b * b) := by
          sorry
        _ = a * a + (b * a + a * b) + b * b := by
          sorry
        _ = a * a + 2 * (a * b) + b * b := by
          sorry

Try proving the following identity using both a pure <span class="pre">`rw`</span> proof and a more structured <span class="pre">`calc`</span> proof:

    example : (a + b) * (c + d) = a * c + a * d + b * c + b * d := by
      sorry

The following exercise is a little more challenging. You can use the theorems listed underneath.

    example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
      sorry

    #check pow_two a
    #check mul_sub a b c
    #check add_mul a b c
    #check add_sub a b c
    #check sub_sub a b c
    #check add_zero a

We can also perform rewriting in an assumption in the context. For example, <span class="pre">`rw`</span>` `<span class="pre">`[mul_comm`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b]`</span>` `<span class="pre">`at`</span>` `<span class="pre">`hyp`</span> replaces <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`b`</span> by <span class="pre">`b`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span> in the assumption <span class="pre">`hyp`</span>.

    example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
      rw [hyp'] at hyp
      rw [mul_comm d a] at hyp
      rw [← two_mul (a * d)] at hyp
      rw [← mul_assoc 2 a d] at hyp
      exact hyp

In the last step, the <span class="pre">`exact`</span> tactic can use <span class="pre">`hyp`</span> to solve the goal because at that point <span class="pre">`hyp`</span> matches the goal exactly.

We close this section by noting that Mathlib provides a useful bit of automation with a <span class="pre">`ring`</span> tactic, which is designed to prove identities in any commutative ring as long as they follow purely from the ring axioms, without using any local assumption.

    example : c * b * a = b * (a * c) := by
      ring

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
      ring

    example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
      ring

    example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
      rw [hyp, hyp']
      ring

The <span class="pre">`ring`</span> tactic is imported indirectly when we import <span class="pre">`Mathlib.Data.Real.Basic`</span>, but we will see in the next section that it can be used for calculations on structures other than the real numbers. It can be imported explicitly with the command <span class="pre">`import`</span>` `<span class="pre">`Mathlib.Tactic`</span>. We will see there are similar tactics for other common kind of algebraic structures.

There is a variation of <span class="pre">`rw`</span> called <span class="pre">`nth_rw`</span> that allows you to replace only particular instances of an expression in the goal. Possible matches are enumerated starting with 1, so in the following example, <span class="pre">`nth_rw`</span>` `<span class="pre">`2`</span>` `<span class="pre">`[h]`</span> replaces the second occurrence of <span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b`</span> with <span class="pre">`c`</span>.

    example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
      nth_rw 2 [h]
      rw [add_mul]

<span id="id2"></span>

## <span class="section-number">2.2. </span>Proving Identities in Algebraic Structures<a href="#proving-identities-in-algebraic-structures" class="headerlink" title="Link to this heading"></a>

Mathematically, a ring consists of a collection of objects, <span class="math notranslate nohighlight">\\R\\</span>, operations <span class="math notranslate nohighlight">\\+\\</span> <span class="math notranslate nohighlight">\\\times\\</span>, and constants <span class="math notranslate nohighlight">\\0\\</span> and <span class="math notranslate nohighlight">\\1\\</span>, and an operation <span class="math notranslate nohighlight">\\x \mapsto -x\\</span> such that:

- <span class="math notranslate nohighlight">\\R\\</span> with <span class="math notranslate nohighlight">\\+\\</span> is an *abelian group*, with <span class="math notranslate nohighlight">\\0\\</span> as the additive identity and negation as inverse.

- Multiplication is associative with identity <span class="math notranslate nohighlight">\\1\\</span>, and multiplication distributes over addition.

In Lean, the collection of objects is represented as a *type*, <span class="pre">`R`</span>. The ring axioms are as follows:

    variable (R : Type*) [Ring R]

    #check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
    #check (add_comm : ∀ a b : R, a + b = b + a)
    #check (zero_add : ∀ a : R, 0 + a = a)
    #check (neg_add_cancel : ∀ a : R, -a + a = 0)
    #check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
    #check (mul_one : ∀ a : R, a * 1 = a)
    #check (one_mul : ∀ a : R, 1 * a = a)
    #check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
    #check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

You will learn more about the square brackets in the first line later, but for the time being, suffice it to say that the declaration gives us a type, <span class="pre">`R`</span>, and a ring structure on <span class="pre">`R`</span>. Lean then allows us to use generic ring notation with elements of <span class="pre">`R`</span>, and to make use of a library of theorems about rings.

The names of some of the theorems should look familiar: they are exactly the ones we used to calculate with the real numbers in the last section. Lean is good not only for proving things about concrete mathematical structures like the natural numbers and the integers, but also for proving things about abstract structures, characterized axiomatically, like rings. Moreover, Lean supports *generic reasoning* about both abstract and concrete structures, and can be trained to recognize appropriate instances. So any theorem about rings can be applied to concrete rings like the integers, <span class="pre">`ℤ`</span>, the rational numbers, <span class="pre">`ℚ`</span>, and the complex numbers <span class="pre">`ℂ`</span>. It can also be applied to any instance of an abstract structure that extends rings, such as any ordered ring or any field.

Not all important properties of the real numbers hold in an arbitrary ring, however. For example, multiplication on the real numbers is commutative, but that does not hold in general. If you have taken a course in linear algebra, you will recognize that, for every <span class="math notranslate nohighlight">\\n\\</span>, the <span class="math notranslate nohighlight">\\n\\</span> by <span class="math notranslate nohighlight">\\n\\</span> matrices of real numbers form a ring in which commutativity usually fails. If we declare <span class="pre">`R`</span> to be a *commutative* ring, in fact, all the theorems in the last section continue to hold when we replace <span class="pre">`ℝ`</span> by <span class="pre">`R`</span>.

    variable (R : Type*) [CommRing R]
    variable (a b c d : R)

    example : c * b * a = b * (a * c) := by ring

    example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

    example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

    example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
      rw [hyp, hyp']
      ring

We leave it to you to check that all the other proofs go through unchanged. Notice that when a proof is short, like <span class="pre">`by`</span>` `<span class="pre">`ring`</span> or <span class="pre">`by`</span>` `<span class="pre">`linarith`</span> or <span class="pre">`by`</span>` `<span class="pre">`sorry`</span>, it is common (and permissible) to put it on the same line as the <span class="pre">`by`</span>. Good proof-writing style should strike a balance between concision and readability.

The goal of this section is to strengthen the skills you have developed in the last section and apply them to reasoning axiomatically about rings. We will start with the axioms listed above, and use them to derive other facts. Most of the facts we prove are already in Mathlib. We will give the versions we prove the same names to help you learn the contents of the library as well as the naming conventions.

Lean provides an organizational mechanism similar to those used in programming languages: when a definition or theorem <span class="pre">`foo`</span> is introduced in a *namespace* <span class="pre">`bar`</span>, its full name is <span class="pre">`bar.foo`</span>. The command <span class="pre">`open`</span>` `<span class="pre">`bar`</span> later *opens* the namespace, which allows us to use the shorter name <span class="pre">`foo`</span>. To avoid errors due to name clashes, in the next example we put our versions of the library theorems in a new namespace called <span class="pre">`MyRing.`</span>

The next example shows that we do not need <span class="pre">`add_zero`</span> or <span class="pre">`add_neg_cancel`</span> as ring axioms, because they follow from the other axioms.

    namespace MyRing
    variable {R : Type*} [Ring R]

    theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

    theorem add_neg_cancel (a : R) : a + -a = 0 := by rw [add_comm, neg_add_cancel]

    #check MyRing.add_zero
    #check add_zero

    end MyRing

The net effect is that we can temporarily reprove a theorem in the library, and then go on using the library version after that. But don’t cheat! In the exercises that follow, take care to use only the general facts about rings that we have proved earlier in this section.

(If you are paying careful attention, you may have noticed that we changed the round brackets in <span class="pre">`(R`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type*)`</span> for curly brackets in <span class="pre">`{R`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type*}`</span>. This declares <span class="pre">`R`</span> to be an *implicit argument*. We will explain what this means in a moment, but don’t worry about it in the meanwhile.)

Here is a useful theorem:

    theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
      rw [← add_assoc, neg_add_cancel, zero_add]

Prove the companion version:

    theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
      sorry

Use these to prove the following:

    theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
      sorry

    theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
      sorry

With enough planning, you can do each of them with three rewrites.

We will now explain the use of the curly braces. Imagine you are in a situation where you have <span class="pre">`a`</span>, <span class="pre">`b`</span>, and <span class="pre">`c`</span> in your context, as well as a hypothesis <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`b`</span>` `<span class="pre">`=`</span>` `<span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`c`</span>, and you would like to draw the conclusion <span class="pre">`b`</span>` `<span class="pre">`=`</span>` `<span class="pre">`c`</span>. In Lean, you can apply a theorem to hypotheses and facts just the same way that you can apply them to objects, so you might think that <span class="pre">`add_left_cancel`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`c`</span>` `<span class="pre">`h`</span> is a proof of the fact <span class="pre">`b`</span>` `<span class="pre">`=`</span>` `<span class="pre">`c`</span>. But notice that explicitly writing <span class="pre">`a`</span>, <span class="pre">`b`</span>, and <span class="pre">`c`</span> is redundant, because the hypothesis <span class="pre">`h`</span> makes it clear that those are the objects we have in mind. In this case, typing a few extra characters is not onerous, but if we wanted to apply <span class="pre">`add_left_cancel`</span> to more complicated expressions, writing them would be tedious. In cases like these, Lean allows us to mark arguments as *implicit*, meaning that they are supposed to be left out and inferred by other means, such as later arguments and hypotheses. The curly brackets in <span class="pre">`{a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`c`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R}`</span> do exactly that. So, given the statement of the theorem above, the correct expression is simply <span class="pre">`add_left_cancel`</span>` `<span class="pre">`h`</span>.

To illustrate, let us show that <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`0`</span>` `<span class="pre">`=`</span>` `<span class="pre">`0`</span> follows from the ring axioms.

    theorem mul_zero (a : R) : a * 0 = 0 := by
      have h : a * 0 + a * 0 = a * 0 + 0 := by
        rw [← mul_add, add_zero, add_zero]
      rw [add_left_cancel h]

We have used a new trick! If you step through the proof, you can see what is going on. The <span class="pre">`have`</span> tactic introduces a new goal, <span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`0`</span>` `<span class="pre">`+`</span>` `<span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`0`</span>` `<span class="pre">`=`</span>` `<span class="pre">`a`</span>` `<span class="pre">`*`</span>` `<span class="pre">`0`</span>` `<span class="pre">`+`</span>` `<span class="pre">`0`</span>, with the same context as the original goal. The fact that the next line is indented indicates that Lean is expecting a block of tactics that serves to prove this new goal. The indentation therefore promotes a modular style of proof: the indented subproof establishes the goal that was introduced by the <span class="pre">`have`</span>. After that, we are back to proving the original goal, except a new hypothesis <span class="pre">`h`</span> has been added: having proved it, we are now free to use it. At this point, the goal is exactly the result of <span class="pre">`add_left_cancel`</span>` `<span class="pre">`h`</span>.

We could equally well have closed the proof with <span class="pre">`apply`</span>` `<span class="pre">`add_left_cancel`</span>` `<span class="pre">`h`</span> or <span class="pre">`exact`</span>` `<span class="pre">`add_left_cancel`</span>` `<span class="pre">`h`</span>. The <span class="pre">`exact`</span> tactic takes as argument a proof term which completely proves the current goal, without creating any new goal. The <span class="pre">`apply`</span> tactic is a variant whose argument is not necessarily a complete proof. The missing pieces are either inferred automatically by Lean or become new goals to prove. While the <span class="pre">`exact`</span> tactic is technically redundant since it is strictly less powerful than <span class="pre">`apply`</span>, it makes proof scripts slightly clearer to human readers and easier to maintain when the library evolves.

Remember that multiplication is not assumed to be commutative, so the following theorem also requires some work.

    theorem zero_mul (a : R) : 0 * a = 0 := by
      sorry

By now, you should also be able replace each <span class="pre">`sorry`</span> in the next exercise with a proof, still using only facts about rings that we have established in this section.

    theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
      sorry

    theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
      sorry

    theorem neg_zero : (-0 : R) = 0 := by
      apply neg_eq_of_add_eq_zero
      rw [add_zero]

    theorem neg_neg (a : R) : - -a = a := by
      sorry

We had to use the annotation <span class="pre">`(-0`</span>` `<span class="pre">`:`</span>` `<span class="pre">`R)`</span> instead of <span class="pre">`0`</span> in the third theorem because without specifying <span class="pre">`R`</span> it is impossible for Lean to infer which <span class="pre">`0`</span> we have in mind, and by default it would be interpreted as a natural number.

In Lean, subtraction in a ring is provably equal to addition of the additive inverse.

    example (a b : R) : a - b = a + -b :=
      sub_eq_add_neg a b

On the real numbers, it is *defined* that way:

    example (a b : ℝ) : a - b = a + -b :=
      rfl

    example (a b : ℝ) : a - b = a + -b := by
      rfl

The proof term <span class="pre">`rfl`</span> is short for “reflexivity”. Presenting it as a proof of <span class="pre">`a`</span>` `<span class="pre">`-`</span>` `<span class="pre">`b`</span>` `<span class="pre">`=`</span>` `<span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`-b`</span> forces Lean to unfold the definition and recognize both sides as being the same. The <span class="pre">`rfl`</span> tactic does the same. This is an instance of what is known as a *definitional equality* in Lean’s underlying logic. This means that not only can one rewrite with <span class="pre">`sub_eq_add_neg`</span> to replace <span class="pre">`a`</span>` `<span class="pre">`-`</span>` `<span class="pre">`b`</span>` `<span class="pre">`=`</span>` `<span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`-b`</span>, but in some contexts, when dealing with the real numbers, you can use the two sides of the equation interchangeably. For example, you now have enough information to prove the theorem <span class="pre">`self_sub`</span> from the last section:

    theorem self_sub (a : R) : a - a = 0 := by
      sorry

Show that you can prove this using <span class="pre">`rw`</span>, but if you replace the arbitrary ring <span class="pre">`R`</span> by the real numbers, you can also prove it using either <span class="pre">`apply`</span> or <span class="pre">`exact`</span>.

Lean knows that <span class="pre">`1`</span>` `<span class="pre">`+`</span>` `<span class="pre">`1`</span>` `<span class="pre">`=`</span>` `<span class="pre">`2`</span> holds in any ring. With a bit of effort, you can use that to prove the theorem <span class="pre">`two_mul`</span> from the last section:

    theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
      norm_num

    theorem two_mul (a : R) : 2 * a = a + a := by
      sorry

We close this section by noting that some of the facts about addition and negation that we established above do not need the full strength of the ring axioms, or even commutativity of addition. The weaker notion of a *group* can be axiomatized as follows:

    variable (A : Type*) [AddGroup A]

    #check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
    #check (zero_add : ∀ a : A, 0 + a = a)
    #check (neg_add_cancel : ∀ a : A, -a + a = 0)

It is conventional to use additive notation when the group operation is commutative, and multiplicative notation otherwise. So Lean defines a multiplicative version as well as the additive version (and also their abelian variants, <span class="pre">`AddCommGroup`</span> and <span class="pre">`CommGroup`</span>).

    variable {G : Type*} [Group G]

    #check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
    #check (one_mul : ∀ a : G, 1 * a = a)
    #check (inv_mul_cancel : ∀ a : G, a⁻¹ * a = 1)

If you are feeling cocky, try proving the following facts about groups, using only these axioms. You will need to prove a number of helper lemmas along the way. The proofs we have carried out in this section provide some hints.

    theorem mul_inv_cancel (a : G) : a * a⁻¹ = 1 := by
      sorry

    theorem mul_one (a : G) : a * 1 = a := by
      sorry

    theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
      sorry

Explicitly invoking those lemmas is tedious, so Mathlib provides tactics similar to ring in order to cover most uses: group is for non-commutative multiplicative groups, abel for abelian additive groups, and noncomm\_ring for non-commutative rings. It may seem odd that the algebraic structures are called Ring and CommRing while the tactics are named noncomm\_ring and ring. This is partly for historical reasons, but also for the convenience of using a shorter name for the tactic that deals with commutative rings, since it is used more often.

<span id="id3"></span>

## <span class="section-number">2.3. </span>Using Theorems and Lemmas<a href="#using-theorems-and-lemmas" class="headerlink" title="Link to this heading"></a>

Rewriting is great for proving equations, but what about other sorts of theorems? For example, how can we prove an inequality, like the fact that <span class="math notranslate nohighlight">\\a + e^b \le a + e^c\\</span> holds whenever <span class="math notranslate nohighlight">\\b \le c\\</span>? We have already seen that theorems can be applied to arguments and hypotheses, and that the <span class="pre">`apply`</span> and <span class="pre">`exact`</span> tactics can be used to solve goals. In this section, we will make good use of these tools.

Consider the library theorems <span class="pre">`le_refl`</span> and <span class="pre">`le_trans`</span>:

    #check (le_refl : ∀ a : ℝ, a ≤ a)
    #check (le_trans : a ≤ b → b ≤ c → a ≤ c)

As we explain in more detail in <a href="C03_Logic.html#implication-and-the-universal-quantifier" class="reference internal"><span class="std std-numref">Section 3.1</span></a>, the implicit parentheses in the statement of <span class="pre">`le_trans`</span> associate to the right, so it should be interpreted as <span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`b`</span>` `<span class="pre">`→`</span>` `<span class="pre">`(b`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`c`</span>` `<span class="pre">`→`</span>` `<span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`c)`</span>. The library designers have set the arguments <span class="pre">`a`</span>, <span class="pre">`b`</span> and <span class="pre">`c`</span> to <span class="pre">`le_trans`</span> implicit, so that Lean will *not* let you provide them explicitly (unless you really insist, as we will discuss later). Rather, it expects to infer them from the context in which they are used. For example, when hypotheses <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`b`</span> and <span class="pre">`h'`</span>` `<span class="pre">`:`</span>` `<span class="pre">`b`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`c`</span> are in the context, all the following work:

    variable (h : a ≤ b) (h' : b ≤ c)

    #check (le_refl : ∀ a : Real, a ≤ a)
    #check (le_refl a : a ≤ a)
    #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
    #check (le_trans h : b ≤ c → a ≤ c)
    #check (le_trans h h' : a ≤ c)

The <span class="pre">`apply`</span> tactic takes a proof of a general statement or implication, tries to match the conclusion with the current goal, and leaves the hypotheses, if any, as new goals. If the given proof matches the goal exactly (modulo *definitional* equality), you can use the <span class="pre">`exact`</span> tactic instead of <span class="pre">`apply`</span>. So, all of these work:

    example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
      apply le_trans
      · apply h₀
      · apply h₁

    example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
      apply le_trans h₀
      apply h₁

    example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
      le_trans h₀ h₁

    example (x : ℝ) : x ≤ x := by
      apply le_refl

    example (x : ℝ) : x ≤ x :=
      le_refl x

In the first example, applying <span class="pre">`le_trans`</span> creates two goals, and we use the dots to indicate where the proof of each begins. The dots are optional, but they serve to *focus* the goal: within the block introduced by the dot, only one goal is visible, and it must be completed before the end of the block. Here we end the first block by starting a new one with another dot. We could just as well have decreased the indentation. In the third example and in the last example, we avoid going into tactic mode entirely: <span class="pre">`le_trans`</span>` `<span class="pre">`h₀`</span>` `<span class="pre">`h₁`</span> and <span class="pre">`le_refl`</span>` `<span class="pre">`x`</span> are the proof terms we need.

Here are a few more library theorems:

    #check (le_refl : ∀ a, a ≤ a)
    #check (le_trans : a ≤ b → b ≤ c → a ≤ c)
    #check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
    #check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
    #check (lt_trans : a < b → b < c → a < c)

Use them together with <span class="pre">`apply`</span> and <span class="pre">`exact`</span> to prove the following:

    example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
      sorry

In fact, Lean has a tactic that does this sort of thing automatically:

    example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
      linarith

The <span class="pre">`linarith`</span> tactic is designed to handle *linear arithmetic*.

    example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
      linarith

In addition to equations and inequalities in the context, <span class="pre">`linarith`</span> will use additional inequalities that you pass as arguments. In the next example, <span class="pre">`exp_le_exp.mpr`</span>` `<span class="pre">`h'`</span> is a proof of <span class="pre">`exp`</span>` `<span class="pre">`b`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`exp`</span>` `<span class="pre">`c`</span>, as we will explain in a moment. Notice that, in Lean, we write <span class="pre">`f`</span>` `<span class="pre">`x`</span> to denote the application of a function <span class="pre">`f`</span> to the argument <span class="pre">`x`</span>, exactly the same way we write <span class="pre">`h`</span>` `<span class="pre">`x`</span> to denote the result of applying a fact or theorem <span class="pre">`h`</span> to the argument <span class="pre">`x`</span>. Parentheses are only needed for compound arguments, as in <span class="pre">`f`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`y)`</span>. Without the parentheses, <span class="pre">`f`</span>` `<span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`y`</span> would be parsed as <span class="pre">`(f`</span>` `<span class="pre">`x)`</span>` `<span class="pre">`+`</span>` `<span class="pre">`y`</span>.

    example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
      linarith [exp_le_exp.mpr h']

Here are some more theorems in the library that can be used to establish inequalities on the real numbers.

    #check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
    #check (exp_lt_exp : exp a < exp b ↔ a < b)
    #check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
    #check (log_lt_log : 0 < a → a < b → log a < log b)
    #check (add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d)
    #check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
    #check (add_le_add_right : a ≤ b → ∀ c, a + c ≤ b + c)
    #check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
    #check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)
    #check (add_lt_add_left : a < b → ∀ c, c + a < c + b)
    #check (add_lt_add_right : a < b → ∀ c, a + c < b + c)
    #check (add_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a + b)
    #check (add_pos : 0 < a → 0 < b → 0 < a + b)
    #check (add_pos_of_pos_of_nonneg : 0 < a → 0 ≤ b → 0 < a + b)
    #check (exp_pos : ∀ a, 0 < exp a)
    #check add_le_add_left

Some of the theorems, <span class="pre">`exp_le_exp`</span>, <span class="pre">`exp_lt_exp`</span> use a *bi-implication*, which represents the phrase “if and only if.” (You can type it in VS Code with <span class="pre">`\lr`</span> or <span class="pre">`\iff`</span>). We will discuss this connective in greater detail in the next chapter. Such a theorem can be used with <span class="pre">`rw`</span> to rewrite a goal to an equivalent one:

    example (h : a ≤ b) : exp a ≤ exp b := by
      rw [exp_le_exp]
      exact h

In this section, however, we will use the fact that if <span class="pre">`h`</span>` `<span class="pre">`:`</span>` `<span class="pre">`A`</span>` `<span class="pre">`↔`</span>` `<span class="pre">`B`</span> is such an equivalence, then <span class="pre">`h.mp`</span> establishes the forward direction, <span class="pre">`A`</span>` `<span class="pre">`→`</span>` `<span class="pre">`B`</span>, and <span class="pre">`h.mpr`</span> establishes the reverse direction, <span class="pre">`B`</span>` `<span class="pre">`→`</span>` `<span class="pre">`A`</span>. Here, <span class="pre">`mp`</span> stands for “modus ponens” and <span class="pre">`mpr`</span> stands for “modus ponens reverse.” You can also use <span class="pre">`h.1`</span> and <span class="pre">`h.2`</span> for <span class="pre">`h.mp`</span> and <span class="pre">`h.mpr`</span>, respectively, if you prefer. Thus the following proof works:

    example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
      apply add_lt_add_of_lt_of_le
      · apply add_lt_add_of_le_of_lt h₀
        apply exp_lt_exp.mpr h₁
      apply le_refl

The first line, <span class="pre">`apply`</span>` `<span class="pre">`add_lt_add_of_lt_of_le`</span>, creates two goals, and once again we use a dot to separate the proof of the first from the proof of the second.

Try the following examples on your own. The example in the middle shows you that the <span class="pre">`norm_num`</span> tactic can be used to solve concrete numeric goals.

    example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by sorry

    example : (0 : ℝ) < 1 := by norm_num

    example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
      have h₀ : 0 < 1 + exp a := by sorry
      apply log_le_log h₀
      sorry

From these examples, it should be clear that being able to find the library theorems you need constitutes an important part of formalization. There are a number of strategies you can use:

- You can browse Mathlib in its <a href="https://github.com/leanprover-community/mathlib4" class="reference external">GitHub repository</a>.

- You can use the API documentation on the Mathlib <a href="https://leanprover-community.github.io/mathlib4_docs/" class="reference external">web pages</a>.

- You can use Loogle &lt;https://loogle.lean-lang.org&gt; to search Lean and Mathlib definitions and theorems by patterns.

- You can rely on Mathlib naming conventions and Ctrl-space completion in the editor to guess a theorem name (or Cmd-space on a Mac keyboard). In Lean, a theorem named <span class="pre">`A_of_B_of_C`</span> establishes something of the form <span class="pre">`A`</span> from hypotheses of the form <span class="pre">`B`</span> and <span class="pre">`C`</span>, where <span class="pre">`A`</span>, <span class="pre">`B`</span>, and <span class="pre">`C`</span> approximate the way we might read the goals out loud. So a theorem establishing something like <span class="pre">`x`</span>` `<span class="pre">`+`</span>` `<span class="pre">`y`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`...`</span> will probably start with <span class="pre">`add_le`</span>. Typing <span class="pre">`add_le`</span> and hitting Ctrl-space will give you some helpful choices. Note that hitting Ctrl-space twice displays more information about the available completions.

- If you right-click on an existing theorem name in VS Code, the editor will show a menu with the option to jump to the file where the theorem is defined, and you can find similar theorems nearby.

- You can use the <span class="pre">`apply?`</span> tactic, which tries to find the relevant theorem in the library.

    example : 0 ≤ a ^ 2 := by
      -- apply?
      exact sq_nonneg a

To try out <span class="pre">`apply?`</span> in this example, delete the <span class="pre">`exact`</span> command and uncomment the previous line. Using these tricks, see if you can find what you need to do the next example:

    example (h : a ≤ b) : c - exp b ≤ c - exp a := by
      sorry

Using the same tricks, confirm that <span class="pre">`linarith`</span> instead of <span class="pre">`apply?`</span> can also finish the job.

Here is another example of an inequality:

    example : 2*a*b ≤ a^2 + b^2 := by
      have h : 0 ≤ a^2 - 2*a*b + b^2
      calc
        a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg

      calc
        2*a*b = 2*a*b + 0 := by ring
        _ ≤ 2*a*b + (a^2 - 2*a*b + b^2) := add_le_add (le_refl _) h
        _ = a^2 + b^2 := by ring

Mathlib tends to put spaces around binary operations like <span class="pre">`*`</span> and <span class="pre">`^`</span>, but in this example, the more compressed format increases readability. There are a number of things worth noticing. First, an expression <span class="pre">`s`</span>` `<span class="pre">`≥`</span>` `<span class="pre">`t`</span> is definitionally equivalent to <span class="pre">`t`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`s`</span>. In principle, this means one should be able to use them interchangeably. But some of Lean’s automation does not recognize the equivalence, so Mathlib tends to favor <span class="pre">`≤`</span> over <span class="pre">`≥`</span>. Second, we have used the <span class="pre">`ring`</span> tactic extensively. It is a real timesaver! Finally, notice that in the second line of the second <span class="pre">`calc`</span> proof, instead of writing <span class="pre">`by`</span>` `<span class="pre">`exact`</span>` `<span class="pre">`add_le_add`</span>` `<span class="pre">`(le_refl`</span>` `<span class="pre">`_)`</span>` `<span class="pre">`h`</span>, we can simply write the proof term <span class="pre">`add_le_add`</span>` `<span class="pre">`(le_refl`</span>` `<span class="pre">`_)`</span>` `<span class="pre">`h`</span>.

In fact, the only cleverness in the proof above is figuring out the hypothesis <span class="pre">`h`</span>. Once we have it, the second calculation involves only linear arithmetic, and <span class="pre">`linarith`</span> can handle it:

    example : 2*a*b ≤ a^2 + b^2 := by
      have h : 0 ≤ a^2 - 2*a*b + b^2
      calc
        a^2 - 2*a*b + b^2 = (a - b)^2 := by ring
        _ ≥ 0 := by apply pow_two_nonneg
      linarith

How nice! We challenge you to use these ideas to prove the following theorem. You can use the theorem <span class="pre">`abs_le'.mpr`</span>. You will also need the <span class="pre">`constructor`</span> tactic to split a conjunction to two goals; see <a href="C03_Logic.html#conjunction-and-biimplication" class="reference internal"><span class="std std-numref">Section 3.4</span></a>.

    example : |a*b| ≤ (a^2 + b^2)/2 := by
      sorry

    #check abs_le'.mpr

If you managed to solve this, congratulations! You are well on your way to becoming a master formalizer.

<span id="more-on-order-and-divisibility"></span>

## <span class="section-number">2.4. </span>More examples using apply and rw<a href="#more-examples-using-apply-and-rw" class="headerlink" title="Link to this heading"></a>

The <span class="pre">`min`</span> function on the real numbers is uniquely characterized by the following three facts:

    #check (min_le_left a b : min a b ≤ a)
    #check (min_le_right a b : min a b ≤ b)
    #check (le_min : c ≤ a → c ≤ b → c ≤ min a b)

Can you guess the names of the theorems that characterize <span class="pre">`max`</span> in a similar way?

Notice that we have to apply <span class="pre">`min`</span> to a pair of arguments <span class="pre">`a`</span> and <span class="pre">`b`</span> by writing <span class="pre">`min`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span> rather than <span class="pre">`min`</span>` `<span class="pre">`(a,`</span>` `<span class="pre">`b)`</span>. Formally, <span class="pre">`min`</span> is a function of type <span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span>. When we write a type like this with multiple arrows, the convention is that the implicit parentheses associate to the right, so the type is interpreted as <span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`(ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ)`</span>. The net effect is that if <span class="pre">`a`</span> and <span class="pre">`b`</span> have type <span class="pre">`ℝ`</span> then <span class="pre">`min`</span>` `<span class="pre">`a`</span> has type <span class="pre">`ℝ`</span>` `<span class="pre">`→`</span>` `<span class="pre">`ℝ`</span> and <span class="pre">`min`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span> has type <span class="pre">`ℝ`</span>, so <span class="pre">`min`</span> acts like a function of two arguments, as we expect. Handling multiple arguments in this way is known as *currying*, after the logician Haskell Curry.

The order of operations in Lean can also take some getting used to. Function application binds tighter than infix operations, so the expression <span class="pre">`min`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`+`</span>` `<span class="pre">`c`</span> is interpreted as <span class="pre">`(min`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b)`</span>` `<span class="pre">`+`</span>` `<span class="pre">`c`</span>. With time, these conventions will become second nature.

Using the theorem <span class="pre">`le_antisymm`</span>, we can show that two real numbers are equal if each is less than or equal to the other. Using this and the facts above, we can show that <span class="pre">`min`</span> is commutative:

    example : min a b = min b a := by
      apply le_antisymm
      · show min a b ≤ min b a
        apply le_min
        · apply min_le_right
        apply min_le_left
      · show min b a ≤ min a b
        apply le_min
        · apply min_le_right
        apply min_le_left

Here we have used dots to separate proofs of different goals. Our usage is inconsistent: at the outer level, we use dots and indentation for both goals, whereas for the nested proofs, we use dots only until a single goal remains. Both conventions are reasonable and useful. We also use the <span class="pre">`show`</span> tactic to structure the proof and indicate what is being proved in each block. The proof still works without the <span class="pre">`show`</span> commands, but using them makes the proof easier to read and maintain.

It may bother you that the proof is repetitive. To foreshadow skills you will learn later on, we note that one way to avoid the repetition is to state a local lemma and then use it:

    example : min a b = min b a := by
      have h : ∀ x y : ℝ, min x y ≤ min y x := by
        intro x y
        apply le_min
        apply min_le_right
        apply min_le_left
      apply le_antisymm
      apply h
      apply h

We will say more about the universal quantifier in <a href="C03_Logic.html#implication-and-the-universal-quantifier" class="reference internal"><span class="std std-numref">Section 3.1</span></a>, but suffice it to say here that the hypothesis <span class="pre">`h`</span> says that the desired inequality holds for any <span class="pre">`x`</span> and <span class="pre">`y`</span>, and the <span class="pre">`intro`</span> tactic introduces an arbitrary <span class="pre">`x`</span> and <span class="pre">`y`</span> to establish the conclusion. The first <span class="pre">`apply`</span> after <span class="pre">`le_antisymm`</span> implicitly uses <span class="pre">`h`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>, whereas the second one uses <span class="pre">`h`</span>` `<span class="pre">`b`</span>` `<span class="pre">`a`</span>.

Another solution is to use the <span class="pre">`repeat`</span> tactic, which applies a tactic (or a block) as many times as it can.

    example : min a b = min b a := by
      apply le_antisymm
      repeat
        apply le_min
        apply min_le_right
        apply min_le_left

We encourage you to prove the following as exercises. You can use either of the tricks just described to shorten the first.

    example : max a b = max b a := by
      sorry
    example : min (min a b) c = min a (min b c) := by
      sorry

Of course, you are welcome to prove the associativity of <span class="pre">`max`</span> as well.

It is an interesting fact that <span class="pre">`min`</span> distributes over <span class="pre">`max`</span> the way that multiplication distributes over addition, and vice-versa. In other words, on the real numbers, we have the identity <span class="pre">`min`</span>` `<span class="pre">`a`</span>` `<span class="pre">`(max`</span>` `<span class="pre">`b`</span>` `<span class="pre">`c)`</span>` `<span class="pre">`=`</span>` `<span class="pre">`max`</span>` `<span class="pre">`(min`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b)`</span>` `<span class="pre">`(min`</span>` `<span class="pre">`a`</span>` `<span class="pre">`c)`</span> as well as the corresponding version with <span class="pre">`max`</span> and <span class="pre">`min`</span> switched. But in the next section we will see that this does *not* follow from the transitivity and reflexivity of <span class="pre">`≤`</span> and the characterizing properties of <span class="pre">`min`</span> and <span class="pre">`max`</span> enumerated above. We need to use the fact that <span class="pre">`≤`</span> on the real numbers is a *total order*, which is to say, it satisfies <span class="pre">`∀`</span>` `<span class="pre">`x`</span>` `<span class="pre">`y,`</span>` `<span class="pre">`x`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`y`</span>` `<span class="pre">`∨`</span>` `<span class="pre">`y`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`x`</span>. Here the disjunction symbol, <span class="pre">`∨`</span>, represents “or”. In the first case, we have <span class="pre">`min`</span>` `<span class="pre">`x`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`x`</span>, and in the second case, we have <span class="pre">`min`</span>` `<span class="pre">`x`</span>` `<span class="pre">`y`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y`</span>. We will learn how to reason by cases in <a href="C03_Logic.html#disjunction" class="reference internal"><span class="std std-numref">Section 3.5</span></a>, but for now we will stick to examples that don’t require the case split.

Here is one such example:

    theorem aux : min a b + c ≤ min (a + c) (b + c) := by
      sorry
    example : min a b + c = min (a + c) (b + c) := by
      sorry

It is clear that <span class="pre">`aux`</span> provides one of the two inequalities needed to prove the equality, but applying it to suitable values yields the other direction as well. As a hint, you can use the theorem <span class="pre">`add_neg_cancel_right`</span> and the <span class="pre">`linarith`</span> tactic.

Lean’s naming convention is made manifest in the library’s name for the triangle inequality:

    #check (abs_add : ∀ a b : ℝ, |a + b| ≤ |a| + |b|)

Use it to prove the following variant, using also <span class="pre">`add_sub_cancel_right`</span>:

    example : |a| - |b| ≤ |a - b| :=
      sorry
    end

See if you can do this in three lines or less. You can use the theorem <span class="pre">`sub_add_cancel`</span>.

Another important relation that we will make use of in the sections to come is the divisibility relation on the natural numbers, <span class="pre">`x`</span>` `<span class="pre">`∣`</span>` `<span class="pre">`y`</span>. Be careful: the divisibility symbol is *not* the ordinary bar on your keyboard. Rather, it is a unicode character obtained by typing <span class="pre">`\|`</span> in VS Code. By convention, Mathlib uses <span class="pre">`dvd`</span> to refer to it in theorem names.

    example (h₀ : x ∣ y) (h₁ : y ∣ z) : x ∣ z :=
      dvd_trans h₀ h₁

    example : x ∣ y * x * z := by
      apply dvd_mul_of_dvd_left
      apply dvd_mul_left

    example : x ∣ x ^ 2 := by
      apply dvd_mul_left

In the last example, the exponent is a natural number, and applying <span class="pre">`dvd_mul_left`</span> forces Lean to expand the definition of <span class="pre">`x^2`</span> to <span class="pre">`x^1`</span>` `<span class="pre">`*`</span>` `<span class="pre">`x`</span>. See if you can guess the names of the theorems you need to prove the following:

    example (h : x ∣ w) : x ∣ y * (x * z) + x ^ 2 + w ^ 2 := by
      sorry
    end

With respect to divisibility, the *greatest common divisor*, <span class="pre">`gcd`</span>, and least common multiple, <span class="pre">`lcm`</span>, are analogous to <span class="pre">`min`</span> and <span class="pre">`max`</span>. Since every number divides <span class="pre">`0`</span>, <span class="pre">`0`</span> is really the greatest element with respect to divisibility:

    variable (m n : ℕ)

    #check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
    #check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
    #check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
    #check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

See if you can guess the names of the theorems you will need to prove the following:

    example : Nat.gcd m n = Nat.gcd n m := by
      sorry

Hint: you can use <span class="pre">`dvd_antisymm`</span>, but if you do, Lean will complain that the expression is ambiguous between the generic theorem and the version <span class="pre">`Nat.dvd_antisymm`</span>, the one specifically for the natural numbers. You can use <span class="pre">`_root_.dvd_antisymm`</span> to specify the generic one; either one will work.

<span id="id4"></span>

## <span class="section-number">2.5. </span>Proving Facts about Algebraic Structures<a href="#proving-facts-about-algebraic-structures" class="headerlink" title="Link to this heading"></a>

In <a href="#proving-identities-in-algebraic-structures" class="reference internal"><span class="std std-numref">Section 2.2</span></a>, we saw that many common identities governing the real numbers hold in more general classes of algebraic structures, such as commutative rings. We can use any axioms we want to describe an algebraic structure, not just equations. For example, a *partial order* consists of a set with a binary relation that is reflexive, transitive, and antisymmetric. like <span class="pre">`≤`</span> on the real numbers. Lean knows about partial orders:

    variable {α : Type*} [PartialOrder α]
    variable (x y z : α)

    #check x ≤ y
    #check (le_refl x : x ≤ x)
    #check (le_trans : x ≤ y → y ≤ z → x ≤ z)
    #check (le_antisymm : x ≤ y → y ≤ x → x = y)

Here we are adopting the Mathlib convention of using letters like <span class="pre">`α`</span>, <span class="pre">`β`</span>, and <span class="pre">`γ`</span> (entered as <span class="pre">`\a`</span>, <span class="pre">`\b`</span>, and <span class="pre">`\g`</span>) for arbitrary types. The library often uses letters like <span class="pre">`R`</span> and <span class="pre">`G`</span> for the carriers of algebraic structures like rings and groups, respectively, but in general Greek letters are used for types, especially when there is little or no structure associated with them.

Associated to any partial order, <span class="pre">`≤`</span>, there is also a *strict partial order*, <span class="pre">`<`</span>, which acts somewhat like <span class="pre">`<`</span> on the real numbers. Saying that <span class="pre">`x`</span> is less than <span class="pre">`y`</span> in this order is equivalent to saying that it is less-than-or-equal to <span class="pre">`y`</span> and not equal to <span class="pre">`y`</span>.

    #check x < y
    #check (lt_irrefl x : ¬ (x < x))
    #check (lt_trans : x < y → y < z → x < z)
    #check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
    #check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

    example : x < y ↔ x ≤ y ∧ x ≠ y :=
      lt_iff_le_and_ne

In this example, the symbol <span class="pre">`∧`</span> stands for “and,” the symbol <span class="pre">`¬`</span> stands for “not,” and <span class="pre">`x`</span>` `<span class="pre">`≠`</span>` `<span class="pre">`y`</span> abbreviates <span class="pre">`¬`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`=`</span>` `<span class="pre">`y)`</span>. In <a href="C03_Logic.html#logic" class="reference internal"><span class="std std-numref">Chapter 3</span></a>, you will learn how to use these logical connectives to *prove* that <span class="pre">`<`</span> has the properties indicated.

A *lattice* is a structure that extends a partial order with operations <span class="pre">`⊓`</span> and <span class="pre">`⊔`</span> that are analogous to <span class="pre">`min`</span> and <span class="pre">`max`</span> on the real numbers:

    variable {α : Type*} [Lattice α]
    variable (x y z : α)

    #check x ⊓ y
    #check (inf_le_left : x ⊓ y ≤ x)
    #check (inf_le_right : x ⊓ y ≤ y)
    #check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
    #check x ⊔ y
    #check (le_sup_left : x ≤ x ⊔ y)
    #check (le_sup_right : y ≤ x ⊔ y)
    #check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

The characterizations of <span class="pre">`⊓`</span> and <span class="pre">`⊔`</span> justify calling them the *greatest lower bound* and *least upper bound*, respectively. You can type them in VS code using <span class="pre">`\glb`</span> and <span class="pre">`\lub`</span>. The symbols are also often called then *infimum* and the *supremum*, and Mathlib refers to them as <span class="pre">`inf`</span> and <span class="pre">`sup`</span> in theorem names. To further complicate matters, they are also often called *meet* and *join*. Therefore, if you work with lattices, you have to keep the following dictionary in mind:

- <span class="pre">`⊓`</span> is the *greatest lower bound*, *infimum*, or *meet*.

- <span class="pre">`⊔`</span> is the *least upper bound*, *supremum*, or *join*.

Some instances of lattices include:

- <span class="pre">`min`</span> and <span class="pre">`max`</span> on any total order, such as the integers or real numbers with <span class="pre">`≤`</span>

- <span class="pre">`∩`</span> and <span class="pre">`∪`</span> on the collection of subsets of some domain, with the ordering <span class="pre">`⊆`</span>

- <span class="pre">`∧`</span> and <span class="pre">`∨`</span> on boolean truth values, with ordering <span class="pre">`x`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`y`</span> if either <span class="pre">`x`</span> is false or <span class="pre">`y`</span> is true

- <span class="pre">`gcd`</span> and <span class="pre">`lcm`</span> on the natural numbers (or positive natural numbers), with the divisibility ordering, <span class="pre">`∣`</span>

- the collection of linear subspaces of a vector space, where the greatest lower bound is given by the intersection, the least upper bound is given by the sum of the two spaces, and the ordering is inclusion

- the collection of topologies on a set (or, in Lean, a type), where the greatest lower bound of two topologies consists of the topology that is generated by their union, the least upper bound is their intersection, and the ordering is reverse inclusion

You can check that, as with <span class="pre">`min`</span> / <span class="pre">`max`</span> and <span class="pre">`gcd`</span> / <span class="pre">`lcm`</span>, you can prove the commutativity and associativity of the infimum and supremum using only their characterizing axioms, together with <span class="pre">`le_refl`</span> and <span class="pre">`le_trans`</span>.

Using <span class="pre">`apply`</span>` `<span class="pre">`le_trans`</span> when seeing a goal <span class="pre">`x`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`z`</span> is not a great idea. Indeed Lean has no way to guess which intermediate element <span class="pre">`y`</span> we want to use. So <span class="pre">`apply`</span>` `<span class="pre">`le_trans`</span> produces three goals that look like <span class="pre">`x`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`?a`</span>, <span class="pre">`?a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`z`</span> and <span class="pre">`α`</span> where <span class="pre">`?a`</span> (probably with a more complicated auto-generated name) stands for the mysterious <span class="pre">`y`</span>. The last goal, with type <span class="pre">`α`</span>, is to provide the value of <span class="pre">`y`</span>. It comes lasts because Lean hopes to automatically infer it from the proof of the first goal <span class="pre">`x`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`?a`</span>. In order to avoid this unappealing situation, you can use the <span class="pre">`calc`</span> tactic to explicitly provide <span class="pre">`y`</span>. Alternatively, you can use the <span class="pre">`trans`</span> tactic which takes <span class="pre">`y`</span> as an argument and produces the expected goals <span class="pre">`x`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`y`</span> and <span class="pre">`y`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`z`</span>. Of course you can also avoid this issue by providing directly a full proof such as <span class="pre">`exact`</span>` `<span class="pre">`le_trans`</span>` `<span class="pre">`inf_le_left`</span>` `<span class="pre">`inf_le_right`</span>, but this requires a lot more planning.

    example : x ⊓ y = y ⊓ x := by
      sorry

    example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
      sorry

    example : x ⊔ y = y ⊔ x := by
      sorry

    example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
      sorry

You can find these theorems in the Mathlib as <span class="pre">`inf_comm`</span>, <span class="pre">`inf_assoc`</span>, <span class="pre">`sup_comm`</span>, and <span class="pre">`sup_assoc`</span>, respectively.

Another good exercise is to prove the *absorption laws* using only those axioms:

    theorem absorb1 : x ⊓ (x ⊔ y) = x := by
      sorry

    theorem absorb2 : x ⊔ x ⊓ y = x := by
      sorry

These can be found in Mathlib with the names <span class="pre">`inf_sup_self`</span> and <span class="pre">`sup_inf_self`</span>.

A lattice that satisfies the additional identities <span class="pre">`x`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`(y`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`z)`</span>` `<span class="pre">`=`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`z)`</span> and <span class="pre">`x`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`(y`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`z)`</span>` `<span class="pre">`=`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`y)`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`(x`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`z)`</span> is called a *distributive lattice*. Lean knows about these too:

    variable {α : Type*} [DistribLattice α]
    variable (x y z : α)

    #check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
    #check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
    #check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
    #check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))

The left and right versions are easily shown to be equivalent, given the commutativity of <span class="pre">`⊓`</span> and <span class="pre">`⊔`</span>. It is a good exercise to show that not every lattice is distributive by providing an explicit description of a nondistributive lattice with finitely many elements. It is also a good exercise to show that in any lattice, either distributivity law implies the other:

    variable {α : Type*} [Lattice α]
    variable (a b c : α)

    example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
      sorry

    example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
      sorry

It is possible to combine axiomatic structures into larger ones. For example, a *strict ordered ring* consists of a ring together with a partial order on the carrier satisfying additional axioms that say that the ring operations are compatible with the order:

    variable {R : Type*} [Ring R] [PartialOrder R] [IsStrictOrderedRing R]
    variable (a b c : R)

    #check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
    #check (mul_pos : 0 < a → 0 < b → 0 < a * b)

<a href="C03_Logic.html#logic" class="reference internal"><span class="std std-numref">Chapter 3</span></a> will provide the means to derive the following from <span class="pre">`mul_pos`</span> and the definition of <span class="pre">`<`</span>:

    #check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

It is then an extended exercise to show that many common facts used to reason about arithmetic and the ordering on the real numbers hold generically for any ordered ring. Here are a couple of examples you can try, using only properties of rings, partial orders, and the facts enumerated in the last two examples (beware that those rings are not assumed to be commutative, so the ring tactic is not available):

    example (h : a ≤ b) : 0 ≤ b - a := by
      sorry

    example (h: 0 ≤ b - a) : a ≤ b := by
      sorry

    example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
      sorry

Finally, here is one last example. A *metric space* consists of a set equipped with a notion of distance, <span class="pre">`dist`</span>` `<span class="pre">`x`</span>` `<span class="pre">`y`</span>, mapping any pair of elements to a real number. The distance function is assumed to satisfy the following axioms:

    variable {X : Type*} [MetricSpace X]
    variable (x y z : X)

    #check (dist_self x : dist x x = 0)
    #check (dist_comm x y : dist x y = dist y x)
    #check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

Having mastered this section, you can show that it follows from these axioms that distances are always nonnegative:

    example (x y : X) : 0 ≤ dist x y := by
      sorry

We recommend making use of the theorem <span class="pre">`nonneg_of_mul_nonneg_left`</span>. As you may have guessed, this theorem is called <span class="pre">`dist_nonneg`</span> in Mathlib.
