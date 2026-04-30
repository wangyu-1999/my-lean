<span id="id1"></span>

# <span class="section-number">1. </span>Introduction<a href="#introduction" class="headerlink" title="Link to this heading"></a>

## <span class="section-number">1.1. </span>Getting Started<a href="#getting-started" class="headerlink" title="Link to this heading"></a>

The goal of this book is to teach you to formalize mathematics using the Lean 4 interactive proof assistant. It assumes that you know some mathematics, but it does not require much. Although we will cover examples ranging from number theory to measure theory and analysis, we will focus on elementary aspects of those fields, in the hopes that if they are not familiar to you, you can pick them up as you go. We also don’t presuppose any background with formal methods. Formalization can be seen as a kind of computer programming: we will write mathematical definitions, theorems, and proofs in a regimented language, like a programming language, that Lean can understand. In return, Lean provides feedback and information, interprets expressions and guarantees that they are well-formed, and ultimately certifies the correctness of our proofs.

You can learn more about Lean from the <a href="https://leanprover.github.io" class="reference external">Lean project page</a> and the <a href="https://leanprover-community.github.io/" class="reference external">Lean community web pages</a>. This tutorial is based on Lean’s large and ever-growing library, *Mathlib*. We also strongly recommend joining the <a href="https://leanprover.zulipchat.com/" class="reference external">Lean Zulip online chat group</a> if you haven’t already. You’ll find a lively and welcoming community of Lean enthusiasts there, happy to answer questions and offer moral support.

Although you can read a pdf or html version of this book online, it is designed to be read interactively, running Lean from inside the VS Code editor. To get started:

1.  Install Lean 4 and VS Code following these <a href="https://leanprover-community.github.io/get_started.html" class="reference external">installation instructions</a>.

2.  Make sure you have <a href="https://git-scm.com/" class="reference external">git</a> installed.

3.  Follow these <a href="https://leanprover-community.github.io/install/project.html#working-on-an-existing-project" class="reference external">instructions</a> to fetch the <span class="pre">`mathematics_in_lean`</span> repository and open it up in VS Code.

4.  Each section in this book has an associated Lean file with examples and exercises. You can find them in the folder <span class="pre">`MIL`</span>, organized by chapter. We strongly recommend making a copy of that folder and experimenting and doing the exercises in that copy. This leaves the originals intact, and it also makes it easier to update the repository as it changes (see below). You can call the copy <span class="pre">`my_files`</span> or whatever you want and use it to create your own Lean files as well.

At that point, you can open the textbook in a side panel in VS Code as follows:

1.  Type <span class="pre">`ctrl-shift-P`</span> (<span class="pre">`command-shift-P`</span> in macOS).

2.  Type <span class="pre">`Lean`</span>` `<span class="pre">`4:`</span>` `<span class="pre">`Docs:`</span>` `<span class="pre">`Show`</span>` `<span class="pre">`Documentation`</span>` `<span class="pre">`Resources`</span> in the bar that appears, and then press return. (You can press return to select it as soon as it is highlighted in the menu.)

3.  In the window that opens, click on <span class="pre">`Mathematics`</span>` `<span class="pre">`in`</span>` `<span class="pre">`Lean`</span>.

Alternatively, you can run Lean and VS Code in the cloud, using <a href="https://gitpod.io/" class="reference external">Gitpod</a>. You can find instructions as to how to do that on the Mathematics in Lean <a href="https://github.com/leanprover-community/mathematics_in_lean" class="reference external">project page</a> on Github. We still recommend working in a copy of the MIL folder, as described above.

This textbook and the associated repository are still a work in progress. You can update the repository by typing <span class="pre">`git`</span>` `<span class="pre">`pull`</span> followed by <span class="pre">`lake`</span>` `<span class="pre">`exe`</span>` `<span class="pre">`cache`</span>` `<span class="pre">`get`</span> inside the <span class="pre">`mathematics_in_lean`</span> folder. (This assumes that you have not changed the contents of the <span class="pre">`MIL`</span> folder, which is why we suggested making a copy.)

We intend for you to work on the exercises in the <span class="pre">`MIL`</span> folder while reading the textbook, which contains explanations, instructions, and hints. The text will often include examples, like this one:

    #eval "Hello, World!"

You should be able to find the corresponding example in the associated Lean file. If you click on the line, VS Code will show you Lean’s feedback in the <span class="pre">`Lean`</span>` `<span class="pre">`Goal`</span> window, and if you hover your cursor over the <span class="pre">`#eval`</span> command VS Code will show you Lean’s response to this command in a pop-up window. You are encouraged to edit the file and try examples of your own.

This book moreover provides lots of challenging exercises for you to try. Don’t rush past these! Lean is about *doing* mathematics interactively, not just reading about it. Working through the exercises is central to the experience. You don’t have to do all of them; when you feel comfortable that you have mastered the relevant skills, feel free to move on. You can always compare your solutions to the ones in the <span class="pre">`solutions`</span> folder associated with each section.

## <span class="section-number">1.2. </span>Overview<a href="#overview" class="headerlink" title="Link to this heading"></a>

Put simply, Lean is a tool for building complex expressions in a formal language known as *dependent type theory*.

Every expression has a *type*, and you can use the \#check command to print it. Some expressions have types like ℕ or ℕ → ℕ. These are mathematical objects.

    #check 2 + 2

    def f (x : ℕ) :=
      x + 3

    #check f

Some expressions have type Prop. These are mathematical statements.

    #check 2 + 2 = 4

    def FermatLastTheorem :=
      ∀ x y z n : ℕ, n > 2 ∧ x * y * z ≠ 0 → x ^ n + y ^ n ≠ z ^ n

    #check FermatLastTheorem

Some expressions have a type, P, where P itself has type Prop. Such an expression is a proof of the proposition P.

    theorem easy : 2 + 2 = 4 :=
      rfl

    #check easy

    theorem hard : FermatLastTheorem :=
      sorry

    #check hard

If you manage to construct an expression of type <span class="pre">`FermatLastTheorem`</span> and Lean accepts it as a term of that type, you have done something very impressive. (Using <span class="pre">`sorry`</span> is cheating, and Lean knows it.) So now you know the game. All that is left to learn are the rules.

This book is complementary to a companion tutorial, <a href="https://leanprover.github.io/theorem_proving_in_lean4/" class="reference external">Theorem Proving in Lean</a>, which provides a more thorough introduction to the underlying logical framework and core syntax of Lean. *Theorem Proving in Lean* is for people who prefer to read a user manual cover to cover before using a new dishwasher. If you are the kind of person who prefers to hit the *start* button and figure out how to activate the potscrubber feature later, it makes more sense to start here and refer back to *Theorem Proving in Lean* as necessary.

Another thing that distinguishes *Mathematics in Lean* from *Theorem Proving in Lean* is that here we place a much greater emphasis on the use of *tactics*. Given that we are trying to build complex expressions, Lean offers two ways of going about it: we can write down the expressions themselves (that is, suitable text descriptions thereof), or we can provide Lean with *instructions* as to how to construct them. For example, the following expression represents a proof of the fact that if <span class="pre">`n`</span> is even then so is <span class="pre">`m`</span>` `<span class="pre">`*`</span>` `<span class="pre">`n`</span>:

    example : ∀ m n : Nat, Even n → Even (m * n) := fun m n ⟨k, (hk : n = k + k)⟩ ↦
      have hmn : m * n = m * k + m * k := by rw [hk, mul_add]
      show ∃ l, m * n = l + l from ⟨_, hmn⟩

The *proof term* can be compressed to a single line:

    example : ∀ m n : Nat, Even n → Even (m * n) :=
    fun m n ⟨k, hk⟩ ↦ ⟨m * k, by rw [hk, mul_add]⟩

The following is, instead, a *tactic-style* proof of the same theorem, where lines starting with <span class="pre">`--`</span> are comments, hence ignored by Lean:

    example : ∀ m n : Nat, Even n → Even (m * n) := by
      -- Say `m` and `n` are natural numbers, and assume `n = 2 * k`.
      rintro m n ⟨k, hk⟩
      -- We need to prove `m * n` is twice a natural number. Let's show it's twice `m * k`.
      use m * k
      -- Substitute for `n`,
      rw [hk]
      -- and now it's obvious.
      ring

As you enter each line of such a proof in VS Code, Lean displays the *proof state* in a separate window, telling you what facts you have already established and what tasks remain to prove your theorem. You can replay the proof by stepping through the lines, since Lean will continue to show you the state of the proof at the point where the cursor is. In this example, you will then see that the first line of the proof introduces <span class="pre">`m`</span> and <span class="pre">`n`</span> (we could have renamed them at that point, if we wanted to), and also decomposes the hypothesis <span class="pre">`Even`</span>` `<span class="pre">`n`</span> to a <span class="pre">`k`</span> and the assumption that <span class="pre">`n`</span>` `<span class="pre">`=`</span>` `<span class="pre">`2`</span>` `<span class="pre">`*`</span>` `<span class="pre">`k`</span>. The second line, <span class="pre">`use`</span>` `<span class="pre">`m`</span>` `<span class="pre">`*`</span>` `<span class="pre">`k`</span>, declares that we are going to show that <span class="pre">`m`</span>` `<span class="pre">`*`</span>` `<span class="pre">`n`</span> is even by showing <span class="pre">`m`</span>` `<span class="pre">`*`</span>` `<span class="pre">`n`</span>` `<span class="pre">`=`</span>` `<span class="pre">`2`</span>` `<span class="pre">`*`</span>` `<span class="pre">`(m`</span>` `<span class="pre">`*`</span>` `<span class="pre">`k)`</span>. The next line uses the <span class="pre">`rw`</span> tactic to replace <span class="pre">`n`</span> by <span class="pre">`2`</span>` `<span class="pre">`*`</span>` `<span class="pre">`k`</span> in the goal (<span class="pre">`rw`</span> stands for “rewrite”), and the <span class="pre">`ring`</span> tactic solves the resulting goal <span class="pre">`m`</span>` `<span class="pre">`*`</span>` `<span class="pre">`(2`</span>` `<span class="pre">`*`</span>` `<span class="pre">`k)`</span>` `<span class="pre">`=`</span>` `<span class="pre">`2`</span>` `<span class="pre">`*`</span>` `<span class="pre">`(m`</span>` `<span class="pre">`*`</span>` `<span class="pre">`k)`</span>.

The ability to build a proof in small steps with incremental feedback is extremely powerful. For that reason, tactic proofs are often easier and quicker to write than proof terms. There isn’t a sharp distinction between the two: tactic proofs can be inserted in proof terms, as we did with the phrase <span class="pre">`by`</span>` `<span class="pre">`rw`</span>` `<span class="pre">`[hk,`</span>` `<span class="pre">`mul_add]`</span> in the example above. We will also see that, conversely, it is often useful to insert a short proof term in the middle of a tactic proof. That said, in this book, our emphasis will be on the use of tactics.

In our example, the tactic proof can also be reduced to a one-liner:

    example : ∀ m n : Nat, Even n → Even (m * n) := by
      rintro m n ⟨k, hk⟩; use m * k; rw [hk]; ring

Here we have used tactics to carry out small proof steps. But they can also provide substantial automation, and justify longer calculations and bigger inferential steps. For example, we can invoke Lean’s simplifier with specific rules for simplifying statements about parity to prove our theorem automatically.

    example : ∀ m n : Nat, Even n → Even (m * n) := by
      intros; simp [*, parity_simps]

Another big difference between the two introductions is that *Theorem Proving in Lean* depends only on core Lean and its built-in tactics, whereas *Mathematics in Lean* is built on top of Lean’s powerful and ever-growing library, *Mathlib*. As a result, we can show you how to use some of the mathematical objects and theorems in the library, and some of the very useful tactics. This book is not meant to be used as an complete overview of the library; the <a href="https://leanprover-community.github.io/" class="reference external">community</a> web pages contain extensive documentation. Rather, our goal is to introduce you to the style of thinking that underlies that formalization, and point out basic entry points so that you are comfortable browsing the library and finding things on your own.

Interactive theorem proving can be frustrating, and the learning curve is steep. But the Lean community is very welcoming to newcomers, and people are available on the <a href="https://leanprover.zulipchat.com/" class="reference external">Lean Zulip chat group</a> round the clock to answer questions. We hope to see you there, and have no doubt that soon enough you, too, will be able to answer such questions and contribute to the development of *Mathlib*.

So here is your mission, should you choose to accept it: dive in, try the exercises, come to Zulip with questions, and have fun. But be forewarned: interactive theorem proving will challenge you to think about mathematics and mathematical reasoning in fundamentally new ways. Your life may never be the same.

*Acknowledgments.* We are grateful to Gabriel Ebner for setting up the infrastructure for running this tutorial in VS Code, and to Kim Morrison and Mario Carneiro for help porting it from Lean 4. We are also grateful for help and corrections from Takeshi Abe, Julian Berman, Alex Best, Thomas Browning, Bulwi Cha, Hanson Char, Bryan Gin-ge Chen, Steven Clontz, Mauricio Collaris, Johan Commelin, Mark Czubin, Alexandru Duca, Pierpaolo Frasa, Denis Gorbachev, Winston de Greef, Mathieu Guay-Paquet, Marc Huisinga, Benjamin Jones, Julian Külshammer, Victor Liu, Jimmy Lu, Martin C. Martin, Giovanni Mascellani, John McDowell, Joseph McKinsey, Bhavik Mehta, Isaiah Mindich, Kabelo Moiloa, Hunter Monroe, Pietro Monticone, Oliver Nash, Emanuelle Natale, Filippo A. E. Nuccio, Pim Otte, Bartosz Piotrowski, Nicolas Rolland, Keith Rush, Yannick Seurin, Guilherme Silva, Bernardo Subercaseaux, Pedro Sánchez Terraf, Matthew Toohey, Alistair Tucker, Floris van Doorn, Eric Wieser, and others. Our work has been partially supported by the Hoskinson Center for Formal Mathematics.
