<span id="id1"></span>

# <span class="section-number">8. </span>Hierarchies<a href="#hierarchies" class="headerlink" title="Link to this heading"></a>

We have seen in <a href="C07_Structures.html#structures" class="reference internal"><span class="std std-numref">Chapter 7</span></a> how to define the class of groups and build instances of this class, and then how to build an instance of the commutative ring class. But of course there is a hierarchy here: a commutative ring is in particular an additive group. In this chapter we will study how to build such hierarchies. They appear in all branches of mathematics but in this chapter the emphasis will be on algebraic examples.

It may seem premature to discuss how to build hierarchies before more discussions about using existing hierarchies. But some understanding of the technology underlying hierarchies is required to use them. So you should probably still read this chapter, but without trying too hard to remember everything on your first read, then read the following chapters and come back here for a second reading.

In this chapter, we will redefine (simpler versions of) many things that appear in Mathlib so we will used indices to distinguish our version. For instance we will have <span class="pre">`Ring₁`</span> as our version of <span class="pre">`Ring`</span>. Since we will gradually explain more powerful ways of formalizing structures, those indices will sometimes grow beyond one.

<span id="section-hierarchies-basics"></span>

## <span class="section-number">8.1. </span>Basics<a href="#basics" class="headerlink" title="Link to this heading"></a>

At the very bottom of all hierarchies in Lean, we find data-carrying classes. The following class records that the given type <span class="pre">`α`</span> is endowed with a distinguished element called <span class="pre">`one`</span>. At this stage, it has no property at all.

    class One₁ (α : Type) where
      /-- The element one -/
      one : α

Since we’ll make a much heavier use of classes in this chapter, we need to understand some more details about what the <span class="pre">`class`</span> command is doing. First, the <span class="pre">`class`</span> command above defines a structure <span class="pre">`One₁`</span> with parameter <span class="pre">`α`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type`</span> and a single field <span class="pre">`one`</span>. It also mark this structure as a class so that arguments of type <span class="pre">`One₁`</span>` `<span class="pre">`α`</span> for some type <span class="pre">`α`</span> will be inferrable using the instance resolution procedure, as long as they are marked as instance-implicit, i.e. appear between square brackets. Those two effects could also have been achieved using the <span class="pre">`structure`</span> command with <span class="pre">`class`</span> attribute, i.e. writing <span class="pre">`@[class]`</span>` `<span class="pre">`structure`</span> instance of <span class="pre">`class`</span>. But the class command also ensures that <span class="pre">`One₁`</span>` `<span class="pre">`α`</span> appears as an instance-implicit argument in its own fields. Compare:

    #check One₁.one -- One₁.one {α : Type} [self : One₁ α] : α

    @[class] structure One₂ (α : Type) where
      /-- The element one -/
      one : α

    #check One₂.one

In the second check, we can see that <span class="pre">`self`</span>` `<span class="pre">`:`</span>` `<span class="pre">`One₂`</span>` `<span class="pre">`α`</span> is an explicit argument. Let us make sure the first version is indeed usable without any explicit argument.

    example (α : Type) [One₁ α] : α := One₁.one

Remark: in the above example, the argument <span class="pre">`One₁`</span>` `<span class="pre">`α`</span> is marked as instance-implicit, which is a bit silly since this affects only *uses* of the declaration and declaration created by the <span class="pre">`example`</span> command cannot be used. However it allows us to avoid giving a name to that argument and, more importantly, it starts installing the good habit of marking <span class="pre">`One₁`</span>` `<span class="pre">`α`</span> arguments as instance-implicit.

Another remark is that all this will work only when Lean knows what is <span class="pre">`α`</span>. In the above example, leaving out the type ascription <span class="pre">`:`</span>` `<span class="pre">`α`</span> would generate an error message like: <span class="pre">`typeclass`</span>` `<span class="pre">`instance`</span>` `<span class="pre">`problem`</span>` `<span class="pre">`is`</span>` `<span class="pre">`stuck,`</span>` `<span class="pre">`it`</span>` `<span class="pre">`is`</span>` `<span class="pre">`often`</span>` `<span class="pre">`due`</span>` `<span class="pre">`to`</span>` `<span class="pre">`metavariables`</span>` `<span class="pre">`One₁`</span>` `<span class="pre">`(?m.263`</span>` `<span class="pre">`α)`</span> where <span class="pre">`?m.263`</span>` `<span class="pre">`α`</span> means “some type depending on <span class="pre">`α`</span>” (and 263 is simply an auto-generated index that would be useful to distinguish between several unknown things). Another way to avoid this issue would be to use a type annotation, as in:

    example (α : Type) [One₁ α] := (One₁.one : α)

You may have already encountered that issue when playing with limits of sequences in <a href="C03_Logic.html#sequences-and-convergence" class="reference internal"><span class="std std-numref">Section 3.6</span></a> if you tried to state for instance that <span class="pre">`0`</span>` `<span class="pre">`<`</span>` `<span class="pre">`1`</span> without telling Lean whether you meant this inequality to be about natural numbers or real numbers.

Our next task is to assign a notation to <span class="pre">`One₁.one`</span>. Since we don’t want collisions with the builtin notation for <span class="pre">`1`</span>, we will use <span class="pre">`𝟙`</span>. This is achieved by the following command where the first line tells Lean to use the documentation of <span class="pre">`One₁.one`</span> as documentation for the symbol <span class="pre">`𝟙`</span>.

    @[inherit_doc]
    notation "𝟙" => One₁.one

    example {α : Type} [One₁ α] : α := 𝟙

    example {α : Type} [One₁ α] : (𝟙 : α) = 𝟙 := rfl

We now want a data-carrying class recording a binary operation. We don’t want to choose between addition and multiplication for now so we’ll use diamond.

    class Dia₁ (α : Type) where
      dia : α → α → α

    infixl:70 " ⋄ "   => Dia₁.dia

As in the <span class="pre">`One₁`</span> example, the operation has no property at all at this stage. Let us now define the class of semigroup structures where the operation is denoted by <span class="pre">`⋄`</span>. For now, we define it by hand as a structure with two fields, a <span class="pre">`Dia₁`</span> instance and some <span class="pre">`Prop`</span>-valued field <span class="pre">`dia_assoc`</span> asserting associativity of <span class="pre">`⋄`</span>.

    class Semigroup₀ (α : Type) where
      toDia₁ : Dia₁ α
      /-- Diamond is associative -/
      dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

Note that while stating dia\_assoc, the previously defined field toDia₁ is in the local context hence can be used when Lean searches for an instance of Dia₁ α to make sense of a ⋄ b. However this toDia₁ field does not become part of the type class instances database. Hence doing <span class="pre">`example`</span>` `<span class="pre">`{α`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type}`</span>` `<span class="pre">`[Semigroup₁`</span>` `<span class="pre">`α]`</span>` `<span class="pre">`(a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α)`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α`</span>` `<span class="pre">`:=`</span>` `<span class="pre">`a`</span>` `<span class="pre">`⋄`</span>` `<span class="pre">`b`</span> would fail with error message <span class="pre">`failed`</span>` `<span class="pre">`to`</span>` `<span class="pre">`synthesize`</span>` `<span class="pre">`instance`</span>` `<span class="pre">`Dia₁`</span>` `<span class="pre">`α`</span>.

We can fix this by adding the <span class="pre">`instance`</span> attribute later.

    attribute [instance] Semigroup₀.toDia₁

    example {α : Type} [Semigroup₀ α] (a b : α) : α := a ⋄ b

Before building up, we need to use a different syntax to add this toDia₁ field, to tell Lean that Dia₁ α should be treated as if its fields were fields of Semigroup₁ itself. This also conveniently adds the toDia₁ instance automatically. The <span class="pre">`class`</span> command supports this using the <span class="pre">`extends`</span> syntax as in:

    class Semigroup₁ (α : Type) extends toDia₁ : Dia₁ α where
      /-- Diamond is associative -/
      dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

    example {α : Type} [Semigroup₁ α] (a b : α) : α := a ⋄ b

Note this syntax is also available in the <span class="pre">`structure`</span> command, although it that case it fixes only the hurdle of writing fields such as toDia₁ since there is no instance to define in that case.

The field name toDia₁ is optional in the extends syntax. By default it takes the name of the class being extended and prefixes it with “to”.

    class Semigroup₂ (α : Type) extends Dia₁ α where
      /-- Diamond is associative -/
      dia_assoc : ∀ a b c : α, a ⋄ b ⋄ c = a ⋄ (b ⋄ c)

Let us now try to combine a diamond operation and a distinguished one element with axioms saying this element is neutral on both sides.

    class DiaOneClass₁ (α : Type) extends One₁ α, Dia₁ α where
      /-- One is a left neutral element for diamond. -/
      one_dia : ∀ a : α, 𝟙 ⋄ a = a
      /-- One is a right neutral element for diamond -/
      dia_one : ∀ a : α, a ⋄ 𝟙 = a

In the next example, we tell Lean that <span class="pre">`α`</span> has a <span class="pre">`DiaOneClass₁`</span> structure and state a property that uses both a Dia₁ instance and a One₁ instance. In order to see how Lean finds those instances we set a tracing option whose result can be seen in the Infoview. This result is rather terse by default but it can be expanded by clicking on lines ending with black arrows. It includes failed attempts where Lean tried to find instances before having enough type information to succeed. The successful attempts do involve the instances generated by the <span class="pre">`extends`</span> syntax.

    set_option trace.Meta.synthInstance true in
    example {α : Type} [DiaOneClass₁ α] (a b : α) : Prop := a ⋄ b = 𝟙

Note that we don’t need to include extra fields where combining existing classes. Hence we can define monoids as:

    class Monoid₁ (α : Type) extends Semigroup₁ α, DiaOneClass₁ α

While the above definition seems straightforward, it hides an important subtlety. Both <span class="pre">`Semigroup₁`</span>` `<span class="pre">`α`</span> and <span class="pre">`DiaOneClass₁`</span>` `<span class="pre">`α`</span> extend <span class="pre">`Dia₁`</span>` `<span class="pre">`α`</span>, so one could fear that having a <span class="pre">`Monoid₁`</span>` `<span class="pre">`α`</span> instance gives two unrelated diamond operations on <span class="pre">`α`</span>, one coming from a field <span class="pre">`Monoid₁.toSemigroup₁`</span> and one coming from a field <span class="pre">`Monoid₁.toDiaOneClass₁`</span>.

Indeed if we try to build a monoid class by hand using:

    class Monoid₂ (α : Type) where
      toSemigroup₁ : Semigroup₁ α
      toDiaOneClass₁ : DiaOneClass₁ α

then we get two completely unrelated diamond operations <span class="pre">`Monoid₂.toSemigroup₁.toDia₁.dia`</span> and <span class="pre">`Monoid₂.toDiaOneClass₁.toDia₁.dia`</span>.

The version generated using the <span class="pre">`extends`</span> syntax does not have this defect.

    example {α : Type} [Monoid₁ α] :
      (Monoid₁.toSemigroup₁.toDia₁.dia : α → α → α) = Monoid₁.toDiaOneClass₁.toDia₁.dia := rfl

So the <span class="pre">`class`</span> command did some magic for us (and the <span class="pre">`structure`</span> command would have done it too). An easy way to see what are the fields of our classes is to check their constructor. Compare:

    /- Monoid₂.mk {α : Type} (toSemigroup₁ : Semigroup₁ α) (toDiaOneClass₁ : DiaOneClass₁ α) : Monoid₂ α -/
    #check Monoid₂.mk

    /- Monoid₁.mk {α : Type} [toSemigroup₁ : Semigroup₁ α] [toOne₁ : One₁ α] (one_dia : ∀ (a : α), 𝟙 ⋄ a = a) (dia_one : ∀ (a : α), a ⋄ 𝟙 = a) : Monoid₁ α -/
    #check Monoid₁.mk

So we see that <span class="pre">`Monoid₁`</span> takes <span class="pre">`Semigroup₁`</span>` `<span class="pre">`α`</span> argument as expected but then it won’t take a would-be overlapping <span class="pre">`DiaOneClass₁`</span>` `<span class="pre">`α`</span> argument but instead tears it apart and includes only the non-overlapping parts. And it also auto-generated an instance <span class="pre">`Monoid₁.toDiaOneClass₁`</span> which is *not* a field but has the expected signature which, from the end-user point of view, restores the symmetry between the two extended classes <span class="pre">`Semigroup₁`</span> and <span class="pre">`DiaOneClass₁`</span>.

    #check Monoid₁.toSemigroup₁
    #check Monoid₁.toDiaOneClass₁

We are now very close to defining groups. We could add to the monoid structure a field asserting the existence of an inverse for every element. But then we would need to work to access these inverses. In practice it is more convenient to add it as data. To optimize reusability, we define a new data-carrying class, and then give it some notation.

    class Inv₁ (α : Type) where
      /-- The inversion function -/
      inv : α → α

    @[inherit_doc]
    postfix:max "⁻¹" => Inv₁.inv

    class Group₁ (G : Type) extends Monoid₁ G, Inv₁ G where
      inv_dia : ∀ a : G, a⁻¹ ⋄ a = 𝟙

The above definition may seem too weak, we only ask that <span class="pre">`a⁻¹`</span> is a left-inverse of <span class="pre">`a`</span>. But the other side is automatic. In order to prove that, we need a preliminary lemma.

    lemma left_inv_eq_right_inv₁ {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
      rw [← DiaOneClass₁.one_dia c, ← hba, Semigroup₁.dia_assoc, hac, DiaOneClass₁.dia_one b]

In this lemma, it is pretty annoying to give full names, especially since it requires knowing which part of the hierarchy provides those facts. One way to fix this is to use the <span class="pre">`export`</span> command to copy those facts as lemmas in the root name space.

    export DiaOneClass₁ (one_dia dia_one)
    export Semigroup₁ (dia_assoc)
    export Group₁ (inv_dia)

We can then rewrite the above proof as:

    example {M : Type} [Monoid₁ M] {a b c : M} (hba : b ⋄ a = 𝟙) (hac : a ⋄ c = 𝟙) : b = c := by
      rw [← one_dia c, ← hba, dia_assoc, hac, dia_one b]

It is now your turn to prove things about our algebraic structures.

    lemma inv_eq_of_dia [Group₁ G] {a b : G} (h : a ⋄ b = 𝟙) : a⁻¹ = b :=
      sorry

    lemma dia_inv [Group₁ G] (a : G) : a ⋄ a⁻¹ = 𝟙 :=
      sorry

At this stage we would like to move on to define rings, but there is a serious issue. A ring structure on a type contains both an additive group structure and a multiplicative monoid structure, and some properties about their interaction. But so far we hard-coded a notation <span class="pre">`⋄`</span> for all our operations. More fundamentally, the type class system assumes every type has only one instance of each type class. There are various ways to solve this issue. Surprisingly Mathlib uses the naive idea to duplicate everything for additive and multiplicative theories with the help of some code-generating attribute. Structures and classes are defined in both additive and multiplicative notation with an attribute <span class="pre">`to_additive`</span> linking them. In case of multiple inheritance like for semi-groups, the auto-generated “symmetry-restoring” instances need also to be marked. This is a bit technical; you don’t need to understand details. The important point is that lemmas are then only stated in multiplicative notation and marked with the attribute <span class="pre">`to_additive`</span> to generate the additive version as <span class="pre">`left_inv_eq_right_inv'`</span> with its auto-generated additive version <span class="pre">`left_neg_eq_right_neg'`</span>. In order to check the name of this additive version we used the <span class="pre">`whatsnew`</span>` `<span class="pre">`in`</span> command on top of <span class="pre">`left_inv_eq_right_inv'`</span>.

    class AddSemigroup₃ (α : Type) extends Add α where
      /-- Addition is associative -/
      add_assoc₃ : ∀ a b c : α, a + b + c = a + (b + c)

    @[to_additive AddSemigroup₃]
    class Semigroup₃ (α : Type) extends Mul α where
      /-- Multiplication is associative -/
      mul_assoc₃ : ∀ a b c : α, a * b * c = a * (b * c)

    class AddMonoid₃ (α : Type) extends AddSemigroup₃ α, AddZeroClass α

    @[to_additive AddMonoid₃]
    class Monoid₃ (α : Type) extends Semigroup₃ α, MulOneClass α

    export Semigroup₃ (mul_assoc₃)
    export AddSemigroup₃ (add_assoc₃)

    whatsnew in
    @[to_additive]
    lemma left_inv_eq_right_inv' {M : Type} [Monoid₃ M] {a b c : M} (hba : b * a = 1) (hac : a * c = 1) : b = c := by
      rw [← one_mul c, ← hba, mul_assoc₃, hac, mul_one b]

    #check left_neg_eq_right_neg'

Equipped with this technology, we can easily define also commutative semigroups, monoids and groups, and then define rings.

    class AddCommSemigroup₃ (α : Type) extends AddSemigroup₃ α where
      add_comm : ∀ a b : α, a + b = b + a

    @[to_additive AddCommSemigroup₃]
    class CommSemigroup₃ (α : Type) extends Semigroup₃ α where
      mul_comm : ∀ a b : α, a * b = b * a

    class AddCommMonoid₃ (α : Type) extends AddMonoid₃ α, AddCommSemigroup₃ α

    @[to_additive AddCommMonoid₃]
    class CommMonoid₃ (α : Type) extends Monoid₃ α, CommSemigroup₃ α

    class AddGroup₃ (G : Type) extends AddMonoid₃ G, Neg G where
      neg_add : ∀ a : G, -a + a = 0

    @[to_additive AddGroup₃]
    class Group₃ (G : Type) extends Monoid₃ G, Inv G where
      inv_mul : ∀ a : G, a⁻¹ * a = 1

We should remember to tag lemmas with <span class="pre">`simp`</span> when appropriate.

    attribute [simp] Group₃.inv_mul AddGroup₃.neg_add

Then we need to repeat ourselves a bit since we switch to standard notations, but at least <span class="pre">`to_additive`</span> does the work of translating from the multiplicative notation to the additive one.

    @[to_additive]
    lemma inv_eq_of_mul [Group₃ G] {a b : G} (h : a * b = 1) : a⁻¹ = b :=
      sorry

Note that <span class="pre">`to_additive`</span> can be asked to tag a lemma with <span class="pre">`simp`</span> and propagate that attribute to the additive version as follows.

    @[to_additive (attr := simp)]
    lemma Group₃.mul_inv {G : Type} [Group₃ G] {a : G} : a * a⁻¹ = 1 := by
      sorry

    @[to_additive]
    lemma mul_left_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : a * b = a * c) : b = c := by
      sorry

    @[to_additive]
    lemma mul_right_cancel₃ {G : Type} [Group₃ G] {a b c : G} (h : b*a = c*a) : b = c := by
      sorry

    class AddCommGroup₃ (G : Type) extends AddGroup₃ G, AddCommMonoid₃ G

    @[to_additive AddCommGroup₃]
    class CommGroup₃ (G : Type) extends Group₃ G, CommMonoid₃ G

We are now ready for rings. For demonstration purposes we won’t assume that addition is commutative, and then immediately provide an instance of <span class="pre">`AddCommGroup₃`</span>. Mathlib does not play this game, first because in practice this does not make any ring instance easier and also because Mathlib’s algebraic hierarchy goes through semirings which are like rings but without opposites so that the proof below does not work for them. What we gain here, besides a nice exercise if you have never seen it, is an example of building an instance using the syntax that allows to provide a parent structure as an instance parameter and then supply the extra fields. Here the Ring₃ R argument supplies anything AddCommGroup₃ R wants except for add\_comm.

    class Ring₃ (R : Type) extends AddGroup₃ R, Monoid₃ R, MulZeroClass R where
      /-- Multiplication is left distributive over addition -/
      left_distrib : ∀ a b c : R, a * (b + c) = a * b + a * c
      /-- Multiplication is right distributive over addition -/
      right_distrib : ∀ a b c : R, (a + b) * c = a * c + b * c

    instance {R : Type} [Ring₃ R] : AddCommGroup₃ R :=
    { add_comm := by
        sorry }

Of course we can also build concrete instances, such as a ring structure on integers (of course the instance below uses that all the work is already done in Mathlib).

    instance : Ring₃ ℤ where
      add := (· + ·)
      add_assoc₃ := add_assoc
      zero := 0
      zero_add := by simp
      add_zero := by simp
      neg := (- ·)
      neg_add := by simp
      mul := (· * ·)
      mul_assoc₃ := mul_assoc
      one := 1
      one_mul := by simp
      mul_one := by simp
      zero_mul := by simp
      mul_zero := by simp
      left_distrib := Int.mul_add
      right_distrib := Int.add_mul

As an exercise you can now set up a simple hierarchy for order relations, including a class for ordered commutative monoids, which have both a partial order and a commutative monoid structure such that <span class="pre">`∀`</span>` `<span class="pre">`a`</span>` `<span class="pre">`b`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α,`</span>` `<span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`b`</span>` `<span class="pre">`→`</span>` `<span class="pre">`∀`</span>` `<span class="pre">`c`</span>` `<span class="pre">`:`</span>` `<span class="pre">`α,`</span>` `<span class="pre">`c`</span>` `<span class="pre">`*`</span>` `<span class="pre">`a`</span>` `<span class="pre">`≤`</span>` `<span class="pre">`c`</span>` `<span class="pre">`*`</span>` `<span class="pre">`b`</span>. Of course you need to add fields and maybe <span class="pre">`extends`</span> clauses to the following classes.

    class LE₁ (α : Type) where
      /-- The Less-or-Equal relation. -/
      le : α → α → Prop

    @[inherit_doc] infix:50 " ≤₁ " => LE₁.le

    class Preorder₁ (α : Type)

    class PartialOrder₁ (α : Type)

    class OrderedCommMonoid₁ (α : Type)

    instance : OrderedCommMonoid₁ ℕ where

We now want to discuss algebraic structures involving several types. The prime example is modules over rings. If you don’t know what is a module, you can pretend it means vector space and think that all our rings are fields. Those structures are commutative additive groups equipped with a scalar multiplication by elements of some ring.

We first define the data-carrying type class of scalar multiplication by some type <span class="pre">`α`</span> on some type <span class="pre">`β`</span>, and give it a right associative notation.

    class SMul₃ (α : Type) (β : Type) where
      /-- Scalar multiplication -/
      smul : α → β → β

    infixr:73 " • " => SMul₃.smul

Then we can define modules (again think about vector spaces if you don’t know what is a module).

    class Module₁ (R : Type) [Ring₃ R] (M : Type) [AddCommGroup₃ M] extends SMul₃ R M where
      zero_smul : ∀ m : M, (0 : R) • m = 0
      one_smul : ∀ m : M, (1 : R) • m = m
      mul_smul : ∀ (a b : R) (m : M), (a * b) • m = a • b • m
      add_smul : ∀ (a b : R) (m : M), (a + b) • m = a • m + b • m
      smul_add : ∀ (a : R) (m n : M), a • (m + n) = a • m + a • n

There is something interesting going on here. While it isn’t too surprising that the ring structure on <span class="pre">`R`</span> is a parameter in this definition, you probably expected <span class="pre">`AddCommGroup₃`</span>` `<span class="pre">`M`</span> to be part of the <span class="pre">`extends`</span> clause just as <span class="pre">`SMul₃`</span>` `<span class="pre">`R`</span>` `<span class="pre">`M`</span> is. Trying to do that would lead to a mysterious sounding error message: <span class="pre">`cannot`</span>` `<span class="pre">`find`</span>` `<span class="pre">`synthesization`</span>` `<span class="pre">`order`</span>` `<span class="pre">`for`</span>` `<span class="pre">`instance`</span>` `<span class="pre">`Module₁.toAddCommGroup₃`</span>` `<span class="pre">`with`</span>` `<span class="pre">`type`</span>` `<span class="pre">`(R`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[inst`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Ring₃`</span>` `<span class="pre">`R]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`{M`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type}`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[self`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Module₁`</span>` `<span class="pre">`R`</span>` `<span class="pre">`M]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`AddCommGroup₃`</span>` `<span class="pre">`M`</span>` `<span class="pre">`all`</span>` `<span class="pre">`remaining`</span>` `<span class="pre">`arguments`</span>` `<span class="pre">`have`</span>` `<span class="pre">`metavariables:`</span>` `<span class="pre">`Ring₃`</span>` `<span class="pre">`?R`</span>` `<span class="pre">`@Module₁`</span>` `<span class="pre">`?R`</span>` `<span class="pre">`?inst✝`</span>` `<span class="pre">`M`</span>. In order to understand this message, you need to remember that such an <span class="pre">`extends`</span> clause would lead to a field <span class="pre">`Module₃.toAddCommGroup₃`</span> marked as an instance. This instance would have the signature appearing in the error message: <span class="pre">`(R`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type)`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[inst`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Ring₃`</span>` `<span class="pre">`R]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`{M`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type}`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[self`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Module₁`</span>` `<span class="pre">`R`</span>` `<span class="pre">`M]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`AddCommGroup₃`</span>` `<span class="pre">`M`</span>. With such an instance in the type class database, each time Lean would look for a <span class="pre">`AddCommGroup₃`</span>` `<span class="pre">`M`</span> instance for some <span class="pre">`M`</span>, it would need to go hunting for a completely unspecified type <span class="pre">`R`</span> and a <span class="pre">`Ring₃`</span>` `<span class="pre">`R`</span> instance before embarking on the main quest of finding a <span class="pre">`Module₁`</span>` `<span class="pre">`R`</span>` `<span class="pre">`M`</span> instance. Those two side-quests are represented by the meta-variables mentioned in the error message and denoted by <span class="pre">`?R`</span> and <span class="pre">`?inst✝`</span> there. Such a <span class="pre">`Module₃.toAddCommGroup₃`</span> instance would then be a huge trap for the instance resolution procedure and then <span class="pre">`class`</span> command refuses to set it up.

What about <span class="pre">`extends`</span>` `<span class="pre">`SMul₃`</span>` `<span class="pre">`R`</span>` `<span class="pre">`M`</span> then? That one creates a field <span class="pre">`Module₁.toSMul₃`</span>` `<span class="pre">`:`</span>` `<span class="pre">`{R`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type}`</span>` `<span class="pre">`→`</span>`  `<span class="pre">`[inst`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Ring₃`</span>` `<span class="pre">`R]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`{M`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type}`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[inst_1`</span>` `<span class="pre">`:`</span>` `<span class="pre">`AddCommGroup₃`</span>` `<span class="pre">`M]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[self`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Module₁`</span>` `<span class="pre">`R`</span>` `<span class="pre">`M]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`SMul₃`</span>` `<span class="pre">`R`</span>` `<span class="pre">`M`</span> whose end result <span class="pre">`SMul₃`</span>` `<span class="pre">`R`</span>` `<span class="pre">`M`</span> mentions both <span class="pre">`R`</span> and <span class="pre">`M`</span> so this field can safely be used as an instance. The rule is easy to remember: each class appearing in the <span class="pre">`extends`</span> clause should mention every type appearing in the parameters.

Let us create our first module instance: a ring is a module over itself using its multiplication as a scalar multiplication.

    instance selfModule (R : Type) [Ring₃ R] : Module₁ R R where
      smul := fun r s ↦ r*s
      zero_smul := zero_mul
      one_smul := one_mul
      mul_smul := mul_assoc₃
      add_smul := Ring₃.right_distrib
      smul_add := Ring₃.left_distrib

As a second example, every abelian group is a module over <span class="pre">`ℤ`</span> (this is one of the reason to generalize the theory of vector spaces by allowing non-invertible scalars). First one can define scalar multiplication by a natural number for any type equipped with a zero and an addition: <span class="pre">`n`</span>` `<span class="pre">`•`</span>` `<span class="pre">`a`</span> is defined as <span class="pre">`a`</span>` `<span class="pre">`+`</span>` `<span class="pre">`⋯`</span>` `<span class="pre">`+`</span>` `<span class="pre">`a`</span> where <span class="pre">`a`</span> appears <span class="pre">`n`</span> times. Then this is extended to scalar multiplication by an integer by ensuring <span class="pre">`(-1)`</span>` `<span class="pre">`•`</span>` `<span class="pre">`a`</span>` `<span class="pre">`=`</span>` `<span class="pre">`-a`</span>.

    def nsmul₁ {M : Type*} [Zero M] [Add M] : ℕ → M → M
      | 0, _ => 0
      | n + 1, a => a + nsmul₁ n a

    def zsmul₁ {M : Type*} [Zero M] [Add M] [Neg M] : ℤ → M → M
      | Int.ofNat n, a => nsmul₁ n a
      | Int.negSucc n, a => -nsmul₁ n.succ a

Proving this gives rise to a module structure is a bit tedious and not interesting for the current discussion, so we will sorry all axioms. You are *not* asked to replace those sorries with proofs. If you insist on doing it then you will probably want to state and prove several intermediate lemmas about <span class="pre">`nsmul₁`</span> and <span class="pre">`zsmul₁`</span>.

    instance abGrpModule (A : Type) [AddCommGroup₃ A] : Module₁ ℤ A where
      smul := zsmul₁
      zero_smul := sorry
      one_smul := sorry
      mul_smul := sorry
      add_smul := sorry
      smul_add := sorry

A much more important issue is that we now have two module structures over the ring <span class="pre">`ℤ`</span> for <span class="pre">`ℤ`</span> itself: <span class="pre">`abGrpModule`</span>` `<span class="pre">`ℤ`</span> since <span class="pre">`ℤ`</span> is a abelian group, and <span class="pre">`selfModule`</span>` `<span class="pre">`ℤ`</span> since <span class="pre">`ℤ`</span> is a ring. Those two module structure correspond to the same abelian group structure, but it is not obvious that they have the same scalar multiplication. They actually do, but this isn’t true by definition, it requires a proof. This is very bad news for the type class instance resolution procedure and will lead to very frustrating failures for users of this hierarchy. When directly asked to find an instance, Lean will pick one, and we can see which one using:

    #synth Module₁ ℤ ℤ -- abGrpModule ℤ

But in a more indirect context it can happen that Lean infers the other one and then gets confused. This situation is known as a bad diamond. This has nothing to do with the diamond operation we used above, it refers to the way one can draw the paths from <span class="pre">`ℤ`</span> to its <span class="pre">`Module₁`</span>` `<span class="pre">`ℤ`</span> going through either <span class="pre">`AddCommGroup₃`</span>` `<span class="pre">`ℤ`</span> or <span class="pre">`Ring₃`</span>` `<span class="pre">`ℤ`</span>.

It is important to understand that not all diamonds are bad. In fact there are diamonds everywhere in Mathlib, and also in this chapter. Already at the very beginning we saw one can go from <span class="pre">`Monoid₁`</span>` `<span class="pre">`α`</span> to <span class="pre">`Dia₁`</span>` `<span class="pre">`α`</span> through either <span class="pre">`Semigroup₁`</span>` `<span class="pre">`α`</span> or <span class="pre">`DiaOneClass₁`</span>` `<span class="pre">`α`</span> and thanks to the work done by the <span class="pre">`class`</span> command, the resulting two <span class="pre">`Dia₁`</span>` `<span class="pre">`α`</span> instances are definitionally equal. In particular a diamond having a <span class="pre">`Prop`</span>-valued class at the bottom cannot be bad since any two proofs of the same statement are definitionally equal.

But the diamond we created with modules is definitely bad. The offending piece is the <span class="pre">`smul`</span> field which is data, not a proof, and we have two constructions that are not definitionally equal. The robust way of fixing this issue is to make sure that going from a rich structure to a poor structure is always done by forgetting data, not by defining data. This well-known pattern has been named “forgetful inheritance” and extensively discussed in <a href="https://inria.hal.science/hal-02463336v2" class="reference external">https://inria.hal.science/hal-02463336v2</a>.

In our concrete case, we can modify the definition of <span class="pre">`AddMonoid₃`</span> to include a <span class="pre">`nsmul`</span> data field and some <span class="pre">`Prop`</span>-valued fields ensuring this operation is provably the one we constructed above. Those fields are given default values using <span class="pre">`:=`</span> after their type in the definition below. Thanks to these default values, most instances would be constructed exactly as with our previous definitions. But in the special case of <span class="pre">`ℤ`</span> we will be able to provide specific values.

    class AddMonoid₄ (M : Type) extends AddSemigroup₃ M, AddZeroClass M where
      /-- Multiplication by a natural number. -/
      nsmul : ℕ → M → M := nsmul₁
      /-- Multiplication by `(0 : ℕ)` gives `0`. -/
      nsmul_zero : ∀ x, nsmul 0 x = 0 := by intros; rfl
      /-- Multiplication by `(n + 1 : ℕ)` behaves as expected. -/
      nsmul_succ : ∀ (n : ℕ) (x), nsmul (n + 1) x = x + nsmul n x := by intros; rfl

    instance mySMul {M : Type} [AddMonoid₄ M] : SMul ℕ M := ⟨AddMonoid₄.nsmul⟩

Let us check we can still construct a product monoid instance without providing the <span class="pre">`nsmul`</span> related fields.

    instance (M N : Type) [AddMonoid₄ M] [AddMonoid₄ N] : AddMonoid₄ (M × N) where
      add := fun p q ↦ (p.1 + q.1, p.2 + q.2)
      add_assoc₃ := fun a b c ↦ by ext <;> apply add_assoc₃
      zero := (0, 0)
      zero_add := fun a ↦ by ext <;> apply zero_add
      add_zero := fun a ↦ by ext <;> apply add_zero

And now let us handle the special case of <span class="pre">`ℤ`</span> where we want to build <span class="pre">`nsmul`</span> using the coercion of <span class="pre">`ℕ`</span> to <span class="pre">`ℤ`</span> and the multiplication on <span class="pre">`ℤ`</span>. Note in particular how the proof fields contain more work than in the default value above.

    instance : AddMonoid₄ ℤ where
      add := (· + ·)
      add_assoc₃ := Int.add_assoc
      zero := 0
      zero_add := Int.zero_add
      add_zero := Int.add_zero
      nsmul := fun n m ↦ (n : ℤ) * m
      nsmul_zero := Int.zero_mul
      nsmul_succ := fun n m ↦ show (n + 1 : ℤ) * m = m + n * m
        by rw [Int.add_mul, Int.add_comm, Int.one_mul]

Let us check we solved our issue. Because Lean already has a definition of scalar multiplication of a natural number and an integer, and we want to make sure our instance is used, we won’t use the <span class="pre">`•`</span> notation but call <span class="pre">`SMul.mul`</span> and explicitly provide our instance defined above.

    example (n : ℕ) (m : ℤ) : SMul.smul (self := mySMul) n m = n * m := rfl

This story then continues with incorporating a <span class="pre">`zsmul`</span> field into the definition of groups and similar tricks. You are now ready to read the definition of monoids, groups, rings and modules in Mathlib. There are more complicated than what we have seen here, because they are part of a huge hierarchy, but all principles have been explained above.

As an exercise, you can come back to the order relation hierarchy you built above and try to incorporate a type class <span class="pre">`LT₁`</span> carrying the Less-Than notation <span class="pre">`<₁`</span> and make sure that every preorder comes with a <span class="pre">`<₁`</span> which has a default value built from <span class="pre">`≤₁`</span> and a <span class="pre">`Prop`</span>-valued field asserting the natural relation between those two comparison operators.

<span id="section-hierarchies-morphisms"></span>

## <span class="section-number">8.2. </span>Morphisms<a href="#morphisms" class="headerlink" title="Link to this heading"></a>

So far in this chapter, we discussed how to create a hierarchy of mathematical structures. But defining structures is not really completed until we have morphisms. There are two main approaches here. The most obvious one is to define a predicate on functions.

    def isMonoidHom₁ [Monoid G] [Monoid H] (f : G → H) : Prop :=
      f 1 = 1 ∧ ∀ g g', f (g * g') = f g * f g'

In this definition, it is a bit unpleasant to use a conjunction. In particular users will need to remember the ordering we chose when they want to access the two conditions. So we could use a structure instead.

    structure isMonoidHom₂ [Monoid G] [Monoid H] (f : G → H) : Prop where
      map_one : f 1 = 1
      map_mul : ∀ g g', f (g * g') = f g * f g'

Once we are here, it is even tempting to make it a class and use the type class instance resolution procedure to automatically infer <span class="pre">`isMonoidHom₂`</span> for complicated functions out of instances for simpler functions. For instance a composition of monoid morphisms is a monoid morphism and this seems like a useful instance. However such an instance would be very tricky for the resolution procedure since it would need to hunt down <span class="pre">`g`</span>` `<span class="pre">`∘`</span>` `<span class="pre">`f`</span> everywhere. Seeing it failing in <span class="pre">`g`</span>` `<span class="pre">`(f`</span>` `<span class="pre">`x)`</span> would be very frustrating. More generally one must always keep in mind that recognizing which function is applied in a given expression is a very difficult problem, called the “higher-order unification problem”. So Mathlib does not use this class approach.

A more fundamental question is whether we use predicates as above (using either a <span class="pre">`def`</span> or a <span class="pre">`structure`</span>) or use structures bundling a function and predicates. This is partly a psychological issue. It is extremely rare to consider a function between monoids that is not a morphism. It really feels like “monoid morphism” is not an adjective you can assign to a bare function, it is a noun. On the other hand one can argue that a continuous function between topological spaces is really a function that happens to be continuous. This is one reason why Mathlib has a <span class="pre">`Continuous`</span> predicate. For instance you can write:

    example : Continuous (id : ℝ → ℝ) := continuous_id

We still have bundles of continuous functions, which are convenient for instance to put a topology on a space of continuous functions, but they are not the primary tool to work with continuity.

By contrast, morphisms between monoids (or other algebraic structures) are bundled as in:

    @[ext]
    structure MonoidHom₁ (G H : Type) [Monoid G] [Monoid H]  where
      toFun : G → H
      map_one : toFun 1 = 1
      map_mul : ∀ g g', toFun (g * g') = toFun g * toFun g'

Of course we don’t want to type <span class="pre">`toFun`</span> everywhere so we register a coercion using the <span class="pre">`CoeFun`</span> type class. Its first argument is the type we want to coerce to a function. The second argument describes the target function type. In our case it is always <span class="pre">`G`</span>` `<span class="pre">`→`</span>` `<span class="pre">`H`</span> for every <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`MonoidHom₁`</span>` `<span class="pre">`G`</span>` `<span class="pre">`H`</span>. We also tag <span class="pre">`MonoidHom₁.toFun`</span> with the <span class="pre">`coe`</span> attribute to make sure it is displayed almost invisibly in the tactic state, simply by a <span class="pre">`↑`</span> prefix.

    instance [Monoid G] [Monoid H] : CoeFun (MonoidHom₁ G H) (fun _ ↦ G → H) where
      coe := MonoidHom₁.toFun

    attribute [coe] MonoidHom₁.toFun

Let us check we can indeed apply a bundled monoid morphism to an element.

    example [Monoid G] [Monoid H] (f : MonoidHom₁ G H) : f 1 = 1 :=  f.map_one

We can do the same with other kind of morphisms until we reach ring morphisms.

    @[ext]
    structure AddMonoidHom₁ (G H : Type) [AddMonoid G] [AddMonoid H]  where
      toFun : G → H
      map_zero : toFun 0 = 0
      map_add : ∀ g g', toFun (g + g') = toFun g + toFun g'

    instance [AddMonoid G] [AddMonoid H] : CoeFun (AddMonoidHom₁ G H) (fun _ ↦ G → H) where
      coe := AddMonoidHom₁.toFun

    attribute [coe] AddMonoidHom₁.toFun

    @[ext]
    structure RingHom₁ (R S : Type) [Ring R] [Ring S] extends MonoidHom₁ R S, AddMonoidHom₁ R S

There are a couple of issues about this approach. A minor one is we don’t quite know where to put the <span class="pre">`coe`</span> attribute since the <span class="pre">`RingHom₁.toFun`</span> does not exist, the relevant function is <span class="pre">`MonoidHom₁.toFun`</span>` `<span class="pre">`∘`</span>` `<span class="pre">`RingHom₁.toMonoidHom₁`</span> which is not a declaration that can be tagged with an attribute (but we could still define a <span class="pre">`CoeFun`</span>`  `<span class="pre">`(RingHom₁`</span>` `<span class="pre">`R`</span>` `<span class="pre">`S)`</span>` `<span class="pre">`(fun`</span>` `<span class="pre">`_`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`R`</span>` `<span class="pre">`→`</span>` `<span class="pre">`S)`</span> instance). A much more important one is that lemmas about monoid morphisms won’t directly apply to ring morphisms. This leaves the alternative of either juggling with <span class="pre">`RingHom₁.toMonoidHom₁`</span> each time we want to apply a monoid morphism lemma or restate every such lemmas for ring morphisms. Neither option is appealing so Mathlib uses a new hierarchy trick here. The idea is to define a type class for objects that are at least monoid morphisms, instantiate that class with both monoid morphisms and ring morphisms and use it to state every lemma. In the definition below, <span class="pre">`F`</span> could be <span class="pre">`MonoidHom₁`</span>` `<span class="pre">`M`</span>` `<span class="pre">`N`</span>, or <span class="pre">`RingHom₁`</span>` `<span class="pre">`M`</span>` `<span class="pre">`N`</span> if <span class="pre">`M`</span> and <span class="pre">`N`</span> have a ring structure.

    class MonoidHomClass₁ (F : Type) (M N : Type) [Monoid M] [Monoid N] where
      toFun : F → M → N
      map_one : ∀ f : F, toFun f 1 = 1
      map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

However there is a problem with the above implementation. We haven’t registered a coercion to function instance yet. Let us try to do it now.

    def badInst [Monoid M] [Monoid N] [MonoidHomClass₁ F M N] : CoeFun F (fun _ ↦ M → N) where
      coe := MonoidHomClass₁.toFun

Making this an instance would be bad. When faced with something like <span class="pre">`f`</span>` `<span class="pre">`x`</span> where the type of <span class="pre">`f`</span> is not a function type, Lean will try to find a <span class="pre">`CoeFun`</span> instance to coerce <span class="pre">`f`</span> into a function. The above function has type: <span class="pre">`{M`</span>` `<span class="pre">`N`</span>` `<span class="pre">`F`</span>` `<span class="pre">`:`</span>` `<span class="pre">`Type}`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[Monoid`</span>` `<span class="pre">`M]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[Monoid`</span>` `<span class="pre">`N]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`[MonoidHomClass₁`</span>` `<span class="pre">`F`</span>` `<span class="pre">`M`</span>` `<span class="pre">`N]`</span>` `<span class="pre">`→`</span>` `<span class="pre">`CoeFun`</span>` `<span class="pre">`F`</span>` `<span class="pre">`(fun`</span>` `<span class="pre">`x`</span>` `<span class="pre">`↦`</span>` `<span class="pre">`M`</span>` `<span class="pre">`→`</span>` `<span class="pre">`N)`</span> so, when it trying to apply it, it wouldn’t be a priori clear to Lean in which order the unknown types <span class="pre">`M`</span>, <span class="pre">`N`</span> and <span class="pre">`F`</span> should be inferred. This is a kind of bad instance that is slightly different from the one we saw already, but it boils down to the same issue: without knowing <span class="pre">`M`</span>, Lean would have to search for a monoid instance on an unknown type, hence hopelessly try *every* monoid instance in the database. If you are curious to see the effect of such an instance you can type <span class="pre">`set_option`</span>` `<span class="pre">`synthInstance.checkSynthOrder`</span>` `<span class="pre">`false`</span>` `<span class="pre">`in`</span> on top of the above declaration, replace <span class="pre">`def`</span>` `<span class="pre">`badInst`</span> with <span class="pre">`instance`</span>, and look for random failures in this file.

Here the solution is easy, we need to tell Lean to first search what is <span class="pre">`F`</span> and then deduce <span class="pre">`M`</span> and <span class="pre">`N`</span>. This is done using the <span class="pre">`outParam`</span> function. This function is defined as the identity function, but is still recognized by the type class machinery and triggers the desired behavior. Hence we can retry defining our class, paying attention to the <span class="pre">`outParam`</span> function:

    class MonoidHomClass₂ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] where
      toFun : F → M → N
      map_one : ∀ f : F, toFun f 1 = 1
      map_mul : ∀ f g g', toFun f (g * g') = toFun f g * toFun f g'

    instance [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] : CoeFun F (fun _ ↦ M → N) where
      coe := MonoidHomClass₂.toFun

    attribute [coe] MonoidHomClass₂.toFun

Now we can proceed with our plan to instantiate this class.

    instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₂ (MonoidHom₁ M N) M N where
      toFun := MonoidHom₁.toFun
      map_one := fun f ↦ f.map_one
      map_mul := fun f ↦ f.map_mul

    instance (R S : Type) [Ring R] [Ring S] : MonoidHomClass₂ (RingHom₁ R S) R S where
      toFun := fun f ↦ f.toMonoidHom₁.toFun
      map_one := fun f ↦ f.toMonoidHom₁.map_one
      map_mul := fun f ↦ f.toMonoidHom₁.map_mul

As promised every lemma we prove about <span class="pre">`f`</span>` `<span class="pre">`:`</span>` `<span class="pre">`F`</span> assuming an instance of <span class="pre">`MonoidHomClass₁`</span>` `<span class="pre">`F`</span> will apply both to monoid morphisms and ring morphisms. Let us see an example lemma and check it applies to both situations.

    lemma map_inv_of_inv [Monoid M] [Monoid N] [MonoidHomClass₂ F M N] (f : F) {m m' : M} (h : m*m' = 1) :
        f m * f m' = 1 := by
      rw [← MonoidHomClass₂.map_mul, h, MonoidHomClass₂.map_one]

    example [Monoid M] [Monoid N] (f : MonoidHom₁ M N) {m m' : M} (h : m*m' = 1) : f m * f m' = 1 :=
    map_inv_of_inv f h

    example [Ring R] [Ring S] (f : RingHom₁ R S) {r r' : R} (h : r*r' = 1) : f r * f r' = 1 :=
    map_inv_of_inv f h

At first sight, it may look like we got back to our old bad idea of making <span class="pre">`MonoidHom₁`</span> a class. But we haven’t. Everything is shifted one level of abstraction up. The type class resolution procedure won’t be looking for functions, it will be looking for either <span class="pre">`MonoidHom₁`</span> or <span class="pre">`RingHom₁`</span>.

One remaining issue with our approach is the presence of repetitive code around the <span class="pre">`toFun`</span> field and the corresponding <span class="pre">`CoeFun`</span> instance and <span class="pre">`coe`</span> attribute. It would also be better to record that this pattern is used only for functions with extra properties, meaning that the coercion to functions should be injective. So Mathlib adds one more layer of abstraction with the base class <span class="pre">`DFunLike`</span> (where “DFun” stands for dependent function). Let us redefine our <span class="pre">`MonoidHomClass`</span> on top of this base layer.

    class MonoidHomClass₃ (F : Type) (M N : outParam Type) [Monoid M] [Monoid N] extends
        DFunLike F M (fun _ ↦ N) where
      map_one : ∀ f : F, f 1 = 1
      map_mul : ∀ (f : F) g g', f (g * g') = f g * f g'

    instance (M N : Type) [Monoid M] [Monoid N] : MonoidHomClass₃ (MonoidHom₁ M N) M N where
      coe := MonoidHom₁.toFun
      coe_injective' _ _ := MonoidHom₁.ext
      map_one := MonoidHom₁.map_one
      map_mul := MonoidHom₁.map_mul

Of course the hierarchy of morphisms does not stop here. We could go on and define a class <span class="pre">`RingHomClass₃`</span> extending <span class="pre">`MonoidHomClass₃`</span> and instantiate it on <span class="pre">`RingHom`</span> and then later on <span class="pre">`AlgebraHom`</span> (algebras are rings with some extra structure). But we’ve covered the main formalization ideas used in Mathlib for morphisms and you should be ready to understand how morphisms are defined in Mathlib.

As an exercise, you should try to define your class of bundled order-preserving function between ordered types, and then order preserving monoid morphisms. This is for training purposes only. Like continuous functions, order preserving functions are primarily unbundled in Mathlib where they are defined by the <span class="pre">`Monotone`</span> predicate. Of course you need to complete the class definitions below.

    @[ext]
    structure OrderPresHom (α β : Type) [LE α] [LE β] where
      toFun : α → β
      le_of_le : ∀ a a', a ≤ a' → toFun a ≤ toFun a'

    @[ext]
    structure OrderPresMonoidHom (M N : Type) [Monoid M] [LE M] [Monoid N] [LE N] extends
    MonoidHom₁ M N, OrderPresHom M N

    class OrderPresHomClass (F : Type) (α β : outParam Type) [LE α] [LE β]

    instance (α β : Type) [LE α] [LE β] : OrderPresHomClass (OrderPresHom α β) α β where

    instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
        OrderPresHomClass (OrderPresMonoidHom α β) α β where

    instance (α β : Type) [LE α] [Monoid α] [LE β] [Monoid β] :
        MonoidHomClass₃ (OrderPresMonoidHom α β) α β
      := sorry

<span id="section-hierarchies-subobjects"></span>

## <span class="section-number">8.3. </span>Sub-objects<a href="#sub-objects" class="headerlink" title="Link to this heading"></a>

After defining some algebraic structure and its morphisms, the next step is to consider sets that inherit this algebraic structure, for instance subgroups or subrings. This largely overlaps with our previous topic. Indeed a set in <span class="pre">`X`</span> is implemented as a function from <span class="pre">`X`</span> to <span class="pre">`Prop`</span> so sub-objects are function satisfying a certain predicate. Hence we can reuse of lot of the ideas that led to the <span class="pre">`DFunLike`</span> class and its descendants. We won’t reuse <span class="pre">`DFunLike`</span> itself because this would break the abstraction barrier from <span class="pre">`Set`</span>` `<span class="pre">`X`</span> to <span class="pre">`X`</span>` `<span class="pre">`→`</span>` `<span class="pre">`Prop`</span>. Instead there is a <span class="pre">`SetLike`</span> class. Instead of wrapping an injection into a function type, that class wraps an injection into a <span class="pre">`Set`</span> type and defines the corresponding coercion and <span class="pre">`Membership`</span> instance.

    @[ext]
    structure Submonoid₁ (M : Type) [Monoid M] where
      /-- The carrier of a submonoid. -/
      carrier : Set M
      /-- The product of two elements of a submonoid belongs to the submonoid. -/
      mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
      /-- The unit element belongs to the submonoid. -/
      one_mem : 1 ∈ carrier

    /-- Submonoids in `M` can be seen as sets in `M`. -/
    instance [Monoid M] : SetLike (Submonoid₁ M) M where
      coe := Submonoid₁.carrier
      coe_injective' _ _ := Submonoid₁.ext

Equipped with the above <span class="pre">`SetLike`</span> instance, we can already state naturally that a submonoid <span class="pre">`N`</span> contains <span class="pre">`1`</span> without using <span class="pre">`N.carrier`</span>. We can also silently treat <span class="pre">`N`</span> as a set in <span class="pre">`M`</span> as take its direct image under a map.

    example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

    example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N

We also have a coercion to <span class="pre">`Type`</span> which uses <span class="pre">`Subtype`</span> so, given a submonoid <span class="pre">`N`</span> we can write a parameter <span class="pre">`(x`</span>` `<span class="pre">`:`</span>` `<span class="pre">`N)`</span> which can be coerced to an element of <span class="pre">`M`</span> belonging to <span class="pre">`N`</span>.

    example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property

Using this coercion to <span class="pre">`Type`</span> we can also tackle the task of equipping a submonoid with a monoid structure. We will use the coercion from the type associated to <span class="pre">`N`</span> as above, and the lemma <span class="pre">`SetCoe.ext`</span> asserting this coercion is injective. Both are provided by the <span class="pre">`SetLike`</span> instance.

    instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
      mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
      mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
      one := ⟨1, N.one_mem⟩
      one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
      mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))

Note that, in the above instance, instead of using the coercion to <span class="pre">`M`</span> and calling the <span class="pre">`property`</span> field, we could have used destructuring binders as follows.

    example [Monoid M] (N : Submonoid₁ M) : Monoid N where
      mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
      mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
      one := ⟨1, N.one_mem⟩
      one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
      mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)

In order to apply lemmas about submonoids to subgroups or subrings, we need a class, just like for morphisms. Note this class take a <span class="pre">`SetLike`</span> instance as a parameter so it does not need a carrier field and can use the membership notation in its fields.

    class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
      mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
      one_mem : ∀ s : S, 1 ∈ s

    instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
      mul_mem := Submonoid₁.mul_mem
      one_mem := Submonoid₁.one_mem

As an exercise you should define a <span class="pre">`Subgroup₁`</span> structure, endow it with a <span class="pre">`SetLike`</span> instance and a <span class="pre">`SubmonoidClass₁`</span> instance, put a <span class="pre">`Group`</span> instance on the subtype associated to a <span class="pre">`Subgroup₁`</span> and define a <span class="pre">`SubgroupClass₁`</span> class.

Another very important thing to know about subobjects of a given algebraic object in Mathlib always form a complete lattice, and this structure is used a lot. For instance you may look for the lemma saying that an intersection of submonoids is a submonoid. But this won’t be a lemma, this will be an infimum construction. Let us do the case of two submonoids.

    instance [Monoid M] : Min (Submonoid₁ M) :=
      ⟨fun S₁ S₂ ↦
        { carrier := S₁ ∩ S₂
          one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
          mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩

This allows to get the intersections of two submonoids as a submonoid.

    example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N ⊓ P

You may think it’s a shame that we had to use the inf symbol <span class="pre">`⊓`</span> in the above example instead of the intersection symbol <span class="pre">`∩`</span>. But think about the supremum. The union of two submonoids is not a submonoid. However submonoids still form a lattice (even a complete one). Actually <span class="pre">`N`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`P`</span> is the submonoid generated by the union of <span class="pre">`N`</span> and <span class="pre">`P`</span> and of course it would be very confusing to denote it by <span class="pre">`N`</span>` `<span class="pre">`∪`</span>` `<span class="pre">`P`</span>. So you can see the use of <span class="pre">`N`</span>` `<span class="pre">`⊓`</span>` `<span class="pre">`P`</span> as much more consistent. It is also a lot more consistent across various kind of algebraic structures. It may look a bit weird at first to see the sum of two vector subspace <span class="pre">`E`</span> and <span class="pre">`F`</span> denoted by <span class="pre">`E`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`F`</span> instead of <span class="pre">`E`</span>` `<span class="pre">`+`</span>` `<span class="pre">`F`</span>. But you will get used to it. And soon you will consider the <span class="pre">`E`</span>` `<span class="pre">`+`</span>` `<span class="pre">`F`</span> notation as a distraction emphasizing the anecdotal fact that elements of <span class="pre">`E`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`F`</span> can be written as a sum of an element of <span class="pre">`E`</span> and an element of <span class="pre">`F`</span> instead of emphasizing the fundamental fact that <span class="pre">`E`</span>` `<span class="pre">`⊔`</span>` `<span class="pre">`F`</span> is the smallest vector subspace containing both <span class="pre">`E`</span> and <span class="pre">`F`</span>.

Our last topic for this chapter is that of quotients. Again we want to explain how convenient notation are built and code duplication is avoided in Mathlib. Here the main device is the <span class="pre">`HasQuotient`</span> class which allows notations like <span class="pre">`M`</span>` `<span class="pre">`⧸`</span>` `<span class="pre">`N`</span>. Beware the quotient symbol <span class="pre">`⧸`</span> is a special unicode character, not a regular ASCII division symbol.

As an example, we will build the quotient of a commutative monoid by a submonoid, leave proofs to you. In the last example, you can use <span class="pre">`Setoid.refl`</span> but it won’t automatically pick up the relevant <span class="pre">`Setoid`</span> structure. You can fix this issue by providing all arguments using the <span class="pre">`@`</span> syntax, as in <span class="pre">`@Setoid.refl`</span>` `<span class="pre">`M`</span>` `<span class="pre">`N.Setoid`</span>.

    def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
      r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
      iseqv := {
        refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
        symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
        trans := by
          sorry
      }

    instance [CommMonoid M] : HasQuotient M (Submonoid M) where
      quotient' := fun N ↦ Quotient N.Setoid

    def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

    instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
      mul := Quotient.map₂ (· * ·) (by
          sorry
            )
      mul_assoc := by
          sorry
      one := QuotientMonoid.mk N 1
      one_mul := by
          sorry
      mul_one := by
          sorry
