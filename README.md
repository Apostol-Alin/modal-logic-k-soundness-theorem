# Modal logic K soundness theorem

Formalize the soundness theorem for modal logic K. The implementation should contain:

* A definition for the syntax as an inductive type `Formula`
* A definition for the proof system as an inductive type: `Proof : Formula → Type`
* A definition of the validity of a formula
* A proof of the fact that `∀ φ : Formula (∃ p : Proof φ) → ⊨ φ`

The implementation is found in `./ModalLogicKSoundnessTheorem/mlk.lean`.

1. Firstly, I defined the syntax for Modal Logic: Formulas as an inductive type:

```lean
inductive Formula where
| var : String → Formula
| imp : Formula → Formula → Formula
| neg : Formula → Formula
| box : Formula → Formula
```

Then I defined the other derivates:

```lean
prefix:max "□" => box
infixr:70 " ⇒ " => imp
prefix:100 "∼" => neg

def top : Formula := (var "p") ⇒ (var "p")
notation "⊤" => top

def bot : Formula := ∼⊤
notation "⊥" => bot

def diamond (φ : Formula) : Formula := ∼□(∼φ)

prefix:max "⋄" => diamond
def disj (φ ψ : Formula) : Formula := ((∼ φ) ⇒ ψ)
def conj (φ ψ : Formula) : Formula := ∼(φ ⇒ (∼ψ))

infixl:80 " ⋁ " => disj
infixl:80 " ⋀ " => conj

def iff (φ ψ : Formula) : Formula := ((φ ⇒ ψ) ⋀ (ψ ⇒ φ))

infixr:70 " ⇔ " => iff
```

2. For the proof system as an inductive type, `Proof : Formula -> Prop`:

```
inductive KProovable : Formula → Prop where
/- All propositional tautologies are axioms of K -/
/- Here we accest Formulas as tautologies because tautologies may contain modalities
   For example ⋄q ⋁ ∼⋄q-/
| tautology {φ : Formula } : IsTautology φ → ⊢K φ
/- The rules of proof of K -/
| modusPonens {φ ψ : Formula} : ⊢K φ → ⊢K (φ ⇒ ψ) → ⊢K ψ
| generalization {φ : Formula} : ⊢K φ → ⊢K (□φ)
| K {φ ψ : Formula} : ⊢K (□(φ ⇒ ψ) ⇒ (□φ ⇒ □ψ))
```

Since all propositional tautologies are considered KProovable, I need a way to define that. This was done by defining a function `IsTautology` which, given a formula, says if it is tautology or not, by taking into consideration every valuation with the condition that the valuation function is a morphism (e.g. ` ∀ (φ ψ : Formula), f (φ ⇒ ψ) ↔ (f φ → f ψ)`).

To check if the proof system works, I tried to proove some propositions for the course material after that.

3. For the notion of the validity of the formula, I had to define what a Frame is and what Model is.

```
structure Frame where
  W : Type -- Worlds can be any type
  R : W → W → Prop -- The relation between two worlds: if R w v == true then we can say as in the course Rwv

structure Model where
  ℱ : Frame
  V : String → ℱ.W → Prop
```

Then, a formula p is considered valid if it is valid in the class of all frames. That means, whichever the frame, a formula is valid in every state of that frame; then a formula is valid in a state of a frame if it is satisfiable in every model:

```
def satisfies (ℳ : Model) (w : ℳ.ℱ.W) : Formula → Prop
  | var p   => ℳ.V p w
  | neg φ   => ¬(satisfies ℳ w φ)
  | box φ   => ∀ v, ℳ.ℱ.R w v → satisfies ℳ v φ
  | imp φ ψ => (satisfies ℳ w φ) → (satisfies ℳ w ψ)

def IsValidInAState (φ : Formula) (frame : Frame) (w : frame.W) : Prop :=
  ∀ (ℳ : Model) , (h : ℳ.ℱ = frame) → satisfies ℳ (h ▸ w) φ

def IsValidInAFrame (φ : Formula) (ℱ : Frame) : Prop :=
  ∀ (w : ℱ.W), IsValidInAState φ ℱ w

def IsValid (φ : Formula) : Prop :=
  ∀ (ℱ : Frame), IsValidInAFrame φ ℱ
```

Then I prooved an example from the course to see how the notion of validity works:

```
theorem example_2_19 : ⊩ (⋄(p ⋁ q) ⇒ (⋄p ⋁ ⋄q))
```

4. The soundness theorem for modal logic K states that any formula provable in MLk is also valid.

```theorem soundness_theorem : ∀ {p : Formula}, ⊢K p → ⊩ p```
