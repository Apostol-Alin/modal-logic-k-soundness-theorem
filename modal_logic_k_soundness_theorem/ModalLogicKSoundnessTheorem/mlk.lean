import Mathlib.Data.Set.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.style.commandStart false
set_option linter.style.cdot false


/- This is inspired from lab5.lean from hcheval.
   Link: https://github.com/hcheval/Lmas20256/blob/main/Lmas20256/Lab5.lean -/

inductive Formula where
| var : String → Formula
| imp : Formula → Formula → Formula
| neg : Formula → Formula
| box : Formula → Formula

namespace Formula

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

/- We need to define a definition for the proof system as in inductive type: Proof: Formula → Type -/
/- This is used to proove tautologies are KProovable, since we make the assumption that all tautologies are axioms of K -/
structure Morphism (f : Formula → Prop) : Prop where
  respects_implication : ∀ (φ ψ : Formula), f (φ ⇒ ψ) ↔ (f φ → f ψ)
  respects_neg : ∀ (φ : Formula), f ( ∼φ ) ↔ ¬f (φ)

section

  variable {f : Formula → Prop} (φ ψ : Formula)

  theorem respects_false (hf : Morphism f) : f ⊥ ↔ False := by
    constructor
    . intros h
      unfold bot at h
      rw [ hf.respects_neg ] at h
      unfold top at h
      rw [ hf.respects_implication ] at h
      rw [ Classical.not_imp ] at h
      have left := h.left
      have right := h.right
      contradiction
    . intros h_false
      trivial

  theorem respects_disj (hf : Morphism f) : f (φ ⋁ ψ) ↔ f φ ∨ f ψ := by
    constructor
    case mp =>
      unfold disj
      rw [ hf.respects_implication ]
      rw [ hf.respects_neg φ ]
      intros h
      by_cases ip : (f φ)
      . exact Or.inl ip
      . exact Or.inr (h ip)
    case mpr =>
      unfold disj
      rw [hf.respects_implication]
      rw [ hf.respects_neg φ ]
      intros h
      cases h
      case inl ip =>
        intros ih
        contradiction
      case inr ip =>
        intros neg
        trivial

  theorem respects_conj (hf : Morphism f) : f (φ ⋀ ψ) ↔ f φ ∧ f ψ := by
    constructor
    case mp =>
      unfold conj
      rw [ hf.respects_neg ((φ ⇒ ∼ ψ)) ]
      rw [ hf.respects_implication ]
      rw [ hf.respects_neg ψ ]
      intros h
      rw [ Classical.not_imp, Classical.not_not ] at h
      trivial
    case mpr =>
      unfold conj
      intros h
      rw [ hf.respects_neg ((φ ⇒ ∼ ψ)) ]
      rw [ hf.respects_implication ]
      rw [ hf.respects_neg ψ ]
      rw [ Classical.not_imp, Classical.not_not ]
      trivial

  theorem respects_iff (hf : Morphism f) : f (φ ⇔ ψ) ↔ (f φ ↔ f ψ ) := by
    constructor
    . unfold iff
      rw [ respects_conj _ _ hf]
      rw [ hf.respects_implication ]
      rw [ hf.respects_implication ]
      intros h
      constructor
      . exact h.left
      . exact h.right
    . unfold iff
      rw [ respects_conj _ _ hf ]
      rw [ hf.respects_implication ]
      rw [ hf.respects_implication ]
      intros h
      exact And.intro h.mp h.mpr

end

def IsTautology (φ : Formula) : Prop := ∀ (f : Formula → Prop), Morphism f → f φ

set_option hygiene false in prefix:100 "⊢K" => KProovable
inductive KProovable : Formula → Prop where
/- All propositional tautologies are axioms of K -/
/- Here we accest Formulas as tautologies because tautologies may contain modalities
   For example ⋄q ⋁ ∼⋄q-/
| tautology {φ : Formula } : IsTautology φ → ⊢K φ
/- The rules of proof of K -/
| modusPonens {φ ψ : Formula} : ⊢K φ → ⊢K (φ ⇒ ψ) → ⊢K ψ
| generalization {φ : Formula} : ⊢K φ → ⊢K (□φ)
| K {φ ψ : Formula} : ⊢K ((φ ⇒ ψ) ⇒ (□φ ⇒ □ψ))

/- Let's define some propositions for the course and proove that they are KProovable -/

open KProovable

variable {p q r : Formula}

theorem tautology_1 : ⊢K ((p ⇒ q) ⋀ (q ⇒ r) ⇒ (p ⇒ r)) := by
  /- (p → q) ∧ (q → r) → (p → r) is a propositional tautology -/
  have I₁ : IsTautology ((p ⇒ q) ⋀ (q ⇒ r) ⇒ (p ⇒ r)) := by
    unfold IsTautology
    intros f hf
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ respects_conj _ _ hf ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    intros h_and hp
    exact h_and.right (h_and.left hp)
  exact tautology I₁

theorem tautology_2 : ⊢K ((p ⇒ q) ⇒ (q ⇒ r) ⇒ ((p ⇒ q) ⋀ (q ⇒ r)) ) := by
  /- (p → q) → (q → r) → ((p → q) ∧ (q → r)) is a propositional tautology -/
  have I₁ : IsTautology ((p ⇒ q) ⇒ (q ⇒ r) ⇒ ((p ⇒ q) ⋀ (q ⇒ r)) ) := by
    unfold IsTautology
    intros f hf
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ respects_conj _ _ hf ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    intros hpq hqr
    exact And.intro hpq hqr
  exact tautology I₁

theorem proposition_2_39 : ⊢K (p ⇒ q) → ⊢K (q ⇒ r) → ⊢K (p ⇒ r) := by
  intros hpq hqr
  have I₁ : ⊢K ((q ⇒ r) ⇒ ((p ⇒ q) ⋀ (q ⇒ r))) := modusPonens hpq tautology_2
  have I₂ : ⊢K ((p ⇒ q) ⋀ (q ⇒ r)) := modusPonens hqr I₁
  exact modusPonens I₂ tautology_1

theorem tautology_3 : ⊢K ( (p ⇒ q) ⋀ (q ⇒ r) ⇒ (p ⇒ q ⋀ r) ) := by
  /- (p → q) ∧ (q → r) → (p → q ∧ r) is a propositional tautology -/
  have I₁ : IsTautology ( (p ⇒ q) ⋀ (q ⇒ r) ⇒ (p ⇒ q ⋀ r) ) := by
    unfold IsTautology
    intros f hf
    rw [ hf.respects_implication ]
    rw [ respects_conj _ _ hf]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ respects_conj _ _ hf]
    intros h_and hp
    exact And.intro (h_and.left hp) (h_and.right (h_and.left hp))
  exact tautology I₁

theorem proposition_2_40 : ⊢K (p ⇒ q) → ⊢K (q ⇒ r) → ⊢K (p ⇒ q ⋀ r) := by
  intros hpq
  intros hqr
  have I₁ : ⊢K ( (q ⇒ r) ⇒ ((p ⇒ q) ⋀ (q ⇒ r)) ) := modusPonens hpq tautology_2
  have I₂ : ⊢K ( (p ⇒ q) ⋀ (q ⇒ r) ) := modusPonens hqr I₁
  exact modusPonens I₂ tautology_3

theorem tautology_4 : ⊢K ((p ⇒ (q ⇒ r)) ⇒ (p ⋀ q ⇒ r)) := by
  have I₁ : IsTautology ((p ⇒ (q ⇒ r)) ⇒ (p ⋀ q ⇒ r)) := by
    unfold IsTautology
    intros f hf
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ respects_conj _ _ hf ]
    intros hpqr h_and
    exact (hpqr h_and.left) h_and.right
  exact tautology I₁

theorem tautology_5 : ⊢K ((p ⋀ q ⇒ r) ⇒ (p ⇒ (q ⇒ r))) := by
  have I₁ : IsTautology ((p ⋀ q ⇒ r) ⇒ (p ⇒ (q ⇒ r))) := by
    unfold IsTautology
    intros f hf
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ respects_conj _ _ hf ]
    intros h hp hq
    exact h (And.intro hp hq)
  exact tautology I₁

theorem proposition_2_41 : ⊢K (p ⇒ (q ⇒ r)) ↔ ⊢K (p ⋀ q ⇒ r) := by
  constructor
  . intros h
    exact modusPonens h tautology_4
  . intros h
    exact modusPonens h tautology_5

theorem tautology_6 : ⊢K ((p ⇒ q) ⇒ (q ⇒ p) ⇒ (p ⇔ q)) := by
  have I₁ : IsTautology ((p ⇒ q) ⇒ (q ⇒ p) ⇒ (p ⇔ q)) := by
    unfold IsTautology
    intros f hf
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ hf.respects_implication ]
    rw [ respects_iff _ _ hf]
    intros hpq hqp
    apply Iff.intro
    . intros hp
      exact hpq hp
    . intros hq
      exact hqp hq
  exact tautology I₁

theorem proposition_2_42 : ⊢K (p ⇒ q) → ⊢K (q ⇒ p) → ⊢K (p ⇔ q) := by
  intros hpq hqp
  have I₁ : ⊢K ((q ⇒ p) ⇒ (p ⇔ q)) := modusPonens hpq tautology_6
  exact modusPonens hqp I₁

/- We need to provide now a defnition of the validity of a formula -/

/- First, define what a frame is -/
structure Frame where
  W : Type -- Worlds can be any type
  R : W → W → Prop -- The relation between two worlds: if R w v == true then we can say as in the course Rwv

/-
The notion of validity as described in the course:
Let ℱ be a frame and φ be a formula.
  * φ is valid a state (or world) in ℱ if φ is true at w in every model ℳ = (ℱ, V) based on ℱ
  * φ is valid in ℱ if it is valid at every state w in ℱ. Notation ℱ ⊩ φ
  * φ is valid in a class of models, 𝔽, if φ is valid at every frame in 𝔽, notation 𝔽 ⊩ φ
Now, from Blackburn+deRijke+Venema:
  * φ is valid (notation ⊩ φ) if it is valid in the class of all frames
-/

structure Model where
  ℱ : Frame
  V : String → ℱ.W → Prop

/- Let's see what it means for a fomula φ to be true in a model ℳ at a state w -/
/- A formula is true (or is satisfied) in ℳ at state w, notation ℳ, w ⊩ φ  -/

def satisfies (ℳ : Model) (w : ℳ.ℱ.W) : Formula → Prop
  | var p   => ℳ.V p w
  | neg φ   => ¬(satisfies ℳ w φ)
  | box φ   => ∀ v, ℳ.ℱ.R w v → satisfies ℳ v φ
  | imp φ ψ => (satisfies ℳ w φ) → (satisfies ℳ w ψ)

def IsValidInAState (φ : Formula) (frame : Frame) (w : frame.W) : Prop :=
  ∀ (ℳ : Model) , (h : ℳ.ℱ = frame) → satisfies ℳ (h ▸ w) φ

def IsValidInAFrame (φ : Formula) (ℱ : Frame) : Prop :=
  ∀ (w : ℱ.W), IsValidInAState φ ℱ w

def IsValidInAClassOfFrames (φ : Formula) (𝔽 : Set (Frame)): Prop :=
  ∀ ℱ ∈ 𝔽, IsValidInAFrame φ ℱ

def IsValid (φ : Formula) : Prop :=
  ∀ (ℱ : Frame), IsValidInAFrame φ ℱ

theorem example_2_19 : IsValid (⋄(p ⋁ q) ⇒ (⋄p ⋁ ⋄q)) := by
  unfold IsValid
  intros ℱ
  unfold IsValidInAFrame
  intros w
  unfold IsValidInAState
  intros ℳ h
  exact satisfies ℳ w


end Formula
