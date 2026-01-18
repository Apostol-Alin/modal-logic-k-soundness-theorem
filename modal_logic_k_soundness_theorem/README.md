# Modal logic K soundness theorem

Formalize the soundness theorem for modal logic K. The implementation should contain:

* A definition for the syntax as an inductive type `Formula`
* A definition for the proof system as an inductive type: `Proof : Formula -> Type`
* A definition of the validity of a formula
* A proof of the fact that `forall phi : Formula (exists p : Proof phi) -> |= phi`
