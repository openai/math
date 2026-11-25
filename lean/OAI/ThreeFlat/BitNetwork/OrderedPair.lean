import OAI.ThreeFlat.BitNetwork.OrderedGlue

namespace OAI
/-! # Joining two separately addressed input intervals -/

namespace ThreeFlat.BitNetwork.Ordered

open scoped BigOperators

variable {F : Type*} {a b : ℕ}

private structure One (F : Type*) (p : ℕ) where
  arity : ℕ
  net : BitNetwork F arity
  onto : Fin arity → BitSource 0 p

private def pairParts (A : BitNetwork F a) (B : BitNetwork F b) : Fin 2 → One F (a+b) :=
  ![⟨a,A,fun i => .pin (i.castAdd b)⟩,⟨b,B,fun i => .pin (Fin.natAdd a i)⟩]

def pair (A : BitNetwork F a) (B : BitNetwork F b) : BitNetwork F (a+b) :=
  glue (fun i => (pairParts A B i).net) (fun i => (pairParts A B i).onto)

theorem pair_eval [CommSemiring F] (A : BitNetwork F a) (B : BitNetwork F b) (x : Fin a → Bool) (y : Fin b → Bool) :
    (pair A B).eval (Fin.append x y) = A.eval x * B.eval y := by
  rw [pair,glue_eval,Fintype.sum_unique,Fin.prod_univ_two]
  simp [pairParts,BitSource.read]

theorem pair_cells (A : BitNetwork F a) (B : BitNetwork F b) : (pair A B).cells = A.cells+B.cells := by
  change (∑ i, (pairParts A B i).net.cells) = _
  rw [Fin.sum_univ_two]
  rfl

theorem pair_hidden (A : BitNetwork F a) (B : BitNetwork F b) : (pair A B).internal = A.internal+B.internal := by
  change 0+(∑ i, (pairParts A B i).net.internal) = _
  rw [Nat.zero_add,Fin.sum_univ_two]
  rfl

end ThreeFlat.BitNetwork.Ordered

end OAI
