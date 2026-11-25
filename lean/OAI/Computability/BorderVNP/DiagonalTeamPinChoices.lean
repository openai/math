import OAI.Computability.BorderVNP.DiagonalNativeGuessImage

/-! # One substituted pin in the joint product of all team prefixes -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open RoutingISA RoutingISA.Pins

variable {R r t d link inner n : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    (ibase hbase starbase : Fin (R+1) → ℕ)

/-- Exact bit-vector type guessed by the physical preparation on this team. -/
abbrev TeamGuess (u : Fin (R+1)) :=
  Fin (G.pinLayout u (ibase u) (hbase u) (starbase u)).guessWidth → Bool

/-- At the joint preparation stage only team zero has a nonempty guess
width. All other teams have the unique empty assignment. -/
def Wiring.jointGuess : (∀ u, TeamGuess G ibase hbase starbase u) ≃ (Fin d → Bool) where
  toFun z := z 0
  invFun b u := if e : u = 0 then e ▸ (show TeamGuess G ibase hbase starbase 0 from b)
    else fun j => False.elim (by
      have ne : u.val ≠ 0 := fun h => e (Fin.ext h)
      have width : (G.pinLayout u (ibase u) (hbase u) (starbase u)).guessWidth = 0 := ite_eq_right ne
      exact (Nat.not_lt_zero j.val (width ▸ j.isLt)))
  left_inv z := by
    funext u
    by_cases h : u = 0
    · subst u; rfl
    · funext j
      exfalso
      have h' : u.val ≠ 0 := fun eq => h (Fin.ext eq)
      have width : (G.pinLayout u (ibase u) (hbase u) (starbase u)).guessWidth = 0 := ite_eq_right h'
      exact Nat.not_lt_zero j.val (width ▸ j.isLt)
  right_inv _ := rfl

/-- Separate the raw guessed pin and one native preparation return per
team. The post-pin state of each team is its actual state for this guess. -/
def Wiring.jointPrefixes (Prep : ∀ u, TeamGuess G ibase hbase starbase u → Type*) :
    (∀ u : Fin (R+1), Σ b : TeamGuess G ibase hbase starbase u, Prep u b) ≃
      (Σ b : Fin d → Bool, ∀ u, Prep u ((G.jointGuess ibase hbase starbase).symm b u)) :=
  let e := G.jointGuess ibase hbase starbase
  let a : (∀ u, Σ b, Prep u b) ≃ (Σ b : ∀ u, TeamGuess G ibase hbase starbase u, ∀ u, Prep u (b u)) :=
    { toFun := fun z => ⟨fun u => (z u).1,fun u => (z u).2⟩
      invFun := fun z u => ⟨z.1 u,z.2 u⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  a.trans (Equiv.sigmaCongrLeft' (β := fun b => ∀ u, Prep u (b u)) e)

end TeamContraction

end BorderVNP
end Computability
end OAI
