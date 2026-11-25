import OAI.Computability.BorderVNP.CubeMeanRows
import OAI.Computability.BorderVNP.CubeLabelISAPassImage
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Row-major numbering of cable and data bins in the public label chooser -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.LabelTrial

open Cube.MeanChoice Finset
open scoped BigOperators

/-- Ordered pairs precede the single-label delivery bins. Within the first square
the source is the quotient and the destination the remainder. -/
def binOrdinal (z : ℕ) : Bins z ≃ Fin ((z+1)^2+(z+1)) :=
  (Equiv.sumCongr (finProdFinEquiv.trans (finCongr (pow_two (z+1)).symm))
    (Equiv.refl _)).trans finSumFinEquiv

/-- A directed pair occupies its row-major position in the first square. -/
theorem binOrdinal_cable {z : ℕ} (u v : Fin (z+1)) :
    (binOrdinal z (.inl (u,v))).val = u.val*(z+1)+v.val := by
  change v.val+(z+1)*u.val = _
  ac_rfl

/-- A delivery bin follows all ordered pairs. -/
theorem binOrdinal_data {z : ℕ} (u : Fin (z+1)) :
    (binOrdinal z (.inr u)).val = (z+1)^2+u.val := rfl

/-- A cable position passes the square guard and division/remainder recover both labels. -/
theorem binOrdinal_cable_decode {z : ℕ} (u v : Fin (z+1)) :
    let i := (binOrdinal z (.inl (u,v))).val
    i < (z+1)^2 ∧ i/(z+1) = u.val ∧ i%(z+1) = v.val := by
  dsimp only
  rw [binOrdinal_cable]
  have bound := (finProdFinEquiv (u,v)).isLt
  change v.val+(z+1)*u.val < (z+1)*(z+1) at bound
  rw [pow_two,Nat.mul_comm u.val (z+1)]
  refine ⟨by omega,?_,?_⟩
  · simp only [Nat.mul_add_div (Nat.zero_lt_succ z),Nat.div_eq_of_lt v.isLt,Nat.add_zero]
  · simp only [Nat.mul_add_mod_self_left,Nat.mod_eq_of_lt v.isLt]

/-- The second region fails the cable guard, and subtraction recovers the label. -/
theorem binOrdinal_data_decode {z : ℕ} (u : Fin (z+1)) :
    let i := (binOrdinal z (.inr u)).val
    (z+1)^2 ≤ i ∧ i-(z+1)^2 = u.val := by
  dsimp only; rw [binOrdinal_data]; omega

/-- The complete native trial pass computes the finite incident-row objective
from its componentwise cache and incident contributions. -/
theorem pass_score_eq {C I : Type*} [DecidableEq C] [Fintype I] {z : ℕ}
    (rows : I → Traffic C) (s : Finset C) (x : C → Fin (z+1)) (c : C) (v : Fin (z+1))
    (b : PassBins) (m : ℕ → ℕ)
    (means : ∀ j, m (b.addr (binOrdinal z j).val) = cache rows s x j)
    (incident : ∀ j, b.after (binOrdinal z j).val =
      incidentSum rows c (insert c s) (Function.update x c v) j) :
    b.score m ((z+1)^2+(z+1)) = scoreNat rows s x c v := by
  unfold PassBins.score scoreNat candidate
  rw [← Fin.sum_univ_eq_sum_range (fun i => m (b.addr i)*b.after i)]
  rw [← (binOrdinal z).sum_comp (fun i => m (b.addr i.val)*b.after i.val)]
  exact sum_congr rfl (fun j _ => congrArg₂ Nat.mul (means j) (incident j))

end RoutingISA.LabelTrial

end BorderVNP
end Computability
end OAI
