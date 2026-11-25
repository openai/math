import OAI.Hierarchy.DescentSIMDLookup

namespace OAI
/-! # The native lookup of an attained endpoint among four sorted peer words -/
namespace Hierarchy.DescentResetJoinedRank
open DescentSIMDLookup
open scoped Classical Fin.CommRing
noncomputable section
variable {b : ℕ}

/-- The four preceding cells are positive packed site codes or the absent code zero.
An absent target or an empty candidate receives ordinal zero. -/
def rank (x : Fin 5→Cell b) : Cell b :=
  let hits:=Finset.univ.filter fun i:Fin 4=>x 4≠0 ∧ x i.castSucc=x 4
  if yes : hits.Nonempty then ⟨(hits.min' yes).val%2^b,Nat.mod_lt _ (Nat.two_pow_pos _)⟩ else 0

theorem rank_at (x : Fin 5→Cell b) (j : Fin 4) (size : 4≤2^b)
    (positive : x 4≠0) (hit : ∀i : Fin 4,x i.castSucc=x 4 ↔ i=j) : (rank x).val=j.val := by
  let hits:=Finset.univ.filter fun i:Fin 4=>x 4≠0 ∧ x i.castSucc=x 4
  have yes : hits.Nonempty:=⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,positive,(hit j).2 rfl⟩⟩
  change (if h:hits.Nonempty then (⟨(hits.min' h).val%2^b,Nat.mod_lt _ (Nat.two_pow_pos _)⟩:Cell b) else 0).val=_
  rw [dite_eq_left yes]
  change (hits.min' yes).val%2^b=_
  rw [Nat.mod_eq_of_lt ((hits.min' yes).isLt.trans_le size)]
  exact congrArg Fin.val ((hit _).1 (Finset.mem_filter.mp (hits.min'_mem yes)).2.2)

/-- A shape and a positive relative old-host rank fit together in the one
packed field even when the old host has more than three neighbors. -/
theorem jointFits {degree shelf shape old bits : ℕ} (low : old≤degree)
    (high : shape<shelf) (bitsFit : Nat.clog 2 (degree+2)+Nat.clog 2 (shelf+1)≤bits) :
    shape*2^Nat.clog 2 (degree+2)+(old+1)<2^bits := by
  let r:=2^Nat.clog 2 (degree+2)
  have lo : old+1<r:=(by omega : old+1<degree+2) |>.trans_le (Nat.le_pow_clog (by decide) _)
  have hi : shelf≤2^Nat.clog 2 (shelf+1):= (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
  calc
    _ < shape*r+r:=Nat.add_lt_add_left lo _
    _ = (shape+1)*r:=by rw [Nat.succ_mul]
    _ ≤ shelf*r:=Nat.mul_le_mul_right _ high
    _ ≤ 2^Nat.clog 2 (shelf+1)*r:=Nat.mul_le_mul_right _ hi
    _ = 2^(Nat.clog 2 (degree+2)+Nat.clog 2 (shelf+1)):=by rw [pow_add,Nat.mul_comm]
    _ ≤ _:=Nat.pow_le_pow_right (by decide) bitsFit

end
end Hierarchy.DescentResetJoinedRank

end OAI
