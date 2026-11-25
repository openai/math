import OAI.Hierarchy.DescentIssuedEmittedReset

namespace OAI
/-! # Word widths for all occupied and vacant rows of the reset estimator -/
noncomputable section
namespace Hierarchy.DescentMeasuredWeights
open DescentGL DescentColonies DescentBaseVariance DescentIntegerScale
open scoped Classical BigOperators
variable {V : Type} [Fintype V] [DecidableEq V] {near : V→Finset V} {k N : ℕ}
def rateCap (k K : ℕ) := max (4*2^((k+7)/8)) (K^2)

omit [DecidableEq V] in
theorem padded_bounds (b : V→ℕ) (loc : Item (inputLevels (k:=k) b) (Contacts near)↪Fin N)
    (f B K w gainBits payloadBits : ℕ)
    (x : V→Bits k→ℕ) (y : Contacts near→Bits k→ℕ)
    (depths : ∀v,b v≤k) (depthRoom : k<2^w)
    (gainRoom : 2^f*B*rateCap k K<2^gainBits)
    (site : ∀v z,x v z<2^payloadBits) (contact : ∀c z,y c z<2^payloadBits) (i : Fin N) :
    padded loc (level _ (inputDepth b) (pairDepth near b)) 0 i<2^w ∧
    padded loc (gain _ f B K) 0 i<2^gainBits ∧
    ∀z,padded loc (load _ x y) (fun _=>0) i z<2^payloadBits := by
  by_cases h : ∃u,loc u=i
  · obtain ⟨u,rfl⟩:=h
    simp only [padded_at]
    cases u with
    | inl pair=>
      rcases pair with ⟨v,j⟩
      have hd:=depths v
      have hj : j.val<k-b v+1:=j.isLt
      refine ⟨Nat.lt_of_le_of_lt (by change b v+j.val≤k;omega) depthRoom,?_,site v⟩
      apply Nat.lt_of_le_of_lt _ gainRoom
      apply Nat.mul_le_mul_left
      apply le_trans _ (le_max_left ..)
      apply Nat.mul_le_mul_left
      exact Nat.pow_le_pow_right (by decide) (Nat.div_le_div_right (by change j.val+7≤k+7; omega))
    | inr c=>
      exact ⟨(max_le (depths _) (depths _)).trans_lt depthRoom,
        (Nat.mul_le_mul_left (2^f*B) (le_max_right ..)).trans_lt gainRoom,contact c⟩
  · simp only [padded_else _ _ _ _ h]
    exact ⟨Nat.two_pow_pos _,Nat.two_pow_pos _,fun _=>Nat.two_pow_pos _⟩

omit [DecidableEq V] in
theorem contactCard {Δ : ℕ} (degree : ∀v,(near v).card≤Δ) : Fintype.card (Contacts near)≤Fintype.card V*Δ := by
  change Fintype.card (Σv,↥(near v))≤_
  rw [Fintype.card_sigma]
  simpa using Finset.sum_le_sum (s:=Finset.univ) (fun v _=>degree v)

theorem siteMass (x : DescentGL.Bits k→ℕ) (B : ℕ) (small : ∀z,x z≤B) : ∑z,x z≤2^k*B := by
  have h:=Finset.sum_le_sum (s:=Finset.univ) (fun z _=>small z)
  simpa [DescentGL.Bits] using h

end Hierarchy.DescentMeasuredWeights

end
end OAI
