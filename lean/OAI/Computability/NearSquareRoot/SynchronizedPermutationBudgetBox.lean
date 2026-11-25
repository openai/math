import OAI.Computability.NearSquareRoot.SynchronizedPermutationBudget

/-! # Eventual batch layouts for the coprime Fourier box -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedPermutationBudget

open Filter Controlled

/-- A subset of the batch may finish its network early. Removing these switches
can only decrease the control and guard space required. -/
theorem selected_fits {d k low high : ℕ} (w : Fin d → ℕ) (hw : ∀ i, w i ≤ width k)
    (room : 8*width k ≤ k) (res : low+high ≤ k/4) (a : ℕ) (selected : Finset (Fin d))
    (sub : selected ⊆ members k a) :
    let b := selected.card
    high + (∑ i ∈ selected, (w i-1)) + (b+1)*guardWidth k + (b+1)*guardWidth k + low ≤ k := by
  have sum : (∑ i ∈ selected, (w i-1)) ≤ controlBits w k a :=
    Finset.sum_le_sum_of_subset sub
  have size := Nat.mul_le_mul_right (guardWidth k) (Nat.succ_le_succ (Finset.card_le_card sub))
  simp only [Nat.succ_eq_add_one] at size
  have fit := batch_fits w hw room res a
  dsimp only at fit ⊢
  omega

/-- The unassigned positions form one middle gap. The leading reserve can be
used as a fixed prefix and the trailing reserve as a packed payload. -/
theorem selected_layout {d k low high : ℕ} (w : Fin d → ℕ) (hw : ∀ i, w i ≤ width k)
    (room : 8*width k ≤ k) (res : low+high ≤ k/4) (a : ℕ) (selected : Finset (Fin d))
    (sub : selected ⊆ members k a) :
    let p := ∑ i ∈ selected, (w i-1)
    let h := (selected.card+1)*guardWidth k
    let gap := k - (high+p+h+h+low)
    high + (p+h+gap+h) + low = k := by
  have fit := selected_fits w hw room res a selected sub
  dsimp only at fit ⊢
  omega

/-- Concrete quantitative premises shared by every permutation opcode and its
inverse at this transform size. -/
structure BoxPasses (k lowDegree highDegree : ℕ) : Prop where
  valid : BoxShape.Valid k (BoxScale.width k) (CoprimeBox.box k)
  fits : 8*width k ≤ k
  reserves : payloadBits lowDegree k + payloadBits highDegree k ≤ k/4

theorem eventually_box_passes (lowDegree highDegree : ℕ) :
    ∀ᶠ k : ℕ in atTop, BoxPasses k lowDegree highDegree := by
  obtain ⟨K,hK⟩ := CoprimeBox.eventually_valid
  filter_upwards [eventually_ge_atTop K, eventually_room lowDegree highDegree] with k hk hr
  exact ⟨hK k hk,hr.1,hr.2⟩

namespace BoxPasses
variable {k lo hi : ℕ} (budget : BoxPasses k lo hi)
include budget

theorem width_bound (j : Fin ((CoprimeBox.box k).length / 4)) :
    BoxFin.physicalWidth (box := CoprimeBox.box k) j ≤ width k :=
  (BoxFin.physicalWidth_log budget.valid j).trans (Nat.mul_le_mul_left 140
    ((Nat.clog_monotone 2 (Nat.le_succ k)).trans (Nat.le_add_left ..)))

theorem slot_count :
    (passes ((CoprimeBox.box k).length / 4) k).length ≤ (32*140^2)*(1+Nat.clog 2 (k+1))^2 :=
  pass_count (BoxFin.blockCount_le budget.valid) budget.fits

theorem layout (a : ℕ) (selected : Finset (Fin ((CoprimeBox.box k).length / 4)))
    (sub : selected ⊆ members k a) :
    let p := ∑ i ∈ selected, (BoxFin.physicalWidth (box := CoprimeBox.box k) i - 1)
    let h := (selected.card+1)*guardWidth k
    let low := payloadBits lo k
    let high := payloadBits hi k
    let gap := k - (high+p+h+h+low)
    high + (p+h+gap+h) + low = k :=
  selected_layout _ budget.width_bound budget.fits budget.reserves a selected sub

end BoxPasses
end SynchronizedPermutationBudget

end NearSquareRoot
end Computability
end OAI
