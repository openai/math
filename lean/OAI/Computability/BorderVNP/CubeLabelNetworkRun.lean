import OAI.Computability.BorderVNP.CubeLabelNative
import OAI.Computability.BorderVNP.CubeMeanPhysicalTables

/-! # Lemma 8.2 on the actual public memory of a packed network

The deterministic program reads the compressed cable and delivery arrays and writes a label
word for each cell. Decoding those words gives the two capacity bounds needed for packet routing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical

open VPVNP.BurstRAM RoutingISA Crossing MeanChoice LabelIndex Finset

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type} [Fintype Cell] [DecidableEq Cell]
variable (N : Network D P bits) (cell : N.Site → Cell)
variable {A : Type*} [Fintype A] (recv : A → Cell) (dataWidth : A → ℕ)

/-- Decode the product label stored at a cell's real output address. -/
def memoryLabel {w k : ℕ} (mt : Memory w) (lab : ℕ) (cells : Cell ≃ Fin k)
    (a d : ℕ) (hd : 0 < d) (c : Cell) : Label (a+1) d :=
  decodeProduct a d hd (Fin.ofNat (d^(a+1)-1+1) (mt (lab+(cells c).val)).val)

/-- Correctness of the complete fixed program on the actual network. Both traffic bounds
apply to the product labels decoded from its output words, and those words are precisely the
chosen numeric labels. -/
theorem native_packed_labels {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (a d : ℕ) (hd : 0 < d) (reg : Bank w) (mem : Memory w) {W : ℝ} {M : ℕ}
    (budget : PackedLabelBudget N cell recv dataWidth W M (d^(a+1))) :
    let m := readings mem
    let base := (pub 0).val
    let l := layout base m
    let lab := m (base+48)
    ∀ (ep : Endpoints l m) (cells : Cell ≃ Fin l.cells)
      (edgeOrd : N.CrossingEdge cell ↪ Fin l.cableCount) (dataOrd : A ↪ Fin l.deliveryCount),
      RowPlacement (networkRows N cell recv dataWidth) (fromTables l m ep) cells (edgeOrd.sumMap dataOrd) →
      Allocated l → l.labels = d^(a+1) → lab+l.cells ≤ l.heads → base+56 < l.heads →
      l.dataMean+l.labels ≤ 2^w → wordEnvelope l.labels (inputWidth l m) < 2^w →
      ∃ tr out mt, Runs pub macros directoryProgram reg mem tr out mt ∧
        traceCost tr ≤ directoryTicks l (d^(a+1)-1) m ∧
        (∀ c, (mt (lab+(cells c).val)).val = (meanPackedCodes N cell recv dataWidth
          ((List.finRange l.cells).map cells.symm) (d^(a+1)-1) c).val) ∧
        (∀ u v, Balancing.load (Balancing.cable (fun b : LiveBit N cell => crossSrc N cell b.1)
          (fun b : LiveBit N cell => crossDst N cell b.1) u v) (memoryLabel mt lab cells a d hd) ≤ 4*W/(d^(a+1) : ℕ)^2) ∧
        (∀ u, Balancing.load (Balancing.datum (fun b : Balancing.Bits dataWidth => recv b.1) u)
          (memoryLabel mt lab cells a d hd) ≤ 4*W/(d^(a+1) : ℕ)) ∧ ∀ addr < lab, mt addr = mem addr := by
  intro m base l lab ep cells edgeOrd dataOrd place al hz sep frame addresses cap
  let z := d^(a+1)-1
  have positive := pow_pos hd (a+1)
  have alphabet : l.labels = z+1 := by dsimp [z]; omega
  obtain ⟨tr,out,mt,run,cost,_,labels,off⟩ := native_table_codes pub macros z reg mem ep al alphabet sep frame addresses cap
  change ∀ c : Fin l.cells, (mt (lab+c.val)).val = (tableCodes l m ep z c).val at labels
  have numbers : tableCodes l m ep z = meanPackedCodes N cell recv dataWidth ((List.finRange l.cells).map cells.symm) z ∘ cells.symm := tableCodes_eq_meanPackedCodes N cell recv dataWidth l m ep cells place z
  have trueLabel : memoryLabel mt lab cells a d hd = fun c => decodeProduct a d hd (tableCodes l m ep z (cells c)) := by
    funext c
    unfold memoryLabel
    apply congrArg (decodeProduct a d hd)
    apply Fin.ext
    change (mt (lab+(cells c).val)).val%(z+1) = (tableCodes l m ep z (cells c)).val
    rw [labels (cells c),Nat.mod_eq_of_lt (tableCodes l m ep z (cells c)).isLt]
  obtain ⟨cable,data⟩ := tableCodes_balanced N cell recv dataWidth l m ep cells place a d hd budget
  refine ⟨tr,out,mt,run,cost,?_,trueLabel ▸ cable,trueLabel ▸ data,off⟩
  intro c
  simpa only [numbers,Function.comp_apply,Equiv.symm_apply_apply] using labels (cells c)

/-- The native initialization, trial, and commit clock is strictly below the bound in Lemma
8.2 at the sparse cell and descriptor scales. The threshold is independent of the public
array contents, the team size, and every allocation within the displayed caps. -/
theorem eventually_native_label_ticks {α : ℝ} (hα : 0 < α) (a : ℕ) (small : α*a < 1/10^6)
    (B C : ℕ) : ∀ᶠ n : ℕ in Filter.atTop, ∀ (r degree z : ℕ) (l : Layout) (m : ℕ → ℕ), 1 ≤ r →
      (l.cells : ℝ) ≤ C*r*(n : ℝ)^(9/10 : ℝ) → (degree : ℝ) ≤ (n : ℝ)^(1/100 : ℝ) →
      1+l.cells+l.cableCount+l.deliveryCount ≤ B*(l.cells+1)*(degree+1) →
      l.labels = labelCount α a n → l.labels = z+1 → (directoryTicks l z m : ℝ) < r*(n : ℝ)^(95/100 : ℝ) := by
  filter_upwards [eventually_scanEnvelope hα a small (600*B) C] with n bound
  intro r degree z l m hr cells sparse counts hlabel hz
  have ticks := directoryTicks_le_envelope l m z B degree hz counts
  rw [hlabel] at ticks
  exact (Nat.cast_le.mpr ticks).trans_lt (bound r l.cells degree hr cells sparse)

end Cube.Physical

end BorderVNP
end Computability
end OAI
