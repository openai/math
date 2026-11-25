import OAI.Hierarchy.ProbeStripMenu
import OAI.Hierarchy.ProtocolRAMCommonCopies
import OAI.Hierarchy.ProtocolRAMLocalCharge
import OAI.Hierarchy.ProtocolRAMPrices

namespace OAI
/-! # Funding each occurrence at a genuine stock-priced option before histogram validation -/

namespace Hierarchy.ProtocolRAM
open LinearAlgebra.SpectralBooks.ChordGraph AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

/-- Install the complete common-size batch at any stock-priced option. The demand
need counts every repeated occurrence. A missing occurrence consumes exactly zero. -/
theorem ordinary_packet_funded {E A J : Type*} [Fintype A] [Fintype J] (req : A→E)
    (width : J→ℕ) (j : J) (e : E) (phase : PhasePrice) (lane bits K multiplicity : ℕ) {γ : ℝ}
    (ha : 0<phase.a) (hs : 0<phase.time) (bonus : 0≤phase.bonus lane) (M : 0≤phase.M)
    (hw : 0<phase.bits) (Kpos : 0<K) (wp : 0<width j) (large : 2*(K*commonWidth width)≤phase.bits)
    (pos : 0≤γ) (adequate : ∀a,req a=e → γ≤phase.quote lane bits)
    (arity : Fintype.card A≤ multiplicity) (rate : (multiplicity:ℝ)/K≤phase.time*phase.a*γ) :
    debited req ((phase.bits/(K*commonWidth width))*width j) e≤bits := by
  classical
  by_cases active : ∃a,req a=e
  · obtain ⟨a,ah⟩ := active
    have large' := (Nat.mul_le_mul_left 2 (Nat.mul_le_mul_left K (width_le_common width j))).trans large
    have funded := adequate_stock (bits:=bits) (w:=phase.bits) (b:=width j) (quote:=phase.quote lane bits)
      (A:=phase.cap lane) ha bonus M hs hw Kpos wp large' (by simpa [PhasePrice.quote] using div_nonneg pos (by norm_num : (0:ℝ)≤2))
      (adequate a ah) rate
    let copies := phase.bits/(K*commonWidth width)
    have copiesSmall := (common_copies_sandwich width j K phase.bits wp Kpos).2
    calc
      _ ≤ ∑ _ : A,copies*width j := by
        apply Finset.sum_le_sum
        intro v _
        change (if req v=e then copies*width j else 0) ≤ copies*width j
        split
        · exact le_rfl
        · exact Nat.zero_le _
      _ = Fintype.card A*(copies*width j) := by simp
      _ ≤ multiplicity*(width j*copied K (width j) phase.bits) := by
        apply Nat.mul_le_mul arity
        exact (Nat.mul_comm copies (width j)).le.trans (Nat.mul_le_mul_left (width j) copiesSmall)
      _ ≤ bits := funded
  · suffices debited req ((phase.bits/(K*commonWidth width))*width j) e=0 by omega
    simp [debited,not_exists.mp active]

variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A] {s : ℕ} [Nonempty (Fin s)]
  {edge : E→Chord s} {req : A→E} {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ}

/-- The issue test succeeds before admitting any private histogram at an ordinary
role of the actual selected rounded-price packet. Its width may vary across the
catalogue and the histogram has no bearing on its demand multiplicities. -/
theorem failed_menu_funded (menu : Probe.FixedMenu F edge req box ε tree N) (rounded : E→ℝ)
    (legal : rounded∈box) (failed : ε≤Probe.discrepancy F edge req rounded) (e : E)
    {J : Type*} [Fintype J] (width : J→ℕ) (code : menu.index→J) (layout : ∀j,width (code j)=(menu.packet j).width)
    (phase : PhasePrice) (lane bits K multiplicity : ℕ) {γ : ℝ} (ha : 0<phase.a) (hs : 0<phase.time)
    (bonus : 0≤phase.bonus lane) (M : 0≤phase.M) (hw : 0<phase.bits) (Kpos : 0<K)
    (large : 2*(K*commonWidth width)≤phase.bits) (pos : 0≤γ) (small : γ≤ menu.margin)
    (roundsDown : rounded e≤phase.quote lane bits) (arity : Fintype.card A≤ multiplicity)
    (rate : (multiplicity:ℝ)/K≤phase.time*phase.a*γ) :
    let j := menu.select ⟨rounded,legal,failed⟩
    debited (fun a : Probe.PositiveDemand req j.val.val=>req a.val)
      ((phase.bits/(K*commonWidth width))*(menu.packet j).width) e≤bits := by
  intro j
  rw [←layout j]
  apply ordinary_packet_funded _ width (code j) e phase lane bits K multiplicity ha hs bonus M hw Kpos
    (by rw [layout]; exact Nat.zero_lt_of_lt (menu.wide j)) large pos _ _ rate
  · intro a eq
    exact small.trans ((menu.adequate ⟨rounded,legal,failed⟩ a).trans ((congrArg rounded eq).le.trans roundsDown))
  · exact (Fintype.card_subtype_le _).trans arity

end
end Hierarchy.ProtocolRAM

end OAI
