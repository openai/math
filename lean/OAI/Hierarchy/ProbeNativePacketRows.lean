import OAI.Hierarchy.ProbeNativePacketAmounts
import OAI.Hierarchy.ProbeNativeActivePorts
import OAI.Hierarchy.ProbeStripMenu
import OAI.Hierarchy.ProbePacketRate

namespace OAI
/-! # Both rate and strict quote on the real histogram bytes of a committed packet row -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram AdaptiveProbe
open ThreeFlat.Diagonal.MotifOuterTerms
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped BigOperators Classical Fin.CommRing
noncomputable section

variable {F E A : Type*} [Field F] [Fintype E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]
variable {edge : E→Chord k} {req : A→E} {w d rows : ℕ} {s : StockCommit} {mem : Memory w}

namespace NativePacketRow
variable {P : Probe.Packet F edge req} {extra : ℕ} {b : Batch (P.terms+extra) d}
  {layout : PortPlan s b mem rows} {j : Fin rows}

omit [Nonempty (Fin k)] in
theorem rate (R : NativePacketRow P extra b layout j) (K payload : ℕ) (positive : 0<P.width)
    (copies : b.copies≤copied K P.width payload) (v : Fin d) :
    K*(installedBits s.columns mem (layout.enum ⟨j,v⟩)+consumedBits s.columns mem (layout.enum ⟨j,v⟩)) ≤ payload*packetRate P := by
  by_cases hit : ∃e,R.ports e=v
  · obtain ⟨e,rfl⟩ := hit
    rw [(R.amounts e).1,(R.amounts e).2]
    exact packet_rate P K payload b.copies positive copies R.h e
  · obtain ⟨a,b⟩ := R.unused v fun e eq=>hit ⟨e,eq⟩
    simp [a,b]

end NativePacketRow

/-- The actual finite code table at a failed rounded price chooses the same packet
used by the physical histogram. Its paid contraction certifies the native strict
quote, and its nonzero required prices remain funded after downward rounding. -/
theorem selected_menu_quote {Y : Type*} [Nonempty E] {box : Set (E→ℝ)} {ε tree : ℝ} {N : ℕ}
    (menu : Probe.FixedMenu F edge req box ε tree N) (price : Y→E→ℝ) (legal : ∀v,price v∈box)
    (v : Y) (failed : ε≤Probe.discrepancy F edge req (price v)) :
    let index := menu.select ⟨price v,legal v,failed⟩
    let packet := menu.packet index
    ∀ (extra : ℕ) (b : Batch (packet.terms+extra) d) (layout : PortPlan s b mem rows)
      (j : Fin rows) (R : NativePacketRow packet extra b layout j) (cash : Fin d→ℝ) (br err γ : ℝ),
    0≤err → γ≤ menu.margin → (∀e,price v e≤cash (R.ports e) ∧ cash (R.ports e)≤price v e+err) →
    br=b.copies*(tree*packet.selectorBits) → (Fintype.card E:ℝ)*b.maxWidth*err≤packet.width*γ/2 →
    (∀ a : Probe.PositiveDemand req index.val.val,γ≤cash (R.ports (req a.val))) ∧
    (∑ i,(installedBits s.columns mem (layout.enum ⟨j,i⟩):ℝ)*cash i)+br+b.copies*(packet.width*γ/2)≤
      ∑ i,(consumedBits s.columns mem (layout.enum ⟨j,i⟩):ℝ)*cash i := by
  intro index packet extra b layout j R cash br err γ errpos small accurate treeVal resolution
  have selected := menu.word_spec price legal v failed
  refine ⟨fun a=>small.trans ((selected.2.1 a).trans (accurate _).1),?_⟩
  apply layout.local_quote packet extra j R.live R.h R.ports R.fields R.entries R.need R.unused R.bound R.fit R.wide
    cash (price v) br tree err γ errpos accurate treeVal _ resolution
  have record := selected.2.2 b.copies R.h
  exact record.trans (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (sub_le_sub_left small _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _))

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
