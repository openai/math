import OAI.Hierarchy.ProtocolRAMPaidWidthCore

namespace OAI
/-! # Native bounds for paired paid-width slices -/

namespace Hierarchy.ProtocolRAM.PaidWidths
open RepairHistogram

/-- Both columns that identify each occurrence, and the two expressions
that read it, suffice to certify the native paired scatter. -/
theorem Slice.fits_of_fields (s : Slice) (bank : Bank) {W edges src : ℕ}
    (edge : s.edge.Fits W bank.base) (amount : s.amount.Fits W bank.base)
    (owner : s.owner.Fits W bank.base) (parity : s.parity.Fits W bank.base)
    (bound : bank.base + edges < src) (room : src + 2*s.count < 2^W) :
    s.Fits bank edges src W := by
  have cap : bank.base ≤ src := by omega
  have bank_le (b : Bank) (ok : b.Fits W bank.base) : b.Fits W src :=
    ⟨ok.1, ok.2.1, ok.2.2.trans cap⟩
  have index : (Expr.lookup s.owner .row).Fits W src := ⟨bank_le _ owner, trivial⟩
  have at_index (x : Expr) (hx : x.Fits W src) :
      (x.atRow (.lookup s.owner .row)).Fits W src := by
    induction x <;> simp_all only [Expr.atRow, Expr.Fits] <;> tauto
  have edge' := ProtocolRAMGeneratedWrite.fits_mono s.edge cap edge
  have dest : (destination bank.base edges s.edge).Fits W src :=
    ⟨trivial, edge', trivial, edge', trivial⟩
  refine ⟨bound, room, ?_, edge, amount, owner.2.2, parity.2.2⟩
  exact ⟨⟨bank_le _ parity, trivial⟩, trivial, at_index _ dest,
    at_index _ (ProtocolRAMGeneratedWrite.fits_mono s.amount cap amount), trivial⟩

/-- The same source program applies to every occurrence of every event,
including repeated slices in the flattened list. -/
theorem fits_flatMap {E : Type*} (events : List E) (slices : E → List Slice)
    (bank : Bank) {W edges src : ℕ} (bound : bank.base + edges < src)
    (fields : ∀ a ∈ events, ∀ s ∈ slices a,
      s.edge.Fits W bank.base ∧ s.amount.Fits W bank.base ∧
      s.owner.Fits W bank.base ∧ s.parity.Fits W bank.base ∧ src+2*s.count<2^W) :
    ∀ s ∈ events.flatMap slices, s.Fits bank edges src W := by
  intro s hs
  obtain ⟨a, ha, hs⟩ := List.mem_flatMap.mp hs
  obtain ⟨edge, amount, owner, parity, room⟩ := fields a ha s hs
  exact s.fits_of_fields bank edge amount owner parity bound room

end Hierarchy.ProtocolRAM.PaidWidths

end OAI
