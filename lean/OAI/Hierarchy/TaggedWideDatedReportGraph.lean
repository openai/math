import OAI.Hierarchy.TaggedWideDatedGraph
import OAI.Hierarchy.TaggedWireTerminalPorts
import OAI.Hierarchy.TaggedWirePhysicalTerm

namespace OAI
/-! # Every occupied prefix row inherits its genuine final socket chord -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.Report
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe Tagged WireTelescope HistoryRoles ProtocolRAM.Calendar
open scoped Classical BigOperators

theorem prefix_named_widths {h W k attempts w R M den n : ℕ} {p : Equiv.Perm (Row h)}
    {U : Widths (siteLast h (2^W) k+1)} (Z : Report p (2^W) k w R M den U) (depth : ℕ)
    (mark : ReportSockets.Marks h W k attempts)
    (order : Fin n ≃ HistoryRoles.Source Z.sampler p.symm depth mark)
    (ord : Catalogue Z.sampler p.symm depth mark ↪ Fin Z.edges)
    (id : {i : Fin Z.edges // 0 < (Z.rows i).width} ↪ Catalogue Z.sampler p.symm depth mark)
    (rooted : ∀ i, ord (id i) = i.val)
    (joins : ∀ i : {i : Fin Z.edges // 0 < (Z.rows i).width},
      let ends := actualEnds Z.sampler p.symm depth mark (id i)
      ((Z.rows i.val).endpoint = (siteNumber h (2^W) k ends.1).val ∧
       (Z.rows i.val).opposite = (siteNumber h (2^W) k ends.2).val) ∨
      ((Z.rows i.val).endpoint = (siteNumber h (2^W) k ends.2).val ∧
       (Z.rows i.val).opposite = (siteNumber h (2^W) k ends.1).val))
    (fixed : Fin Z.edges → ℕ) (stock : Goods h W k → ℕ) (reserve : Catalysts h W k → ℕ)
    (prior : ∀ i, fixed i ≤ Z.fixed i) :
    installedWidths (HistoryRoles.sorted Z.sampler p.symm depth mark ∘ order)
      (Sum.elim (fixed ∘ ord) (Sum.elim stock reserve) ∘ order) =
      Z.mount.actual.chordWidths fixed +
      (commodityGraph p.symm (siteNumber h (2^W) k)).chordWidths stock +
      (catalystGraph (siteNumber h (2^W) k)).chordWidths reserve := by
  classical
  have reported (i : Fin Z.edges) : Z.fixed i ≤ (Z.rows i).width := by
    rw [Z.receipt.report i]
    exact (Nat.le_add_right _ _).trans (Nat.le_add_right _ _)
  have active (i : {i : Fin Z.edges // 0 < Z.fixed i}) : 0 < (Z.rows i.val).width :=
    i.property.trans_le (reported i.val)
  let sub : {i : Fin Z.edges // 0 < Z.fixed i} ↪ Catalogue Z.sampler p.symm depth mark :=
    ⟨fun i => id ⟨i.val, active i⟩, fun i j eqn => by
      have project := congrArg (fun q : {e : Fin Z.edges // 0 < (Z.rows e).width} => q.val)
        (id.injective eqn)
      exact Subtype.ext project⟩
  have positions := Terminal.positions_of_reported Z.sampler p.symm depth mark Z.mount (publicChord h (2^W) k)
    Z.fixed Z.stock Z.reserved Z.used sub Z.receipt (fun i => joins ⟨i.val, active i⟩)
  apply DatedRows.named_widths Z.sampler p.symm depth mark order ord Z.mount.actual fixed stock reserve
    (publicChord h (2^W) k)
  · intro i absent
    by_contra nz
    have pos : 0 < Z.fixed i := (Nat.pos_of_ne_zero nz).trans_le (prior i)
    exact absent ⟨_, rooted ⟨i, active ⟨i, pos⟩⟩⟩
  · intro i loop
    exact Nat.eq_zero_of_le_zero ((prior i).trans ((reported i).trans_eq (Z.receipt.dropped i loop)))
  · intro e pos
    let i : {i : Fin Z.edges // 0 < Z.fixed i} := ⟨ord e, pos.trans_le (prior _)⟩
    have same : sub i = e := ord.injective (rooted ⟨i.val, active i⟩)
    exact (positions i).trans (congrArg (fun c => HistoryRoles.sorted Z.sampler p.symm depth mark (.inl c)) same)

end Hierarchy.ProbeStage.CoreBoard.Report

end
end OAI
