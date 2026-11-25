import OAI.Computability.BorderVNP.PackedCompleteRoutes
import OAI.Computability.BorderVNP.ShortenEnrichedNamedProgram

/-! # Complete physical charge masks in a measured stable-order stage -/

namespace OAI
namespace Computability
namespace BorderVNP

open Cover Crossing Epoch Epoch.Round Shortening Packing Shortening.PreparedBins
open Shortening.Framed PackedHistoryCircuit.Normalized Shortening.Adaptive
open scoped Classical BorderVNP.Epoch.Cube

variable {D m k d old : ℕ} [NeZero D] {P : Type} {bits : P → ℕ} {K : Type*} [Field K]
    {e : PaidIdentity K D m} {S : Finset (HyperbolicHost (Cube D))} {h H ν : ℝ}

omit [NeZero D] [Field K] in
/-- Sorting occupied cable names preserves the charge and both physical endpoint sites. -/
theorem Shortening.PlacedPack.CoversCrossings.dense {I : Type} [Fintype I] {rows : ℕ}
    {p : PlacedPack D P bits K I d} (complete : p.CoversCrossings) (slot : p.pack.layout.Edge ↪ Fin rows) :
    (p.dense slot).CoversCrossings := by
  intro c
  obtain ⟨a,rfl⟩ := (Names.denseSlot p.pack.layout slot).surjective c
  rw [(p.dense_endpoints slot a).1,(p.dense_endpoints slot a).2,(p.dense_marks slot a).1]
  exact complete a

/-- Hooks and inserted cables are charged. Each retained band uses the bin of its own
original sorted cable, whose moved endpoints coincide whenever that bin is absent. -/
theorem PackedHistoryCircuit.Normalized.Stage.coversCrossings_result {I B : Type} [Fintype I] [Fintype B]
    {child : Fin k → PlacedPack D P bits K I old} (s : Stage m B d child)
    (labeled : ∀ c, s.placed.old (s.input.layout.src c) ≠ s.placed.old (s.input.layout.dst c) → (s.label c).isSome)
    (q : s.Index e) : (s.result e q).CoversCrossings := by
  intro c hn
  rcases c with c | (c | c)
  · rfl
  · exact labeled c.val.1 hn
  · rfl

/-- The physical receipt covers each crossing in the installed sorted input. If two old
endpoints coincide, applying their child's single sampled motion keeps them together. -/
theorem PackedHistoryCircuit.Normalized.SourceTemplate.receiptAt_coversCrossings (src : SourceTemplate e h H ν S)
    {he : old = d+2*src.word} {child : Fin k → PlacedPack D P bits K (Cube D) old} {hk : 0 < k}
    {sel : src.SelectionAt he child hk} {dir : CableSlots (raw child)} {s : Stage m src.bins.Bin d child}
    (receipt : src.ReceiptAt he child hk sel dir s) (complete : ∀ i, (child i).CoversCrossings)
    (q : s.Index e) : (s.result e q).CoversCrossings := by
  subst old
  obtain ⟨r⟩ := receipt
  apply s.coversCrossings_result
  intro c
  obtain ⟨z,rfl⟩ := (Names.denseSlot (raw child).layout s.slot).surjective c
  have hs : s.input.layout.src (Names.denseSlot (raw child).layout s.slot z) = (raw child).layout.src z :=
    Names.src_slot _ _ _ z
  have hd : s.input.layout.dst (Names.denseSlot (raw child).layout s.slot z) = (raw child).layout.dst z :=
    Names.dst_slot _ _ _ z
  rw [hs,hd]
  have label : s.label (Names.denseSlot (raw child).layout s.slot z) = s.bin z :=
    congrArg s.bin ((Names.denseSlot (raw child).layout s.slot).symm_apply_apply z)
  rw [label]
  obtain ⟨i,a⟩ := z
  let pick : src.Selection child hk := sel
  have moved : s.placed.old = movedOld (fun i => (child i).pack) pick.sample (childSites child) := by
    rw [r.trace.realizes]
    exact r.trace.moved
  have bin : s.bin = src.bins.publicBin child pick.labels pick.sample := by rw [r.trace.realizes]; rfl
  rw [moved,bin]
  intro ne
  have distinct : (child i).site ((child i).pack.layout.src a) ≠ (child i).site ((child i).pack.layout.dst a) := by
    intro eq
    exact ne (congrArg (fun z => sampleMove (pick.sample i) (levelCast (Nat.add_right_comm d (2*src.word) 1) z)) eq)
  have ha := ((child i).active_iff a).mpr ⟨complete i a distinct,distinct⟩
  change (if ht : (child i).active a then some _ else none).isSome = true
  rw [dite_eq_left ha]
  rfl

end BorderVNP
end Computability
end OAI
