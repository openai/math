import OAI.Computability.BorderVNP.ShortenCompiledSourceTemplate
import OAI.Computability.BorderVNP.ShortenDensePath

/-!
# Installing the compiled choices of a whole source path

A selected stage records its actual decoded labels and frame-selected
samples. Choosing such data at every child tuple yields one program whose
input cable order, receipt, site record factor and stored histogram rows all
refer to those selections. The equality of scheduled depths is explicit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Cover Cover.Frame Hecke Shortening Shortening.Framed Packing
open scoped Classical BorderVNP.Epoch.Cube

variable {D m b k d old : ℕ} [NeZero D] {K : Type*} [Field K] {P : Type} {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : Finset (HyperbolicHost (Cube D))} {h H ν : ℝ}

namespace SourceTemplate

variable (src : SourceTemplate e h H ν S)

/-- Publicly decoded endpoint labels and the selected sample for every
child, with the deviation certificate supplied by the sample frame. -/
structure Selection (child : Fin k → PlacedPack D P bits K (Cube D) (d+2*src.word)) (hk : 0 < k) where
  /-- The common label bank determined from the actual old endpoints. -/
  labels : PreparedBins.Labels src.bins (fun i => (child i).pack) (fun i => (child i).active)
    (PreparedBins.childSites child)
  /-- Frame-selected word, factor permutation and posttranslation of each child. -/
  sample : Fin k → PackSample (lattice 1) elliptic (Cube D) (d+1) src.word
  /-- The true finite sample law gives this deviation for those exact labels. -/
  bound : src.bins.SampleDeviation child labels sample hk src.motion

/-- The very same public selection at an arithmetically equal scheduled
input level. Eliminating the level equality recovers the literal labels
and samples without any address permutation. -/
def SelectionAt (he : old = d+2*src.word) (child : Fin k → PlacedPack D P bits K (Cube D) old)
    (hk : 0 < k) : Type := by
  subst old
  exact src.Selection child hk

/-- The physical receipt of a prescribed selection and row directory at
the scheduled input level. -/
def ReceiptAt (he : old = d+2*src.word) (child : Fin k → PlacedPack D P bits K (Cube D) old)
    (hk : 0 < k) (sel : src.SelectionAt he child hk) (dir : CableSlots (raw child))
    (s : Stage m src.bins.Bin d child) : Prop := by
  subst old
  let selected : src.Selection child hk := sel
  exact Nonempty (src.bins.DenseReceipt e child selected.labels selected.sample dir.number s hk H ν
    src.mean src.motion src.record)

/-- Existence of public selections on every admissible tuple, by the actual
compiled radius chosen by the source template. -/
theorem exists_selectionAt (he : old = d+2*src.word) (hf : src.floor ≤ d) (hk : 0 < k)
    (child : Fin k → PlacedPack D P bits K (Cube D) old) (prep : ∀ i, Catalog.PlacedAt S h (child i)) :
    Nonempty (src.SelectionAt he child hk) := by
  subst old
  obtain ⟨L⟩ := src.bins.exists_childLabels child (fun i => (prep i).sites) (fun i => (prep i).short)
  obtain ⟨ω,hdev⟩ := src.bins.physical_choice src.compiled (src.floor_pos.trans_le hf) hk child L
    (fun i => (prep i).midpoint)
  exact ⟨⟨L,ω,hdev⟩⟩

/-- Install precisely the selection supplied at the scheduled level and
the incoming directory, preserving its physical quantitative witnesses. -/
theorem installAt (he : old = d+2*src.word) (hf : src.floor ≤ d) (hk : 0 < k)
    (child : Fin k → PlacedPack D P bits K (Cube D) old) (prep : ∀ i, Catalog.PlacedAt S h (child i))
    (sel : src.SelectionAt he child hk) (dir : CableSlots (raw child)) :
    ∃ s : Stage m src.bins.Bin d child,
      s.rowCount = dir.rows ∧ (∀ x, (s.slot x).val = (dir.number x).val) ∧
      Nonempty (Stage.Measurements s hk H ν src.mean src.motion) ∧
      (src.ReceiptAt he child hk sel dir s ∧ s.RecordFactor e src.record) ∧
      ∀ q : s.Index e, Catalog.PlacedAt (src.bins.successorSites src.word e) h (s.result e q) := by
  subst old
  let selected : src.Selection child hk := sel
  obtain ⟨s,⟨R⟩⟩ := src.run_selected d hf hk child prep selected.labels selected.sample dir.number selected.bound
  refine ⟨s,?_,?_,⟨R.measure⟩,⟨⟨R⟩,R.records⟩,R.closure⟩
  · rw [R.trace.realizes]; rfl
  · intro x; rw [R.trace.realizes]; rfl

end SourceTemplate

namespace SourcePath

variable (p : SourcePath b e h H ν) (last high : ℕ)

/-- Arithmetic depth agreement between the schedule and the source motion table. -/
theorem stepDepth (i : Fin b) :
    p.asPath.depth last high i.val = p.asPath.depth last high (i.val+1) + 2*(p.pattern i).word :=
  Adaptive.Levels.step_depth (fun j => (p.pattern j).word) _ _ i

variable (before : ∀ (i : Fin b) (c : Fin k → p.asPath.State P bits k last high i.val),
    CableSlots (raw fun j => (c j).val))
variable (after : ∀ (i : Fin b) (c : Fin k → p.asPath.State P bits k last high i.val)
    (s : Stage m (p.pattern i).bins.Bin (p.asPath.depth last high (i.val+1)) (fun j => (c j).val))
    (q : s.Index e), CableSlots (s.result e q).pack)

set_option maxHeartbeats 1200000 in
/-- Choose the exact normalized program for a prescribed public selection
and both actual row directories. Its saved states and all returned receipts
are indexed by the same physical histogram. -/
theorem program_selected (hk : 0 < k) (hf : ∀ i : Fin b, (p.pattern i).floor ≤ p.asPath.depth last high (i.val+1))
    (sel : ∀ (i : Fin b) (c : Fin k → p.asPath.State P bits k last high i.val),
      (p.pattern i).SelectionAt (p.stepDepth last high i) (fun j => (c j).val) hk) :
    ∃ F : p.asPath.ProgramAt P bits k last high,
      (∀ i c, (F.stage i c).rowCount = (before i c).rows ∧ ∀ x, ((F.stage i c).slot x).val = ((before i c).number x).val) ∧
      (∀ i c, Nonempty (Stage.Measurements (F.stage i c) hk H ν (p.pattern i).mean (p.pattern i).motion)) ∧
      (∀ (i : Fin b) (c : Fin k → p.asPath.State P bits k last high i.val), (p.pattern i).ReceiptAt (p.stepDepth last high i) (fun j => (c j).val) hk (sel i c)
        (before i c) (F.stage i c) ∧ (F.stage i c).RecordFactor e (p.pattern i).record) ∧
      ∀ i c q, (F.advance i c q).val = ((F.stage i c).result e q).dense ((after i c (F.stage i c) q).number) := by
  refine p.asPath.exists_program_with last high before after hk (fun i c s =>
    (p.pattern i).ReceiptAt (p.stepDepth last high i) (fun j => (c j).val) hk (sel i c) (before i c) s ∧
      s.RecordFactor e (p.pattern i).record) ?_
  intro i c
  exact (p.pattern i).installAt (p.stepDepth last high i) (hf i) hk (fun j => (c j).val)
    (fun j => (c j).property) (sel i c) (before i c)

end SourcePath
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
