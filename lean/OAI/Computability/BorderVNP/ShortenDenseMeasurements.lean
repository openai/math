import OAI.Computability.BorderVNP.PackedHistoryDenseStep
import OAI.Computability.BorderVNP.ShortenPlacedMeasurements

/-!
# The measured shortening rows for the publicly sorted input

Reordering the disjoint input preserves its full bin count vector and
charged length. The record and motion estimates therefore use the same
input mean, while the output length and midpoint population are evaluated
on the actual stable-order partition and its newly fitted hooks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.Stage

open Cover Crossing Packing Shortening CombiningStep Epoch SeedIntervals Finset
open scoped Classical

variable {D m k d d' : ℕ} [NeZero D] {K : Type*} [Field K] {I B P : Type}
    [Fintype I] [Fintype B] {bits : P → ℕ} {child : Fin k → PlacedPack D P bits K I d}

/-- Input measurements on the physical union sorted by public cable rows. -/
structure Measurements (s : Stage m B d' child) (hk : 0 < k) (h ν u v : ℝ) where
  /-- The same expected bin population as before reindexing. -/
  mean : ((I → Deck (d'+1)) × B) → ℝ
  /-- Source midpoint attached to each sorted cable. -/
  oldMid : s.input.layout.Edge → SurfaceHost I (d'+1)
  /-- Address attached to each sorted cable. -/
  addr : s.input.layout.Edge → ((I → Deck (d'+1)) × B)
  /-- Total length of the measured, moved, reordered input. -/
  keeps : s.placed.input s.input s.label s.perm = ∑ i, (child i).length
  /-- Actual endpoint hooks in the stable-order allocation fit their own charts. -/
  fits : s.placed.fits s.input s.label s.perm s.orient h ν
  /-- Each sorted address and midpoint describe the actual moved input cable. -/
  midpoint : ∀ c a, s.label c = some a → addr c = a ∧ a.1 = productTileName d' (oldMid c) ∧
    dist (oldMid c) (s.placed.old (s.input.layout.src c)) ≤
      dist (s.placed.old (s.input.layout.src c)) (s.placed.old (s.input.layout.dst c))/2
  /-- Every seed retains its own midpoint tile under the direction permutations. -/
  center : ∀ a, (s.perm 0 a).1 = productTileName d' (s.placed.project a (s.placed.chart a).center)
  /-- Coverage by the actual sampled mean before matching. -/
  half : (s.placed.input s.input s.label s.perm / k) / 2 ≤
    matchedLength s.perm (fun a => 2*(s.placed.chart a).radius) mean
  /-- Tile-normalized Euclidean norm of that mean. -/
  norm : Real.sqrt (Fintype.card (I → Deck (d'+1))) * Real.sqrt (binEnergy mean) ≤
    u * (s.placed.input s.input s.label s.perm / k)
  /-- Equation (6.2) for the very same samples on the sorted bin counts. -/
  deviation : Real.sqrt (Fintype.card (I → Deck (d'+1))) *
    Real.sqrt (binEnergy fun a => count s.input.layout s.label a / k - mean a) ≤
      v * PlacedStep.childMaximum child hk / Real.sqrt k

variable (s : Stage m B d' child) (r : PlacedStep m B d' child)

omit [Field K] in
set_option maxHeartbeats 1200000 in
/-- Transport only the input measurements. The fit for the actual dense
allocation is supplied by its independently rebuilt canonical placement. -/
theorem measurements_dense {hk : 0 < k} {h ν u v : ℝ}
    (M : PlacedStep.Measurements r hk h ν u v) (hbin : s.bin = r.bin) (hperm : s.perm = r.perm)
    (hold : s.placed.old = r.placed.old) (hchart : s.placed.chart = r.placed.chart)
    (hproject : s.placed.project = r.placed.project) (fit : s.placed.fits s.input s.label s.perm s.orient h ν) :
    Nonempty (Measurements s hk h ν u v) := by
  let ep := Names.denseSlot (raw child).layout s.slot
  let moved : PlacedPack D (Fin k × P) (fun z => bits z.2) K I d' :=
    ⟨raw child,r.placed.old,fun c => (r.bin c).isSome,M.oldMid⟩
  have len : s.placed.input s.input s.label s.perm = r.placed.input (raw child) r.bin r.perm := by
    unfold Placement.input
    rw [hold]
    change chargedLength (DirectoryCircuit.densePack (raw child) s.slot).layout r.placed.old
      (fun c => (s.bin (ep.symm c)).isSome) = _
    rw [hbin]
    exact moved.dense_length s.slot
  have src (x : (raw child).layout.Edge) : s.input.layout.src (ep x) = (raw child).layout.src x :=
    Names.src_slot _ _ _ x
  have dst (x : (raw child).layout.Edge) : s.input.layout.dst (ep x) = (raw child).layout.dst x :=
    Names.dst_slot _ _ _ x
  refine ⟨{
    mean := M.mean
    oldMid := M.oldMid ∘ ep.symm
    addr := M.addr ∘ ep.symm
    keeps := len.trans (r.input_length M.keeps)
    fits := fit
    midpoint := ?_
    center := ?_
    half := ?_
    norm := ?_
    deviation := ?_ }⟩
  · intro c a hc
    obtain ⟨x,rfl⟩ := ep.surjective c
    have htag : r.bin x = some a := by
      change s.bin (ep.symm (ep x)) = some a at hc
      simpa only [Equiv.symm_apply_apply,hbin] using hc
    change M.addr (ep.symm (ep x)) = a ∧ a.1 = productTileName d' (M.oldMid (ep.symm (ep x))) ∧
      dist (M.oldMid (ep.symm (ep x))) (s.placed.old (s.input.layout.src (ep x))) ≤
        dist (s.placed.old (s.input.layout.src (ep x))) (s.placed.old (s.input.layout.dst (ep x)))/2
    rw [ep.symm_apply_apply,src,dst,hold]
    exact M.midpoint x a htag
  · simpa only [hperm,hproject,hchart] using M.center
  · simpa only [len,hperm,hchart] using M.half
  · simpa only [len] using M.norm
  · change Real.sqrt _ * Real.sqrt (binEnergy fun a =>
      count (Names.denseLayout (raw child).layout s.slot) (CutCircuit.denseBin _ s.slot s.bin) a / k - M.mean a) ≤ _
    simp only [CutCircuit.dense_count,hbin]
    exact M.deviation

/-- Both physical rows, with a single coefficient per prepared bin and motion
catalog, valid for every chosen stable row order and attained histogram. -/
theorem measured_rows (e : PaidIdentity K D m) (hm : 0 < m) :
    ∃ ν : ℝ, 0 < ν ∧ ∃ h : ℝ, 0 < h ∧ ∀ (B : Type) [Fintype B] (u v : ℝ), 0 ≤ u → 0 ≤ v →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {k d d' : ℕ} (hk : 0 < k) {P : Type} {bits : P → ℕ}
      (child : Fin k → PlacedPack D P bits K I d) (s : Stage m B d' child), Measurements s hk h ν u v →
      ∀ V : ℝ, (Fintype.card (I → Deck (d'+1)) : ℝ) ≤ V → ∀ q : s.Index e,
      let W := (∑ i, (child i).length) / k
      let X := PlacedStep.childMaximum child hk
      (s.result e q).length / k ≤ max 0 (1-(ν/2)/2)*W + C*(Real.sqrt k)⁻¹*X + C*V ∧
      (s.result e q).concentration / k ≤ C*(W+(Real.sqrt k)⁻¹*X) := by
  obtain ⟨ν,hν,h,hh,uniform⟩ := physical_rows (I := I) e hm
  refine ⟨ν,hν,h,hh,?_⟩
  intro B _ u v hu hv
  obtain ⟨C,hC,bound⟩ := uniform (B := B) u v hu hv
  refine ⟨C,hC,?_⟩
  intro k d d' hk P bits child s M V hv q W X
  let z : Fin k := ⟨0,hk⟩
  have hX : 0 ≤ PlacedStep.childMaximum child hk := by
    unfold PlacedStep.childMaximum
    exact (PlacedPack.nonneg (child z)).2.trans
      (Finset.le_sup' (s := (Finset.univ : Finset (Fin k))) (fun i => (child i).concentration) (mem_univ z))
  have h := bound d' k hk s.input s.label s.perm s.orient s.placed M.fits M.oldMid M.addr M.midpoint M.center
    M.mean _ V hX hv M.half M.norm M.deviation q
  rw [M.keeps] at h
  exact h

end PackedHistoryCircuit.Normalized.Stage

end BorderVNP
end Computability
end OAI
