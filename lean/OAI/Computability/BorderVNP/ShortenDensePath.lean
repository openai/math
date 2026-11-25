import OAI.Computability.BorderVNP.ShortenDenseTemplates

/-!
# Installing a prepared program on the requested public row names

The input and saved-output directories supply their stable sparse row slots.
Any certificate carried by the selected measured stage, such as its exact
frame samples or a physical record bound, remains attached to that stage in
the program. All stored successor networks are the dense reindexing of the
particular profile reached in that public row order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized

open Crossing Epoch Cover Shortening Packing Catalog
open scoped Classical

variable {D m b k : ℕ} [NeZero D] {K : Type*} [Field K] {I P : Type} [Fintype I]
    {bits : P → ℕ} {hCap hSaving ν : ℝ} {e : PaidIdentity K D m}

/-- A sparse public cable directory records the entire slot rectangle and the
stable occupied row of every real cable, including zero-width cables. -/
structure CableSlots {D : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} (p : Pack D P bits K) where
  /-- Total number of rows, including padding. -/
  rows : ℕ
  /-- The occupied row of each real cable. -/
  number : p.layout.Edge ↪ Fin rows

/-- Canonical finite slots when an external consumer does not prescribe a directory. -/
noncomputable def CableSlots.all {D : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} (p : Pack D P bits K) : CableSlots p :=
  ⟨Fintype.card p.layout.Edge,(Fintype.equivFin _).toEmbedding⟩

variable {S : Finset (HyperbolicHost I)}

/-- Move from the calculated input level of a stage to the level in its schedule. -/
theorem StageTemplate.atLevel (t : StageTemplate e I hCap hSaving ν S) {old next : ℕ}
    (he : old = next+2*t.word) (hf : t.floor ≤ next) (hk : 0 < k)
    (child : Fin k → PlacedPack D P bits K I old) (hc : ∀ i, PlacedAt S hCap (child i))
    (dir : CableSlots (raw child)) :
    ∃ s : Stage m t.Bin next child, s.rowCount = dir.rows ∧ (∀ x, (s.slot x).val = (dir.number x).val) ∧
      Nonempty (Stage.Measurements s hk hSaving ν t.meanFactor t.motionFactor) ∧
      ∀ q : s.Index e, PlacedAt t.nextSites hCap (s.result e q) := by
  subst old
  exact t.run next hf hk child hc dir.rows dir.number

namespace StagePath

variable (path : StagePath b e I hCap hSaving ν) (last high : ℕ)
variable (before : ∀ (i : Fin b) (c : Fin k → path.State P bits k last high i.val),
  CableSlots (raw (fun j => (c j).val)))
variable (after : ∀ (i : Fin b) (c : Fin k → path.State P bits k last high i.val)
  (s : Stage m (path.pattern i).Bin (path.depth last high (i.val+1)) (fun j => (c j).val))
  (q : s.Index e), CableSlots (s.result e q).pack)

/-- A program on the prepared levels and relative states of this exact path. -/
abbrev ProgramAt (P : Type) (bits : P → ℕ) (k last high : ℕ) :=
  Program (B := fun i => (path.pattern i).Bin) e (fun j (p : path.State P bits k last high j) => p.val)

set_option maxHeartbeats 1200000 in
/-- Install each selected measured stage along with any additional local
certificate. This chooses the stable input and storage directories before
reading the corresponding profile index. -/
theorem exists_program_with (hk : 0 < k)
    (cert : ∀ (i : Fin b) (c : Fin k → path.State P bits k last high i.val),
      Stage m (path.pattern i).Bin (path.depth last high (i.val+1)) (fun j => (c j).val) → Prop)
    (choose : ∀ (i : Fin b) (c : Fin k → path.State P bits k last high i.val),
      ∃ s : Stage m (path.pattern i).Bin (path.depth last high (i.val+1)) (fun j => (c j).val),
        s.rowCount = (before i c).rows ∧ (∀ x, (s.slot x).val = ((before i c).number x).val) ∧
        Nonempty (Stage.Measurements s hk hSaving ν (path.pattern i).meanFactor (path.pattern i).motionFactor) ∧
        cert i c s ∧ ∀ q : s.Index e, PlacedAt (path.pattern i).nextSites hCap (s.result e q)) :
    ∃ F : path.ProgramAt P bits k last high,
      (∀ i c, (F.stage i c).rowCount = (before i c).rows ∧ ∀ x, ((F.stage i c).slot x).val = ((before i c).number x).val) ∧
      (∀ i c, Nonempty (Stage.Measurements (F.stage i c) hk hSaving ν (path.pattern i).meanFactor (path.pattern i).motionFactor)) ∧
      (∀ i c, cert i c (F.stage i c)) ∧
      ∀ i c q, (F.advance i c q).val = ((F.stage i c).result e q).dense ((after i c (F.stage i c) q).number) := by
  choose s cap slot M extra closed using choose
  let good := fun j (p : PlacedPack D (Adaptive.Port k P j) (Adaptive.width bits k j) K I (path.depth last high j)) =>
    PlacedAt (path.catalog j) hCap p
  let size := fun i c q => (after i c (s i c) q).rows
  let number := fun i c q => (after i c (s i c) q).number
  have hc (i : Fin b) (c : Fin k → path.State P bits k last high i.val) (q : (s i c).Index e) :
      good (i.val+1) (((s i c).result e q).dense (number i c q)) := by
    change PlacedAt (path.catalog (i.val+1)) hCap _
    rw [path.next i]
    exact placedAt_dense _ (closed i c q) _
  exact ⟨Program.ofDenseClosed good s size number hc,fun i c => ⟨cap i c,slot i c⟩,M,extra,fun _ _ _ => rfl⟩

/-- A sufficient starting threshold supplies the calculated stage depths,
including the final site motion. -/
theorem levels_at_start (lastFloor : ℕ) (hh : path.threshold last lastFloor ≤ high) :
    path.depth last high 0 = high ∧
      lastFloor ≤ high - Adaptive.Levels.totalDrop (fun i => (path.pattern i).word) last ∧
      (∀ i : Fin b, (path.pattern i).floor ≤ path.depth last high (i.val+1)) ∧
      (∀ j, Fintype.card (I → Deck (path.depth last high j+1)) ≤ Fintype.card (I → Deck (high+1))) := by
  let w := fun i => (path.pattern i).word
  let l := high - Adaptive.Levels.totalDrop w last
  obtain ⟨hs,hl,hf⟩ := Adaptive.Levels.of_start w last lastFloor (fun i => (path.pattern i).floor) hh
  exact ⟨hs,hl,hf,fun j => (Adaptive.Levels.tiles_le_start w I l last j).trans_eq
    (congrArg (fun v => Fintype.card (I → Deck (v+1))) hs)⟩

end StagePath
end PackedHistoryCircuit.Normalized

end BorderVNP
end Computability
end OAI
