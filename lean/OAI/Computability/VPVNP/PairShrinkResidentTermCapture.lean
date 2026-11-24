import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch
import OAI.Computability.VPVNP.CompressorShrinkAllocatedTables
import OAI.Computability.VPVNP.CompressorShrinkResidentFinal

/-! # Selected demand pairs and term rows in the final shrinking memory

The paired gather writes one AB and one CD width per motif. The term worker
writes each admitted term at the same motif ordinal in a second table. The
selected geometry, resident directories and subsequent slice tables preserve
both sets of cells for the six local map calls.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkTermInputs

open BurstRAM Compression Compression.ShrinkMotif

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {w a g : ℕ} (X : State a (packingLaneBits a g)) (start stride : ℕ)
variable {sel : SelectedScore.Selection B X} {before out : Memory w}

private noncomputable local instance captureBaseDecidable : DecidableEq X.Base := Classical.decEq _

local notation "dense" => ShrinkInput.demandHead (w := w) X start
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "stop" => ShrinkInput.termEnd X start stride

/-- Exact exclusive ends of the paired gather and the term worker. -/
theorem capture_ends (room : stop < 2 ^ w) :
    (dense).val + 2 * motifCount X = (term).val ∧ (term).val + motifCount X * stride = stop := by
  let n := ShrinkTermSelection.bundles X * ShrinkTermSelection.ranks a
  change ShrinkInput.stop X start + 2*n + n*stride < 2 ^ w at room
  rw [ShrinkTermSelection.motifCount_eq]
  change ShrinkInput.stop X start % (2 ^ w) + 2*n = (ShrinkInput.stop X start + 2*n) % (2^w) ∧
    (ShrinkInput.stop X start + 2*n) % (2^w) + n*stride = ShrinkInput.stop X start + 2*n + n*stride
  rw [Nat.mod_eq_of_lt (by omega : ShrinkInput.stop X start < 2 ^ w),
    Nat.mod_eq_of_lt (by omega : ShrinkInput.stop X start + 2*n < 2 ^ w)]
  exact ⟨rfl, rfl⟩

/-- Transfer exactly the two cells per motif lying before the term table. -/
theorem pairs_transfer (room : stop < 2 ^ w) (pairs : statePairs X dense before)
    (keep : ∀ x, (dense).val ≤ x → x < (term).val → out x = before x) :
    statePairs X dense out := by
  have endPairs := (capture_ends X start stride room).1
  intro u
  let j := (ShrinkMotifOrder.stateNumber X u).val
  have hj : j < motifCount X := ((ShrinkMotifOrder.entries X).symm u).isLt
  change (out ((dense).val + 2*j)).val = _ ∧ (out ((dense).val + 2*j + 1)).val = _
  rw [keep _ (by omega) (by omega), keep _ (by omega) (by omega)]
  exact pairs u

/-- Reading the two demand cells and the ten selected term cells is stable
under later writes outside the actual dense-through-term interval. -/
theorem capture_transfer (room : stop < 2 ^ w) (wide : 10 ≤ stride)
    (pairs : statePairs X dense before)
    (fields : ∀ u, TermRecordScan.Fields B.shrink ShrinkSliceArrays.supplyRoles demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth u) (sel u).val
      (ShrinkTermSelection.rowBase X term stride u) before)
    (keep : ∀ x, (dense).val ≤ x → x < stop → out x = before x) :
    statePairs X dense out ∧ ∀ u, TermRecordScan.Fields B.shrink
      ShrinkSliceArrays.supplyRoles demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth u) (sel u).val
      (ShrinkTermSelection.rowBase X term stride u) out := by
  obtain ⟨endPairs, endTerms⟩ := capture_ends X start stride room
  refine ⟨pairs_transfer X start stride room pairs (fun x lo hi ↦ keep x lo (by omega)), ?_⟩
  intro u
  let row := ShrinkTermSelection.rowBase X term stride u
  let j := (ShrinkMotifOrder.stateNumber X u).val
  have hj : j < motifCount X := ((ShrinkMotifOrder.entries X).symm u).isLt
  have last := Nat.mul_le_mul_right stride hj
  rw [Nat.succ_mul] at last
  have addr : row.val = (term).val + j * stride := Nat.mod_eq_of_lt (by
    change (term).val + j * stride < 2 ^ w
    omega)
  have same (n : ℕ) (hn : n < 10) : out (row.val + n) = before (row.val + n) := by
    apply keep <;> rw [addr] <;> omega
  obtain ⟨grid, copies, payload⟩ := fields u
  change TermRecordScan.Fields _ _ _ _ _ row out
  refine ⟨?_, ?_, ?_⟩
  · rw [show out row.val = _ from by simpa only [Nat.add_zero] using same 0 (by decide)]
    exact grid
  · rw [same 1 (by decide)]
    exact copies
  · intro e
    have he : 2 + e.val < 10 := by have := e.isLt; omega
    rw [Nat.add_assoc, same _ he, ← Nat.add_assoc]
    exact payload e

end CompressorRecords.ShrinkTermInputs

namespace CompressorRecords.ShrinkBranch

open BurstRAM Compression Compression.ShrinkMotif

variable {w a g start cap : ℕ} {X : State a (packingLaneBits a g)} {T : IncidenceDirectory w}
variable {m : Memory w} (p : Prefix X T start cap m)
private noncomputable local instance captureBaseDecidable : DecidableEq X.Base := Classical.decEq _

local notation "dense" => ShrinkInput.demandHead (w := w) X start
local notation "term" => ShrinkInput.termHead (w := w) X start

/-- The reports in this prefix gather the two widths for each actual CD motif. -/
theorem Prefix.statePairs_beforeTerm (room : ShrinkInput.stop X start < 2 ^ w) :
    ShrinkTermInputs.statePairs X dense p.beforeTerm := by
  have stored := (p.input.keepAbsoluteFrame room p.absoluteRun.frame).stored
  intro u
  let b := X.packingData.bundle u
  let x : X.packingData.MotifFiber b := ⟨u, rfl⟩
  let r := X.shrinkNumber b x
  let j := BundleLists.portIndex (Shrink.packedIndex X.baseIndex) b
  have ab := (congrArg Fin.val (p.gatherRun.readAB j.val j.isLt r.val r.isLt)).trans
    (stored.ab.widths b r)
  have cd := (congrArg Fin.val (p.gatherRun.readCD j.val j.isLt r.val r.isLt)).trans
    (stored.cdWidths b r)
  rw [show (X.shrinkNumber b).symm r = x from (X.shrinkNumber b).symm_apply_apply x] at ab cd
  change (p.beforeTerm ((dense).val + 2 * (ShrinkMotifOrder.stateNumber X u).val)).val = _ ∧
    (p.beforeTerm ((dense).val + 2 * (ShrinkMotifOrder.stateNumber X u).val + 1)).val = _
  rw [ShrinkMotifOrder.number_val]
  exact ⟨ab, cd⟩

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {stride selectors : Word w} {sel : SelectedScore.Selection B X} {p}
variable (v : Selected B X T start stride selectors cap m p sel)
local notation "origin" => SelectedArena.origin X term stride

/-- The selected geometry and a later interval frame retain the two gathered
widths, the grid index, the repetitions and the eight chosen payload widths. -/
theorem Selected.term_capture {out : Memory w}
    (room : ShrinkInput.termEnd X start stride.val < 2 ^ w) (wide : 10 ≤ stride.val)
    (keep : ∀ x, (dense).val ≤ x → x < origin → out x = v.beforeOutput x) :
    ShrinkTermInputs.statePairs X dense out ∧ ∀ u, TermRecordScan.Fields B.shrink
      ShrinkSliceArrays.supplyRoles demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth u) (sel u).val
      (ShrinkTermSelection.rowBase X term stride.val u) out := by
  have stopRoom : ShrinkInput.stop X start < 2 ^ w := by
    unfold ShrinkInput.termEnd at room
    omega
  let afterTerm := after p.beforeTerm (eventLog v.terms)
  have pairs : ShrinkTermInputs.statePairs X dense afterTerm :=
    ShrinkTermInputs.pairs_transfer X start stride.val room (p.statePairs_beforeTerm stopRoom)
      (fun x _ hi ↦ v.termRun.frame x (.inl hi))
  have endTerms : origin = ShrinkInput.termEnd X start stride.val :=
    (ShrinkTermInputs.capture_ends X start stride.val room).2
  exact ShrinkTermInputs.capture_transfer B X start stride.val room wide pairs v.termRun.fields
    (fun x lo hi ↦ (keep x lo (hi.trans_eq endTerms.symm)).trans
      (v.postTerm.geometry.frame x (.inl (hi.trans_eq endTerms.symm))))

end CompressorRecords.ShrinkBranch

namespace CompressorRecords.ShrinkOutput

open BurstRAM Compression Compression.ShrinkMotif ShrinkBlockInputs ShrinkResidentRun

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates} {i : Fin S.steps}
variable {w g start cap : ℕ} {δ : ℝ} {X : State (a i) (packingLaneBits (a i) g)}
variable {ready : Ready (2 ^ a i) (Shrink.colors (a i)) (2 ^ b i) δ}
variable {m : Memory w} {T : IncidenceDirectory w} {stride selectors : Word w}
variable {sel : SelectedScore.Selection B X} {p : ShrinkBranch.Prefix X T start cap m}
variable (v : ShrinkBranch.Selected B X T start stride selectors cap m p sel)
private noncomputable local instance captureBaseDecidable : DecidableEq X.Base := Classical.decEq _

local notation "dense" => ShrinkInput.demandHead (w := w) X start
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "absHead" => ShrinkBundlePlan.absoluteHead (ShrinkInput.plan X start) w
local notation "origin" => SelectedArena.origin X term stride

variable {I : ShrinkABSliceRecipe.Inputs} {pub : Fin 5 → Word w} {state : Word w} {ref : Memory w}
variable {first width slotStart : ℕ} {r : TablesRun w}

/-- Capture after the AB and ordered-slot scans. The input interval frame
also permits intervening publication of the six resident heads. -/
theorem CompleteTables.term_capture_after {input : Memory w}
    (tables : CompleteTables B i X ready sel term stride absHead start I pub state ref
      first width slotStart cap input r)
    (room : ShrinkInput.termEnd X start stride.val < 2 ^ w) (wide : 10 ≤ stride.val)
    (resident : ∀ x, (dense).val ≤ x → x < origin → input x = v.beforeOutput x)
    (abFresh : origin ≤ first) (order : first ≤ width) :
    ShrinkTermInputs.statePairs X dense r.final ∧ ∀ u, TermRecordScan.Fields B.shrink
      ShrinkSliceArrays.supplyRoles demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth u) (sel u).val
      (ShrinkTermSelection.rowBase X term stride.val u) r.final := by
  apply v.term_capture room wide
  intro x lo hi
  have beforeAB := hi.trans_le abFresh
  have beforeSlots := (beforeAB.trans_le order).trans_le
    (retained_room X term stride.val (SelectedArena.roleBase X term stride) width)
  exact (tables.remainder.construction.frame x (.inl beforeSlots)).trans
    ((tables.abFrame x (.inl beforeAB)).trans (resident x lo hi))

/-- Read the dense demands and selected term in the common final snapshot
of both resident-directory scans and all three output tables. -/
theorem CompleteTables.term_capture {resident : ℕ} {role : Word w} {side : Bool}
    {h u : ShrinkResidentRun.Passes w}
    (hiddenRun : Built X resident absHead role side false v.beforeOutput h)
    (mapRun : Built X resident absHead role side true (h.final v.beforeOutput) u)
    (tables : CompleteTables B i X ready sel term stride absHead start I pub state ref
      first width slotStart cap (u.final (h.final v.beforeOutput)) r)
    (room : ShrinkInput.termEnd X start stride.val < 2 ^ w) (wide : 10 ≤ stride.val)
    (residentFresh : origin ≤ resident) (abFresh : origin ≤ first) (order : first ≤ width) :
    ShrinkTermInputs.statePairs X dense r.final ∧ ∀ u, TermRecordScan.Fields B.shrink
      ShrinkSliceArrays.supplyRoles demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth u) (sel u).val
      (ShrinkTermSelection.rowBase X term stride.val u) r.final := by
  apply tables.term_capture_after v room wide _ abFresh order
  intro x _ hi
  have early := hi.trans_le residentFresh
  exact (mapRun.frame x (.inl (early.trans_le ((ShrinkResidentLayout.layout X resident).ranges
    true).1))).trans (hiddenRun.frame x (.inl (early.trans_le
      ((ShrinkResidentLayout.layout X resident).ranges false).1)))

/-- The six header publishers lie below the demand pairs. After their writes,
the actual AB and slot passes still expose every map operand from the same branch. -/
theorem CompleteTables.published_term_capture {resident level : ℕ} {role : Word w} {side : Bool}
    {h u : ShrinkResidentRun.Passes w}
    (hiddenRun : Built X resident absHead role side false v.beforeOutput h)
    (mapRun : Built X resident absHead role side true (h.final v.beforeOutput) u)
    (tables : CompleteTables B i X ready sel term stride absHead start I pub state ref
      first width slotStart cap (endMemory X resident level v.beforeOutput h u) r)
    (room : ShrinkInput.termEnd X start stride.val < 2 ^ w) (wide : 10 ≤ stride.val)
    (headerBefore : level + 36 ≤ (dense).val) (residentFresh : origin ≤ resident)
    (abFresh : origin ≤ first) (order : first ≤ width) :
    ShrinkTermInputs.statePairs X dense r.final ∧ ∀ u, TermRecordScan.Fields B.shrink
      ShrinkSliceArrays.supplyRoles demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth u) (sel u).val
      (ShrinkTermSelection.rowBase X term stride.val u) r.final := by
  apply tables.term_capture_after v room wide _ abFresh order
  have publish := (ShrinkResidentsPlan.published level (ShrinkResidentLayout.layout X resident)
    (headerBefore.trans (dense).isLt.le) (u.final (h.final v.beforeOutput))).2
  intro x lo hi
  have early := hi.trans_le residentFresh
  exact (publish x (.inr (headerBefore.trans lo))).trans
    ((mapRun.frame x (.inl (early.trans_le ((ShrinkResidentLayout.layout X resident).ranges
      true).1))).trans (hiddenRun.frame x (.inl (early.trans_le
        ((ShrinkResidentLayout.layout X resident).ranges false).1))))

end CompressorRecords.ShrinkOutput

end VPVNP
end Computability
end OAI
