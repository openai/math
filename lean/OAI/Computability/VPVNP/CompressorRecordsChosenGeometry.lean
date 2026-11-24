import OAI.Computability.VPVNP.CompressorRecordsTermLayout
import OAI.Computability.VPVNP.CompressorRecordsSelectedFinish

/-!
# Shrinking geometry after an admitted native term stream

The term pass writes each CD motif's grid row, repetition count and eight payload
widths. Its post-memory goes directly into the comparison, chosen placement,
absolute role scan, and bounded preimage builder. All previously written term rows
remain accessible at their original motif ordinals throughout.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ChosenGeometry

open Compression BurstRAM ShrinkMotif SelectedArena
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))
variable (dense term stride selectors : Word w) (p₀ : Fin 14 → Word w) (T : IncidenceDirectory w)
variable (cap : ℕ) (s : SelectedScore.Selection B X) (before : Memory w) (terms : List (Report w))

/-- The post-term reports of this level, with both the selected layout and child lists. -/
structure Construction (w : ℕ) where
  /-- The score, placement, and role passes executed on the memory containing the admitted term
  rows. -/
  placed : SelectedStage.Passes w
  /-- The passes that clear and collect the child preimages of the chosen placement. -/
  children : SelectedFinish.Passes w

/-- The memory after applying the placement passes and then the child-preimage passes to the
term pass's output. -/
def Construction.final (r : Construction w) (m : Memory w) := r.children.final (r.placed.final m)

/-- The chronological reports of placement followed by the child-directory clearing and
collection scans. -/
def Construction.reports (r : Construction w) := r.placed.all ++ (r.children.clear ++ r.children.collect)

/-- Execution and readback evidence for constructing the chosen geometry from the admitted
terms, including probe and scan costs. -/
structure Run (r : Construction w) : Prop where
  placed : SelectedStage.Execution X term stride selectors p₀ T (after before (eventLog terms)) r.placed
  selected : SelectedStage.Stored B X term stride p₀ s (after before (eventLog terms)) r.placed
  geometry : SelectedFinish.Built B X term stride selectors p₀ s (after before (eventLog terms)) r.placed r.children
  scores : r.placed.scores.length = 8*motifs X+2
  scoreProbes : RAMBuckets.probeCount Report.probes r.placed.scores = 32*motifs X+5
  placementCost : RAMBuckets.cost Report.probes r.placed.positions = 9*positions X
  roleCost : RAMBuckets.cost Report.probes r.placed.roles = 11*DemandRAM.oldCount X

theorem Construction.replay (r : Construction w) (m : Memory w) :
    after m (eventLog r.reports) = r.final m := by
  rw [Construction.reports,eventLog,List.flatMap_append,after,List.foldl_append]
  change after (after m (eventLog r.placed.all)) (eventLog (r.children.clear++r.children.collect)) = _
  rw [SelectedStage.Passes.all_after,SelectedFinish.Passes.after_append]
  rfl

theorem Run.charge (r : Construction w) (h : Run B X term stride selectors p₀ T s before terms r) :
    RAMBuckets.cost Report.probes r.reports = (40*motifs X+7) + 9*positions X + 11*DemandRAM.oldCount X +
      (2*ShrinkPreimages.newCount X+5*ShrinkPreimages.oldCount X) := by
  simp only [Construction.reports,SelectedStage.Passes.all,RAMBuckets.cost_append]
  rw [RAMBuckets.cost_eq_length_add_probes _ r.placed.scores,h.scores,h.scoreProbes,h.placementCost,h.roleCost,
    ← RAMBuckets.cost_append,h.geometry.raw.cost]
  omega

/-- The original admitted term rows can be read after the last preimage call. -/
theorem Run.fields (r : Construction w) (h : Run B X term stride selectors p₀ T s before terms r)
    (u : X.packingData.Motif) :
    TermRecordScan.Fields B.shrink ShrinkSliceArrays.supplyRoles demandMass_pos
      (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth u) (s u).val
      (ShrinkTermSelection.rowBase X term stride.val u) (r.final (after before (eventLog terms))) := by
  let j := (ShrinkMotifOrder.entries X).symm u
  let L := scoreTables X term stride selectors
  have hrow := h.geometry.terms j
  have hr : (SelectedScore.motifOrder X).entries j = u := (ShrinkMotifOrder.entries X).apply_symm_apply u
  have hb : SelectedScore.headAt X L j = ShrinkTermSelection.rowBase X term stride.val u := by
    dsimp only [SelectedScore.headAt,TermScores.rowBase,ShrinkTermSelection.rowBase]
    change term + (j.val : Word w)*stride = ((term.val + (ShrinkMotifOrder.stateNumber X u).val * stride.val : ℕ) : Word w)
    rw [← ShrinkMotifOrder.entries_ordinal]
    have hterm : (term.val : Word w) = term := Fin.ext (Nat.mod_eq_of_lt term.isLt)
    have hstride : (stride.val : Word w) = stride := Fin.ext (Nat.mod_eq_of_lt stride.isLt)
    simp [hterm,hstride,j]
  change TermRecordScan.Fields B.shrink SelectedScore.supplyOrder.entries demandMass_pos
    (X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth ((SelectedScore.motifOrder X).entries j))
    (s ((SelectedScore.motifOrder X).entries j)).val (SelectedScore.headAt X L j)
    (r.final (after before (eventLog terms))) at hrow
  rw [hr,hb] at hrow
  exact hrow

theorem build {first : Bool} (hp : ShrinkRAM.Params p₀ a (Shrink.colors a) (Shrink.J a) g first)
    (written : ShrinkTermSelection.Written B.shrink X dense term stride.val cap s before terms)
    (dir : let m := after before (eventLog terms)
      Shrink.Directory X.slots X.baseIndex (ShrinkRAM.column p₀ m 6) (ShrinkRAM.column p₀ m 7)
        (ShrinkRAM.column p₀ m 8) (ShrinkRAM.column p₀ m 9))
    (inc : T.ActualColumns X (after before (eventLog terms))) (old : OldInputs X term stride p₀ T)
    (hI : T.actualIn.val+DemandRAM.oldCount X ≤ origin X term stride)
    (hW : T.width.val+DemandRAM.oldCount X ≤ origin X term stride)
    (wide : 10 ≤ stride.val) (room : SelectedFinish.stop X term stride ≤ 2^w)
    (hw : ∀ t, MotifAdmission.weight relativeMass t < 2^w) (hs : selectors.val=B.shrink.selectorBits)
    (scoreFit : ∀ l, layoutScore relativeMass (X.packingData.termWidths B.shrink X.shrinkNumber X.packingWidth s) l < 2^w) :
    ∃ r : Construction w, Run B X term stride selectors p₀ T s before terms r := by
  let L := scoreTables X term stride selectors
  let m := after before (eventLog terms)
  have hterms : SelectedScore.Stored B X s (SelectedScore.headAt X L) m :=
    SelectedScore.stored_of_term_run B X L dense cap s before terms written
  have hpos : 0 < ShrinkPreimages.oldCount X := Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _)
  have fit : Fits X term stride := by
    change endAddr X term stride + ShrinkPreimages.newCount X + ShrinkPreimages.oldCount X ≤ 2^w at room
    change endAddr X term stride < 2^w
    omega
  obtain ⟨p,hep,hgp,hsc,hsp,hposc,hrole⟩ := SelectedStage.run B X term stride selectors p₀ T s m
    hterms dir inc old hI hW hp wide fit hw hs scoreFit
  obtain ⟨q,hq⟩ := SelectedFinish.build B X term stride selectors p₀ s m p hgp hterms wide room
  exact ⟨⟨p,q⟩,⟨hep,hgp,hq,hsc,hsp,hposc,hrole⟩⟩

end CompressorRecords.ChosenGeometry

end VPVNP
end Computability
end OAI
