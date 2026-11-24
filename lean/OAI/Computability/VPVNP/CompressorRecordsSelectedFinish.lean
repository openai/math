import OAI.Computability.VPVNP.CompressorRecordsSelectedStage
import OAI.Computability.VPVNP.CompressorRecordsSelectedPreimages

/-! # Retaining the selected term and its complete preimage directory

The new arrays are allocated after the old-arc role table. Clearing the
counts and appending children therefore preserves the chosen term, layout,
placement and role records at their original addresses.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.SelectedFinish

open Compression BurstRAM ShrinkMotif SelectedArena
open PairSimulation.LocalHistory PairSimulation.TraversalRows
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
variable {a g w : ℕ} (X : State a (packingLaneBits a g))
variable (term stride selectors : Word w) (p₀ : Fin 14 → Word w) (s : SelectedScore.Selection B X)
variable (mem : Memory w) (p : SelectedStage.Passes w)

/-- The Boolean shrink layout selected for all motifs by comparing their aggregate supply
energies for the given term choices. -/
abbrev chosen := X.packingData.shrinkTermLayout B.shrink X.shrinkNumber X.packingWidth s
/-- The shrink-worker operand vector using the chosen-layout word actually stored by the
completed score passes. -/
abbrev shr := selectedWords X term stride p₀ (p.afterScores mem)

/-- All physical artifacts of the selected shrinking branch, after the two
new native passes in their chronological memory. -/
structure Built (q : Passes w) : Prop where
  raw : Collected X term stride (shr X term stride p₀ mem p) (chosen B X s) (p.final mem) q
  chosenCell : q.final (p.final mem) (origin X term stride+2) = ((chosen B X s).toNat : Word w)
  placement : ShrinkRAM.PlacementColumns X.slots X.baseIndex (shr X term stride p₀ mem p)
    (chosen B X s) (q.final (p.final mem))
  roles : DemandRAM.RoleColumns X (chosen B X s) (roleBase X term stride) (q.final (p.final mem))
  terms : SelectedScore.Stored B X s (SelectedScore.headAt X (scoreTables X term stride selectors))
    (q.final (p.final mem))
  frame : ∀ j, j < origin X term stride ∨ stop X term stride ≤ j → q.final (p.final mem) j = mem j

private theorem preserve_terms (room : stop X term stride ≤ 2^w) (wide : 10 ≤ stride.val)
    (h : SelectedScore.Stored B X s (SelectedScore.headAt X (scoreTables X term stride selectors)) mem)
    (post : Memory w) (fr : ∀ j, j < origin X term stride → post j = mem j) :
    SelectedScore.Stored B X s (SelectedScore.headAt X (scoreTables X term stride selectors)) post := by
  let L := scoreTables X term stride selectors
  intro i
  have hi := Nat.mul_le_mul_right stride.val i.isLt
  rw [Nat.succ_mul] at hi
  have hfit : origin X term stride ≤ 2^w := by
    dsimp only [stop,rowStart,countStart,endAddr,roleBase,placementBase] at room
    omega
  change i.val*stride.val+stride.val ≤ motifs X*stride.val at hi
  have hbase : (SelectedScore.headAt X L i).val = term.val+i.val*stride.val := by
    apply TermScores.rowBase_val
    change term.val+i.val*stride.val < 2^w
    unfold origin at hfit; omega
  have small (j : ℕ) (hj : j<10) : (SelectedScore.headAt X L i).val+j < origin X term stride := by
    unfold origin; rw [hbase]; omega
  obtain ⟨d,r,fields⟩ := h i
  refine ⟨?_,?_,?_⟩
  · have hz := small 0 (by decide)
    rw [Nat.add_zero] at hz
    rwa [fr _ hz]
  · rwa [fr _ (small 1 (by decide))]
  · intro j
    have hf : 2+j.val < 10 := by have hj : j.val < 8 := j.isLt; omega
    have hs := small _ hf
    rw [← Nat.add_assoc] at hs
    rw [fr _ hs]
    exact fields j

/-- Execute the preimage build from the actual final memory of the score,
placement, and role passes, including nonzero prior workspace contents. -/
theorem build (stored : SelectedStage.Stored B X term stride p₀ s mem p)
    (terms : SelectedScore.Stored B X s (SelectedScore.headAt X (scoreTables X term stride selectors)) mem)
    (wide : 10 ≤ stride.val) (room : stop X term stride ≤ 2^w) :
    ∃ q, Built B X term stride selectors p₀ s mem p q := by
  let bit := (p.afterScores mem) (origin X term stride+2)
  obtain ⟨q,raw⟩ := collect X term stride p₀ bit (chosen B X s) (p.final mem) room stored.placement
  have stopEq : stop X term stride = endAddr X term stride + ShrinkPreimages.newCount X + ShrinkPreimages.oldCount X := rfl
  have pos : 0 < ShrinkPreimages.oldCount X := Nat.mul_pos Fintype.card_pos (Nat.two_pow_pos _)
  have fit : Fits X term stride := by change endAddr X term stride < _; omega
  have before (j : ℕ) (hj : j < endAddr X term stride) : q.final (p.final mem) j = p.final mem j :=
    raw.frame j (Or.inl hj)
  have all (j : ℕ) (hj : j < origin X term stride ∨ stop X term stride ≤ j) : q.final (p.final mem) j = mem j := by
    rcases hj with lo|hi
    · have endGt : origin X term stride < endAddr X term stride := by unfold endAddr roleBase placementBase; omega
      exact (before j (lo.trans endGt)).trans (stored.frame j (Or.inl lo))
    · exact (raw.frame j (Or.inr hi)).trans (stored.frame j (Or.inr (by omega)))
  refine ⟨q,⟨raw,?_,?_,?_,preserve_terms B X term stride selectors s mem room wide terms _ (fun j hj => all j (.inl hj)),all⟩⟩
  · exact (before _ (by unfold endAddr roleBase placementBase; omega)).trans stored.chosen
  · constructor
    intro x
    let i := ShrinkRAM.word w (Shrink.oldNumber X.baseIndex x)
    have hsmall : i.val < positions X := (Nat.mod_le ..).trans_lt
      ((Shrink.oldIndex_val X.baseIndex x) ▸ (Shrink.oldIndex X.baseIndex x).isLt)
    have keep (t : Fin 4) : q.final (p.final mem) (ShrinkRAM.outAddr (shr X term stride p₀ mem p) t i) =
        p.final mem (ShrinkRAM.outAddr (shr X term stride p₀ mem p) t i) := by
      apply before
      have ht := Nat.mul_le_mul_right (positions X) t.isLt
      rw [Nat.succ_mul] at ht
      change (((shrinkWords X term stride p₀ bit) (t.natAdd 10)).val + i.val) % (2^w) < _
      apply (Nat.mod_le ..).trans_lt
      rw [output_column X term stride p₀ bit fit]
      unfold endAddr roleBase; omega
    change ((q.final (p.final mem) (ShrinkRAM.outAddr _ 0 i)).val, (q.final (p.final mem) (ShrinkRAM.outAddr _ 1 i)).val,
      (q.final (p.final mem) (ShrinkRAM.outAddr _ 2 i)).val, (q.final (p.final mem) (ShrinkRAM.outAddr _ 3 i)).val) = _
    rw [keep 0,keep 1,keep 2,keep 3]
    exact stored.placement.atSite x
  · constructor
    · intro e
      rw [before]
      · exact stored.roles.cd e
      · have hi : (DemandRAM.absoluteIndex X e).val < DemandRAM.absoluteCount X := (DemandRAM.absoluteIndex X e).isLt
        unfold endAddr; omega
    · intro e r
      rw [before]
      · exact stored.roles.packed e r
      · have hi : (DemandRAM.absoluteIndex X e.val).val < DemandRAM.absoluteCount X := (DemandRAM.absoluteIndex X e.val).isLt
        have hr : SlotOwners.roleOffset r < 3 := by cases r <;> decide
        unfold endAddr; omega

section DFS

open NetworkKernel MotifBlocks MotifGrid MotifConversion SurvivingSlots

variable {R : Type*} [CommRing R] {δ : ℝ} {b : ℕ}
variable (κ : (parameterData B.shrink).Entry → R) (hκ : (parameterData B.shrink).IsSolution κ)
variable (ready : Ready (2^a) (Shrink.colors a) (2^b) δ)

/-- The final chronological memory supplies the DFS row data for the actual
selected pass term and the site orders of its actual source and next states. -/
def Built.selectedDirectory {q : Passes w} (r : Built B X term stride selectors p₀ s mem p q)
    (room : stop X term stride ≤ 2^w) :
    PairSimulation.TraversalRows.Directory (ShrinkPreimages.selectedTerm X B.shrink κ hκ ready s)
      (siteOrder X) (siteOrder (X.shrinkNext B.shrink ready s)) (q.final (p.final mem)) (stop X term stride) := by
  let bit := (p.afterScores mem) (origin X term stride+2)
  have ar := areas X term stride p₀ bit room
  apply ShrinkPreimages.selectedDirectory X B.shrink κ hκ ready s ar _ r.raw.preimages
  rw [← ShrinkPreimages.oldCount_eq X]
  exact Nat.add_le_add_right (Nat.mod_le ..) _

end DFS
end CompressorRecords.SelectedFinish

end

end VPVNP
end Computability
end OAI
