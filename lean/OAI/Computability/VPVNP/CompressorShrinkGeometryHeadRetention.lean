import OAI.Computability.VPVNP.CompressorBlockLevelFit
import OAI.Computability.VPVNP.CompressorRecordsShrinkBranch
import OAI.Computability.VPVNP.CompressorShrinkGeometryHeadBanks
import OAI.Computability.VPVNP.CompressorShrinkInputUpperFrame

/-! # Header retention through the selected shrinking geometry

After the substep publishes its two headers, the input scans, absolute-ID
scatter, gather, term writer and selected child-directory construction run
in table zero. Their interval bounds preserve the current header below the
table and every cell at or beyond the successor header.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkGeometryHeadBanks

open BurstRAM Compression BlockHeaderRun DescriptorSpace PairSimulation.TraversalRows
open PortRefresh.TraversalHeaders ShrinkSlots
open scoped Fin.CommRing

set_option maxHeartbeats 1600000

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) (i : Fin S.steps)
variable {g w : ℕ} (X : State (ShrinkBlockInputs.a i) (packingLaneBits (ShrinkBlockInputs.a i) g))
variable (sel : SelectedScore.Selection B X) (base positions blocks : ℕ)
local notation "lay" => BlockProgram.layout B base positions blocks
variable (old new : Fin (BlockProgram.layout B base positions blocks).levels)
local notation "start" => tableBase lay old (0 : Fin 6)
local notation "z" => ShrinkInput.plan X start
local notation "stop" => ShrinkInput.stop X start
local notation "term" => ShrinkInput.termHead (w := w) X start
local notation "num" => ShrinkTermSelection.bundles X * ShrinkTermSelection.ranks (ShrinkBlockInputs.a i)
local notation "top" => levelStart lay new

/-- The original chronological reports preserve the lower and upper frame
of the active shrinking level, uniformly in the selected terms. -/
theorem beforeOutput_table_frame {headPost : Memory w} {fuel : ℕ}
    (p : ShrinkBranch.Prefix X (packedIncidence lay w old (DemandRAM.oldCount X)) start fuel headPost)
    (v : ShrinkBranch.Selected B X (packedIncidence lay w old (DemandRAM.oldCount X)) start
      10 (B.shrink.selectorBits : Word w) fuel headPost p sel)
    (sites : X.positions ≤ positions) (room : endAddress lay < 2^w) :
    ∀ j, j < start ∨ start+tableWords lay ≤ j → v.beforeOutput j = headPost j := by
  let T := packedIncidence lay w old (DemandRAM.oldCount X)
  obtain ⟨inputFit,termFit,selectedFit,_⟩ :=
    BlockLevelFit.shrink (w := w) (L := lay) B base positions blocks old rfl i X sites room
  have stopFit : stop < 2^w := inputFit.word
  have termEnd : stop+2*num+num*10 ≤ start+tableWords lay := termFit.within
  have termRoom : stop+2*num+num*10 < 2^w := termFit.word
  have tv : (term).val = stop+2*num := Nat.mod_eq_of_lt ((Nat.le_add_right ..).trans_lt termRoom)
  have dv : (ShrinkInput.pairBank X T start 5 : Word w).val = stop := Nat.mod_eq_of_lt stopFit
  have countEq := ShrinkTermSelection.motifCount_eq X
  have widthBound : (10 : Word w).val ≤ 10 := Nat.mod_le ..
  have fits : (term).val + ShrinkTermInputs.motifCount X * (10 : Word w).val ≤ start+tableWords lay := by
    rw [tv,countEq]
    exact (Nat.add_le_add_left (Nat.mul_le_mul_left _ widthBound) _).trans termEnd
  have inputRanges := ShrinkInput.range_bounds X start
  have early : start ≤ (z).gathered := by
    refine (inputRanges.1.trans inputRanges.2.1).trans ?_
    change ShrinkInput.rankBase X start ≤ ((ShrinkInput.rankBase X start+2*(z).A)+2*(z).B)+(z).rectangleSize
    exact ((Nat.le_add_right ..).trans (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have ranks : (z).ranks ≤ stop := (Nat.le_add_right (z).ranks (z).A).trans inputRanges.2.2.2
  intro j outside
  rcases outside with low | high
  · have below : j < stop := low.trans_le (inputRanges.1.trans (inputRanges.2.1.trans
      (inputRanges.2.2.1.trans inputRanges.2.2.2)))
    exact (v.lowerFrame j below).trans ((p.absoluteRun.frame j (.inl (low.trans_le early))).trans (p.input.below j low))
  · have selected : SelectedFinish.stop X term 10 ≤ j := selectedFit.within.trans high
    have gathered : (ShrinkInput.pairBank X T start 5 : Word w).val + 2*num ≤ j := by rw [dv]; exact (Nat.le_add_right ..).trans (termEnd.trans high)
    exact (v.postTerm.geometry.frame j (.inr selected)).trans
      ((v.termRun.frame j (.inr (fits.trans high))).trans
      ((p.gatherRun.frame j (.inr gathered)).trans
      ((p.absoluteRun.frame j (.inr (ranks.trans ((Nat.le_add_right ..).trans (dv ▸ gathered))))).trans
        (p.input.post_upper stopFit j ((Nat.le_add_right ..).trans (dv ▸ gathered))))))

/-- The successor's header starts beyond the end of the current scratch table. -/
theorem beforeOutput_frame (next : old.val+1 = new.val) {headPost : Memory w} {fuel : ℕ}
    (p : ShrinkBranch.Prefix X (packedIncidence lay w old (DemandRAM.oldCount X)) start fuel headPost)
    (v : ShrinkBranch.Selected B X (packedIncidence lay w old (DemandRAM.oldCount X)) start
      10 (B.shrink.selectorBits : Word w) fuel headPost p sel)
    (sites : X.positions ≤ positions) (room : endAddress lay < 2^w) :
    ∀ j, j < start ∨ top ≤ j → v.beforeOutput j = headPost j := by
  intro j outside
  apply beforeOutput_table_frame B i X sel base positions blocks old p v sites room j
  refine outside.imp id (fun high ↦ ?_)
  exact (tableEnd_le_nextLevel lay old (0 : Fin 6)).trans (next.symm ▸ high)

/-- Transport both actual pointer banks from the scalar/header substep
through the term-dependent geometry and into the resident workers. -/
theorem beforeOutput_heads {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)
    (bits : List Bool) (next : old.val+1 = new.val) (m : Memory w) {fuel : ℕ} :
    let lv := shrinkLevel B f hf i X sel bits
    let headPost := finalMemory lv lay old new m
    ∀ (_ : Substep lv lay old new (by change 6 ≤ 54; decide) m)
      (p : ShrinkBranch.Prefix X (packedIncidence lay w old (DemandRAM.oldCount X)) start fuel headPost)
      (v : ShrinkBranch.Selected B X (packedIncidence lay w old (DemandRAM.oldCount X)) start
        10 (B.shrink.selectorBits : Word w) fuel headPost p sel),
      HeadBank lay old (DemandRAM.oldCount X) m → X.positions ≤ positions → endAddress lay < 2^w →
      HeadBank lay old (DemandRAM.oldCount X) v.beforeOutput ∧
      HeadBank lay new (actualCount (levelShape (b := ShrinkBlockInputs.b i) X)) v.beforeOutput := by
  intro lv headPost sub p v bank sites room
  obtain ⟨oldHeads,newHeads⟩ := after_substep B f hf i X sel bits sub (by omega) bank
  have same := beforeOutput_frame B i X sel base positions blocks old new next p v sites room
  constructor
  · apply oldHeads.keep
    intro n hn
    apply same _ (.inl ?_)
    change levelStart lay old+n < levelStart lay old+levelHeaderWords lay+6*slotCapacity lay+0*tableWords lay
    omega
  · exact newHeads.keep (fun n _ => same _ (.inr (Nat.le_add_right _ n)))

end CompressorRecords.ShrinkGeometryHeadBanks

end VPVNP
end Computability
end OAI
