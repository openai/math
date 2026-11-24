import OAI.Computability.VPVNP.CompressorRecordsShrinkInput
import OAI.Computability.VPVNP.CompressorShrinkTermAllocation

/-!
# Selecting shrinking terms from a completed graph-input pass

The first free cell of the input construction is the dense demand head.
The next two cells per motif hold the AB/CD pair, followed by one strided
term descriptor per motif. The reports consume exactly the original
shrinking choices. Every cell of the completed graph-input arena survives
both scans, including its incidence directory, colors, offsets and old
field starts.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkInput

open BurstRAM Compression Compression.PackingData ShrinkRankSpace MotifGrid MotifBlocks ShrinkMotif
open scoped Classical

variable {w a g : ℕ} (X : State a (packingLaneBits a g)) (T : IncidenceDirectory w) (start : ℕ)

local notation "Z" => plan X start
local notation "q" => Shape.collectBank (plan X start) w
local notation "dest" => ShrinkRAM.word w (Shape.ranks (plan X start))
local notation "wb" => widthBase X start
local notation "B" => ShrinkTermSelection.bundles X
local notation "Q" => ShrinkTermSelection.ranks a
local notation "N" => B*Q

/-- Base address of the dense two-word demand pairs, immediately after the shrinking input
workspace. -/
abbrev demandHead := ShrinkRAM.word w (stop X start)
/-- Base address of the term descriptors, immediately after one dense AB/CD demand pair per
motif. -/
abbrev termHead := ShrinkRAM.word w (stop X start+2*N)
/-- Exclusive end of the descriptor array, allowing one row of the given stride after each
motif's demand pair has been allocated. -/
def termEnd (stride : ℕ) := stop X start+2*N+N*stride
/-- Prefix-scan operand bank for the thick-wire width rows in the completed shrinking input
arena. -/
abbrev thickBank := ShrinkWidthArena.prefixBank X T q dest wb false
/-- Prefix-scan operand bank for the CD width rows in the completed shrinking input arena. -/
abbrev cdBank := ShrinkWidthArena.prefixBank X T q dest wb true
/-- Operand bank for splitting each bundle's width into its ordered AB pieces in the input
arena. -/
abbrev piecesBank := ShrinkWidthArena.abBank X T q dest wb
/-- Six gather operands that pair the AB piece width with the CD width for each motif and
address the dense demand output. -/
abbrev pairBank := ShrinkTermInputs.operands (cdBank X T start) (piecesBank X T start) (demandHead (w := w) X start)

set_option maxHeartbeats 1200000 in
theorem termLayout (stride : ℕ) (room : termEnd X start stride < 2^w) :
    ShrinkDemandGather.Layout B Q (pairBank X T start) ∧
      ShrinkDemandFrame.Before B (2^(Shrink.colors a)*2^a/4) Q (thickBank X T start)
        (cdBank X T start) (piecesBank X T start) (demandHead (w := w) X start).val ∧
      (demandHead (w := w) X start).val+ShrinkTermInputs.motifCount X*2 ≤ (termHead (w := w) X start).val ∧
      (termHead (w := w) X start).val+ShrinkTermInputs.motifCount X*stride < 2^w := by
  let s := ShrinkWidthArena.scatterBank T q dest wb
  let first := ShrinkWidthArena.prefixBase X q wb
  let abStart := ShrinkWidthArena.abBase X q wb
  change stop X start+2*N+N*stride < 2^w at room
  have endSpace : stop X start = wb+6*N+2*B := rfl
  have hrank : (Z).stop < 2^w := by change wb < _; omega
  have hv := (Z).values T (placementBank X T start) Fintype.card_pos hrank
  have hs : (s 3).val = Q := hv.stride
  have hs₄ : (s 4).val = wb := Nat.mod_eq_of_lt hrank
  have hf : first = wb+2*N := by change wb+2*(B*(q 4).val) = _; rw [hv.stride]
  have ha : abStart = first+2*(B*(s 3).val)+2*B := rfl
  have hd : abStart+2*N = stop X start := by rw [ha,hf,hs,endSpace]; omega
  have hAfter : (s 4).val+2*(B*(s 3).val) ≤ first := by rw [hs₄,hs,hf]
  have hfit : first+2*(B*(s 3).val)+2*B+4*N+N*stride < 2^w := by rw [← ha]; omega
  obtain ⟨lay,early,sep,cap⟩ := ShrinkTermSelection.packed_arena s B (2^a) (Shrink.colors a) first stride
    hs.ge hAfter hfit
  let d := Fin.ofNat (2^w) (abStart+2*N)
  let t := Fin.ofNat (2^w) (abStart+2*N+2*N)
  have ed : d = demandHead (w := w) X start := congrArg (Fin.ofNat (2^w)) hd
  have et : t = termHead (w := w) X start := congrArg (fun j => Fin.ofNat (2^w) (j+2*N)) hd
  change ShrinkDemandGather.Layout B Q (ShrinkTermInputs.operands (cdBank X T start) (piecesBank X T start) d) at lay
  change ShrinkDemandFrame.Before B _ Q (thickBank X T start) (cdBank X T start) (piecesBank X T start) d.val at early
  change d.val+N*2 ≤ t.val at sep
  change t.val+N*stride < 2^w at cap
  rw [ed] at lay early
  rw [ed,et,← ShrinkTermSelection.motifCount_eq X] at sep
  rw [et,← ShrinkTermSelection.motifCount_eq X] at cap
  exact ⟨lay,early,sep,cap⟩

variable {k : Type*} [_root_.Field k] {factor : ℝ}
variable (F : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31/16) factor)


set_option maxHeartbeats 900000 in
theorem gather_select_from (before : Memory w)
    (stored : ShrinkTermSelection.oldRows X (thickBank X T start) (cdBank X T start) (piecesBank X T start) before)
    (stride : ℕ) (wide : 10 ≤ stride) (room : termEnd X start stride < 2^w)
    (fit : ShrinkTermSelection.fitConstant F+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (cap : ℕ) (gatherCap : ShrinkDemandGather.cost < cap) (termCap : TermWorker.budget F 2 8 w X.maxWireWidth ≤ cap) :
    ∃ gs, ShrinkDemandGather.Gathered B Q (pairBank X T start) cap before gs ∧
      let mid := after before (eventLog gs)
      (∀ bs : Fin (ShrinkTermInputs.motifCount X) → List Bool,
        (runSegment (ShrinkTermSelection.termProgram F (demandHead X start) (termHead X start) stride)
          cap (some 0) mid (List.ofFn bs)).isSome ↔
          ∃! s : X.ShrinkSelection F, bs = ShrinkTermSelection.tapes F X s w) ∧
      ∀ s : X.ShrinkSelection F, ∃ ts,
        ShrinkTermSelection.Written F X (demandHead X start) (termHead X start) stride cap s mid ts ∧
        ShrinkTermSelection.oldRows X (thickBank X T start) (cdBank X T start) (piecesBank X T start)
          (after mid (eventLog ts)) ∧
        ∀ addr < stop X start, after mid (eventLog ts) addr = before addr := by
  obtain ⟨layout,earlier,sep,termRoom⟩ := termLayout X T start stride room
  obtain ⟨gs,scan,legal,full⟩ := ShrinkTermSelection.gather_select F X (thickBank X T start) (cdBank X T start)
    (piecesBank X T start) (demandHead X start) (termHead X start) stride wide sep termRoom before
    stored layout earlier fit cap gatherCap termCap
  refine ⟨gs,scan,legal,fun s => ?_⟩
  obtain ⟨ts,hs,hrows⟩ := full s
  refine ⟨ts,hs,hrows,fun addr h => ?_⟩
  have hd : (demandHead (w := w) X start).val = stop X start :=
    Nat.mod_eq_of_lt (by change stop X start+2*N+N*stride < 2^w at room; omega)
  exact (hs.frame addr (.inl (by omega))).trans (scan.frame addr (.inl (hd ▸ h)))


namespace Run

variable {X T start} {m : Memory w} (r : Run X T start m)

set_option maxHeartbeats 900000 in
theorem gather_select (stride : ℕ) (wide : 10 ≤ stride) (room : termEnd X start stride < 2^w)
    (fit : ShrinkTermSelection.fitConstant F+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (cap : ℕ) (gatherCap : ShrinkDemandGather.cost < cap) (termCap : TermWorker.budget F 2 8 w X.maxWireWidth ≤ cap) :
    ∃ gs, ShrinkDemandGather.Gathered B Q (pairBank X T start) cap r.post gs ∧
      let mid := after r.post (eventLog gs)
      (∀ bs : Fin (ShrinkTermInputs.motifCount X) → List Bool,
        (runSegment (ShrinkTermSelection.termProgram F (demandHead X start) (termHead X start) stride)
          cap (some 0) mid (List.ofFn bs)).isSome ↔
          ∃! s : X.ShrinkSelection F, bs = ShrinkTermSelection.tapes F X s w) ∧
      ∀ s : X.ShrinkSelection F, ∃ ts,
        ShrinkTermSelection.Written F X (demandHead X start) (termHead X start) stride cap s mid ts ∧
        ShrinkTermSelection.oldRows X (thickBank X T start) (cdBank X T start) (piecesBank X T start)
          (after mid (eventLog ts)) ∧
        ∀ addr < stop X start, after mid (eventLog ts) addr = r.post addr :=
  gather_select_from X T start F r.post r.stored stride wide room fit cap gatherCap termCap

end Run

end CompressorRecords.ShrinkInput

end VPVNP
end Computability
end OAI
