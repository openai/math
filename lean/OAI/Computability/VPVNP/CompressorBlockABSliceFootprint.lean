import OAI.Computability.VPVNP.CompressorBlockABSliceRun
import OAI.Computability.VPVNP.CompressorShrinkABSliceFootprint

/-!
# Physical footprint of the AB interval calendar inside a block

The fixed graph input begins at its own scratch-table head. The four read
columns lie between that head and the slice table, and the latter has one
bank for each bundle. Thus the typed chronological walk supplies the progress
and external address evidence of all AB stages inside the allocated interval.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockSlices

open BurstRAM Compression Compression.PackingData PhaseRecipe ShrinkBlockInputs ShrinkSliceArrays
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (i : Fin S.steps)
variable {g w : ℕ} (X : State (a i) (packingLaneBits (a i) g))
variable (T : IncidenceDirectory w) (start : ℕ)

local notation "Z" => ShrinkInput.plan X start
local notation "t" => ShrinkInput.thickBank X T start
local notation "u" => ShrinkInput.cdBank X T start
local notation "p" => ShrinkInput.piecesBank X T start
local notation "ns" => ShrinkBundlePlan.thickCount (a i)
local notation "nt" => ShrinkBundlePlan.cap (a i)
local notation "sites" => Shrink.packedIndex (a := a i) (g := g) X.baseIndex

private theorem before_width : start ≤ ShrinkInput.widthBase X start := by
  let V := Fintype.card X.Base
  let d := 2^(a i)
  have greedy : ShrinkInput.placementBase X start =
      start+V*(6+3*d+4*Greedy.WalkLayout.tagCount d)+1 := GreedyArena.greedyStop_eq ..
  change start ≤ (((((ShrinkInput.placementBase X start+_)+_)+_)+_)+_)+_
  omega

private theorem columns_after {stride : ℕ} (room : ShrinkInput.termEnd X start stride < 2^w) :
    start ≤ (t 2).val ∧ start ≤ (t 3).val ∧ start ≤ (p 3).val ∧ start ≤ (p 4).val := by
  let W := ShrinkInput.widthBase X start
  let q := ShrinkRankSpace.Shape.collectBank Z w
  let B := (Z).B
  let Q := (Z).Q
  have lower : start ≤ W := before_width i X start
  have cap : W+6*(B*Q)+2*B < 2^w := by
    change (W+6*(B*Q)+2*B)+_+_ < _ at room; omega
  have rankFit : (Z).stop < 2^w := by change W < _; omega
  have hv : (q 4).val = Q := ((Z).values T (ShrinkInput.placementBank X T start) Fintype.card_pos rankFit).stride
  have hW : W < 2^w := rankFit
  have tc : (t 2).val = W := by change ((W%(2^w))%(2^w))=W; rw [Nat.mod_mod,Nat.mod_eq_of_lt hW]
  have ts : (t 3).val = W+2*(B*Q) := by
    change (W+2*(B*(q 4).val))%(2^w) = _
    rw [hv,Nat.mod_eq_of_lt (by omega)]
  have pc : (p 3).val = W+2*(B*Q)+2*(B*Q)+2*B := by
    change ((W+2*(B*(q 4).val))+2*(B*(q 4).val)+2*B)%(2^w) = _
    rw [hv,Nat.mod_eq_of_lt (by omega)]
  have ps : (p 4).val = W+2*(B*Q)+2*(B*Q)+2*B+B*Q := by
    change ((W+2*(B*(q 4).val))+2*(B*(q 4).val)+2*B+B*Q)%(2^w) = _
    rw [hv,Nat.mod_eq_of_lt (by omega)]
  rw [tc,ts,pc,ps]; omega

/-- Exact external interval enclosing all reads, including the old widths
and both sets of field starts. -/
theorem ab_region {first stride : ℕ} (termRoom : ShrinkInput.termEnd X start stride < 2^w)
    (fresh : ShrinkInput.stop X start ≤ first)
    (room : first+(Z).B*IndexedStarts.capacity ns nt < 2^w) :
    ShrinkABSliceRecipe.ReadRegion t p (Z).B ns nt first
      (fun x => start ≤ x ∧ x < first+(Z).B*IndexedStarts.capacity ns nt) := by
  let L := ab_layout i X T start termRoom fresh room
  have lo := columns_after i X T start termRoom
  have low : start ≤ first := by
    have h := before_width i X start
    change ShrinkInput.widthBase X start+_+_ ≤ first at fresh
    omega
  constructor
  · intro j c v hv
    obtain ⟨a,b,f,g'⟩ := ShrinkABSliceTable.columns_val L j
    have pre := (ShrinkABSliceTable.space L j).reads c
    have hb := ShrinkABSliceTable.bank_val L j
    have top := Nat.mul_le_mul_right (IndexedStarts.capacity ns nt) j.isLt.le
    have lower : start ≤ ((ShrinkABSliceTable.columns t p j.val) c).val := by
      fin_cases c
      · change start ≤ ((ShrinkABSliceTable.columns t p j.val) 0).val
        rw [a]; exact lo.2.1.trans (Nat.le_add_right ..)
      · change start ≤ ((ShrinkABSliceTable.columns t p j.val) 1).val
        rw [b]; exact lo.1.trans (Nat.le_add_right ..)
      · change start ≤ ((ShrinkABSliceTable.columns t p j.val) 2).val
        rw [f]; exact lo.2.2.2.trans (Nat.le_add_right ..)
      · change start ≤ ((ShrinkABSliceTable.columns t p j.val) 3).val
        rw [g']; exact lo.2.2.1.trans (Nat.le_add_right ..)
    exact ⟨lower.trans (Nat.le_add_right ..),by omega⟩
  · intro x hx high; exact ⟨low.trans hx,high⟩

open private inputs from OAI.Computability.VPVNP.CompressorShrinkABSliceTable

variable {F : DescriptorSpace.Shape} {origin abArena : Expr} {pub : Fin 5 → Word w}
variable {state : Word w} {ref : Memory w}

set_option maxHeartbeats 1200000 in
/-- Preserve the real stage inputs and report lists and attach the exact
cursor guards, reads and writes to every stage of the admitted block. -/
theorem ab_guarded [Nontrivial (Word w)] {first stride : ℕ} (initial : Memory w)
    (stored : DemandWidths.Stored X.packingData sites X.packingWidth X.shrinkOrder X.shrinkNumber t u p initial)
    (level : ShrinkBundlePlan.Reads X F i.val origin pub state ref start T)
    (arena : abArena.eval pub state ref = (first : Word w))
    (termRoom : ShrinkInput.termEnd X start stride < 2^w) (fresh : ShrinkInput.stop X start ≤ first)
    (room : first+(Z).B*IndexedStarts.capacity ns nt < 2^w) (widthRoom : nt*X.maxWireWidth < 2^w)
    (cap : ℕ) (hcap : 95 ≤ cap) {rs : List (Report w)}
    (walk : SourceWalk (ShrinkABSliceRecipe.Source (abInputs i origin abArena) pub state ref (Z).B cap)
      (ShrinkABSliceRecipe.phases ns nt) initial rs) :
    SourceWalk (ShrinkABSliceRecipe.Guarded (abInputs i origin abArena) pub state ref (Z).B cap
      (fun x => start ≤ x ∧ x < first+(Z).B*IndexedStarts.capacity ns nt)) (ShrinkABSliceRecipe.phases ns nt) initial rs := by
  let L := ab_layout i X T start termRoom fresh room
  have rankFit : (Z).stop < 2^w := by
    change ShrinkInput.widthBase X start < _
    change ShrinkInput.widthBase X start+_+_+_+_ < _ at termRoom
    omega
  let heads := ab_describes i X T start level rankFit arena
  let old := fun j => thickWidths X.packingData X.shrinkOrder X.packingWidth ((BundleLists.portIndex sites).symm j)
  let new := fun j => abWidths X.packingData X.shrinkNumber X.packingWidth ((BundleLists.portIndex sites).symm j)
  have hc := State.two_le_packingColors (a i)
  have hd := Nat.two_pow_pos (a i)
  have fit := ab_widthFit i X widthRoom
  have hs j : (old j).sum < 2^w := (thickWidths_sum X.packingData X.shrinkOrder X.packingWidth _).symm ▸ fit _
  have ht j : (new j).sum < 2^w := by
    dsimp only [new]
    rw [abWidths,orderedWidths,List.sum_ofFn,
      (X.shrinkNumber _).symm.sum_comp (fun z : X.packingData.MotifFiber _ => X.packingData.abWidth X.shrinkNumber X.packingWidth z.1),
      X.packingData.sum_abWidth hc hd X.shrinkNumber X.packingWidth _]
    exact fit _
  have hpow : 4 ≤ 2^(Shrink.colors (a i)) := Nat.pow_le_pow_right Nat.zero_lt_two hc
  have hprod := hpow.trans (Nat.le_mul_of_pos_right (2^(Shrink.colors (a i))) hd)
  have qpos : 0 < nt := by change 0 < 3*(2^(Shrink.colors (a i))*2^(a i))/4; omega
  have cnt : (Z).B < 2^w := (Nat.le_mul_of_pos_right _ (show 0 < IndexedStarts.capacity ns nt by unfold IndexedStarts.capacity; omega)).trans_lt (by omega)
  exact ShrinkABSliceRecipe.guarded_walk (abInputs i origin abArena) pub state ref L heads
    (ab_region i X T start termRoom fresh room) cnt old new (fun _ => List.length_ofFn) (fun _ => List.length_ofFn)
    hs ht initial (inputs X.packingData sites X.packingWidth X.shrinkOrder X.shrinkNumber t u p initial stored L)
    cap hcap walk

end CompressorRecords.BlockSlices

end VPVNP
end Computability
end OAI
