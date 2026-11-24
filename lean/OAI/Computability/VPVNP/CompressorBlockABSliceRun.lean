import OAI.Computability.VPVNP.CompressorBlockSlices
import OAI.Computability.VPVNP.CompressorShrinkABSliceCalendar
import OAI.Computability.VPVNP.CompressorShrinkInputTerms

/-!
# AB interval scans in the block's physical address space

The level planner reads the same prefix and AB heads that the demand builder
writes. Its four input columns lie below the demand head. An AB interval bank
placed after that head needs only its own rectangular capacity, and every
thick bundle sum fits under the word bound already used to build the prefixes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BlockSlices

open BurstRAM Compression Compression.PackingData PhaseRecipe
open ShrinkBlockInputs
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

/-- The width builder's four source rectangles all precede the new slice
bank. This uses the common bound on the existing term array and one end
bound on the new interval allocation. -/
theorem ab_layout {stride first : ℕ} (termRoom : ShrinkInput.termEnd X start stride < 2^w)
    (fresh : ShrinkInput.stop X start ≤ first)
    (room : first+(Z).B*IndexedStarts.capacity ns nt < 2^w) :
    ShrinkABSliceTable.Layout t p (Z).B ns nt first := by
  have h := (ShrinkInput.termLayout X T start stride termRoom).2.1
  have le : (ShrinkInput.demandHead (w := w) X start).val ≤ first :=
    (Nat.mod_le ..).trans fresh
  exact ⟨room,h.thickRanks,h.abRanks,h.thickWidths.trans le,h.thickStarts.trans le,
    h.abWidths.trans le,h.abStarts.trans le⟩

variable {F : DescriptorSpace.Shape} {origin abArena : Expr} {pub : Fin 5 → Word w}
variable {state : Word w} {ref : Memory w}

open private eval_bundles from OAI.Computability.VPVNP.CompressorShrinkBundlePlan

/-- Evaluation of the fixed block's eight AB operands in the real directory. -/
theorem ab_describes {first : ℕ} (level : ShrinkBundlePlan.Reads X F i.val origin pub state ref start T)
    (rankFit : (Z).stop < 2^w) (arena : abArena.eval pub state ref = (first : Word w)) :
    ShrinkABSliceRecipe.Describes (abInputs i origin abArena) pub state ref t p (Z).B first := by
  have thick := ShrinkBundlePlan.prefix_bank X level false rankFit
  have pieces := ShrinkBundlePlan.ab_bank X level rankFit
  exact ⟨eval_bundles X level,arena,congrFun thick 3,congrFun thick 2,congrFun thick 1,
    congrFun pieces 4,congrFun pieces 3,congrFun pieces 1⟩

/-- A bundle sum uses at most the sorted thick row count, which is at most
the CD rectangle capacity already charged to the prefix scan. -/
theorem ab_widthFit (fit : nt*X.maxWireWidth < 2^w) :
    ∀ b, X.packingData.bundleWidth X.packingWidth b < 2^w := by
  have hsmall : ns ≤ nt := by
    change 2^(Shrink.colors (a i))*2^(a i)/4 ≤ pieceCount (2^(a i)) (Shrink.colors (a i))
    unfold pieceCount; omega
  intro b
  exact ((X.packingData.bundleWidth_le (State.two_le_packingColors _) X.packingWidth
    (fun e => X.width_le_maxWireWidth _) b).trans (Nat.mul_le_mul_right X.maxWireWidth hsmall)).trans_lt fit

set_option maxHeartbeats 900000 in
/-- Execute the actual AB part of the online block calendar in the current
shrinking state. The post-memory has the exact compact lists and interval
records of every assigned bundle and preserves both outside intervals. -/
theorem ab_run {first stride : ℕ} (initial : Memory w)
    (stored : DemandWidths.Stored X.packingData sites X.packingWidth X.shrinkOrder X.shrinkNumber t u p initial)
    (level : ShrinkBundlePlan.Reads X F i.val origin pub state ref start T)
    (arena : abArena.eval pub state ref = (first : Word w))
    (termRoom : ShrinkInput.termEnd X start stride < 2^w) (fresh : ShrinkInput.stop X start ≤ first)
    (room : first+(Z).B*IndexedStarts.capacity ns nt < 2^w) (widthRoom : nt*X.maxWireWidth < 2^w)
    (cap : ℕ) (hcap : 95 ≤ cap) :
    ∃ rs, SourceWalk (ShrinkABSliceRecipe.Source (abInputs i origin abArena) pub state ref (Z).B cap)
      (ShrinkABSliceRecipe.phases ns nt) initial rs ∧
      (∀ b, IndexedStarts.Stored (ShrinkABSliceTable.bank first ns nt (BundleLists.portIndex sites b).val)
        (ShrinkSliceArrays.thickWidths X.packingData X.shrinkOrder X.packingWidth b)
        (ShrinkSliceArrays.abWidths X.packingData X.shrinkNumber X.packingWidth b) (after initial (eventLog rs))) ∧
      ∀ x, x < first ∨ first+(Z).B*IndexedStarts.capacity ns nt ≤ x → after initial (eventLog rs) x = initial x := by
  have rankFit : (Z).stop < 2^w := by
    change ShrinkInput.widthBase X start < _
    change ShrinkInput.stop X start + _ + _ < _ at termRoom
    change ShrinkInput.widthBase X start + _ + _ + _ + _ < _ at termRoom
    omega
  exact ShrinkABSliceRecipe.graph_run (abInputs i origin abArena) pub state ref X.packingData sites X.packingWidth
    X.shrinkOrder X.shrinkNumber (State.two_le_packingColors _) (Nat.two_pow_pos _) t u p initial stored
    (ab_layout i X T start termRoom fresh room) (ab_describes i X T start level rankFit arena)
    (ab_widthFit i X widthRoom) cap hcap

end CompressorRecords.BlockSlices

end VPVNP
end Computability
end OAI
