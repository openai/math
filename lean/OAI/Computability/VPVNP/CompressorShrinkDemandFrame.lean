import OAI.Computability.VPVNP.CompressorRecordsDemandWidths

/-!
# Retaining the sorted width and field-start rectangles

The dense demand array and term records can be allocated beyond the old
width tables. Any scan that preserves the preceding addresses then keeps
the six width and field-start columns required by the interval kernels.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkDemandFrame

open Compression Compression.PackingData BurstRAM

variable {w B k q : ℕ}

/-- The two old rectangles have their own strides. The balanced AB rectangle
has one live entry per CD rank. All six columns precede the scratch arena. -/
structure Before (B k q : ℕ) (thick cdRows ab : Fin 5 → BurstRAM.Word w) (head : ℕ) : Prop where
  thickRanks : k ≤ (thick 1).val
  cdRanks : q ≤ (cdRows 1).val
  abRanks : q ≤ (ab 1).val
  thickWidths : (thick 2).val+B*(thick 1).val ≤ head
  thickStarts : (thick 3).val+B*(thick 1).val ≤ head
  cdWidths : (cdRows 2).val+B*(cdRows 1).val ≤ head
  cdStarts : (cdRows 3).val+B*(cdRows 1).val ≤ head
  abWidths : (ab 3).val+B*(ab 1).val ≤ head
  abStarts : (ab 4).val+B*(ab 1).val ≤ head

private theorem cell_lt {base head stride : ℕ} (b : Fin B) (i : Fin k) (hs : k ≤ stride)
    (h : base+B*stride ≤ head) : base+b.val*stride+i.val < head := by
  have row := Nat.mul_le_mul_right stride b.isLt
  rw [Nat.succ_mul] at row
  have := i.isLt
  omega

variable {V H T L : Type} {d c n : ℕ} [AddCommGroup H] [AddCommGroup T] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype T] [Fintype L]
variable [DecidableEq V] [DecidableEq T] [DecidableEq L]
variable {P : PackingData V H T L d c} {site : Site V T L ≃ Fin n} {old : Arc V H T L d c → ℕ}
variable {dd : P.ThickNumbering} {cd : P.BundleNumbering} {thick cdRows ab : Fin 5 → BurstRAM.Word w}

/-- The six source columns still represent the same old widths and starts
after the dense demand and term phases. -/
theorem retain {mem out : Memory w} {head : ℕ}
    (stored : DemandWidths.Stored P site old dd cd thick cdRows ab mem)
    (earlier : Before (n*d) (2^c*d/4) (pieceCount d c) thick cdRows ab head)
    (keep : ∀ a < head, out a = mem a) :
    DemandWidths.Stored P site old dd cd thick cdRows ab out := by
  let idx := BundleLists.portIndex (d := d) site
  refine ⟨fun b i => ?_,fun b i => ?_,fun b x => ?_,fun b x => ?_,⟨fun b i => ?_,fun b i => ?_⟩⟩
  · rw [keep _ (cell_lt (idx b) i earlier.thickRanks earlier.thickWidths)]; exact stored.thickWidths b i
  · rw [keep _ (cell_lt (idx b) i earlier.cdRanks earlier.cdWidths)]; exact stored.cdWidths b i
  · rw [keep _ (cell_lt (idx b) (dd b x) earlier.thickRanks earlier.thickStarts)]; exact stored.thickStarts b x
  · rw [keep _ (cell_lt (idx b) (cd b x) earlier.cdRanks earlier.cdStarts)]; exact stored.cdStarts b x
  · rw [keep _ (cell_lt (idx b) i earlier.abRanks earlier.abWidths)]; exact stored.ab.widths b i
  · rw [keep _ (cell_lt (idx b) i earlier.abRanks earlier.abStarts)]; exact stored.ab.starts b i

end CompressorRecords.ShrinkDemandFrame

end VPVNP
end Computability
end OAI
