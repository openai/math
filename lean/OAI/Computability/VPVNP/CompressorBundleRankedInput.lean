import OAI.Computability.VPVNP.CompressorRecordsRankedDirectory
import OAI.Computability.VPVNP.CompressorBundleSortedWidths

/-!
# Reading the ranked shrinking directory in the width scatter

The three arrays left by `ranked_directory` are the owner, rank and
width inputs of the native scatter. Every actual port address is shared
with the classification pass. Representability of the old widths gives
their exact natural values.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.BundleWidthScatter

open BurstRAM Compression BundleKeys BundleLists

variable {w a g : ℕ} (X : State a (packingLaneBits a g))
local notation "N" => Fintype.card X.Base
local notation "A" => N * 2^(packingLaneBits a g) * 2^a
local notation "P" => X.packingData
local notation "arcs" => oldArcOrder (a := a) (g := g) X.baseIndex
local notation "sites" => Shrink.packedIndex (a := a) (g := g) X.baseIndex

/-- Assemble the typed scatter input from the final four-pass directory
readbacks. Each array uses the original absolute outgoing arc ID. -/
theorem ranked_input (T : IncidenceDirectory w) (q : Fin 6 → Word w) (dest sorted : Word w)
    (mem : Memory w)
    (space : Layout (scatterPublic q dest T.width sorted) A (N*(2^(Shrink.J a)*2^g)) (2^a) (Shrink.colors a))
    (fit : ∀ e : OldArc X.Base a g, X.packingWidth e < 2^w)
    (motifs : ∀ b (x : (P).MotifFiber b), mem (dest.val+(arcs x.val.val).val) = Fin.ofNat _ (X.shrinkNumber b x).val)
    (thick : ∀ b (x : (P).ThickFiber b), mem (dest.val+(arcs x.val.val).val) = Fin.ofNat _ (X.shrinkOrder b x).val)
    (widths : ∀ e : OldArc X.Base a g, mem (T.width.val+(arcs e).val) = Fin.ofNat _ (X.packingWidth e))
    (owners : ∀ e : OldArc X.Base a g, mem ((q 1).val+(arcs e).val) = Fin.ofNat _ (bucketIndex sites (bucketOf P e)).val) :
    RankedInput P X.shrinkNumber X.shrinkOrder arcs sites (scatterPublic q dest T.width sorted) mem X.packingWidth := by
  let s := scatterPublic q dest T.width sorted
  have addr (e : OldArc X.Base a g) (t : Fin 3) :
      (source s t (arcWord arcs e)).val = (s (t.castAdd 2)).val+(arcs e).val := by
    have h := space.sourceFits t
    change (s (t.castAdd 2)).val+A ≤ 2^w at h
    rw [source,Fin.val_add,Fin.val_ofNat,Nat.add_mod_mod,Nat.mod_eq_of_lt (by have := (arcs e).isLt; omega)]
  constructor
  · intro e
    rw [addr e 0]; exact owners e
  · intro e
    rw [addr e 1]
    by_cases h : (P).thick (sourcePosition e) ∧ (P).thick (sourcePosition ((P).actual e))
    · let x : (P).ThickFiber e.1 := ⟨⟨e,h⟩,rfl⟩
      rw [show rankOf P X.shrinkNumber X.shrinkOrder e = (X.shrinkOrder e.1 x).val from
        rank_thick P X.shrinkNumber X.shrinkOrder x]
      exact thick _ x
    · let m : (P).Motif := ⟨e,h⟩
      let x : (P).MotifFiber ((P).bundle m) := ⟨m,rfl⟩
      rw [show rankOf P X.shrinkNumber X.shrinkOrder e = (X.shrinkNumber _ x).val from
        rank_motif P X.shrinkNumber X.shrinkOrder x]
      exact motifs _ x
  · intro e
    rw [addr e 2]
    change (mem (T.width.val+(arcs e).val)).val = _
    rw [widths,Fin.val_ofNat,Nat.mod_eq_of_lt (fit e)]

end CompressorRecords.BundleWidthScatter

end VPVNP
end Computability
end OAI
