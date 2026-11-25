import OAI.Computability.BorderVNP.CubeScatterPacketStreams
import OAI.Computability.BorderVNP.CubeScatterVisits
import OAI.Computability.BorderVNP.CubeISAOwnedPacketCount

/-! # Canonical common words of each strict label-pair view

Both incident groups read the same selector stream. Its crossing suffix consists
of packet bits in the stable packet-counter order, then singleton bits in the two
orientations. These lists realize the exact widths of the declaration at its chosen cut.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open Physical Physical.Owned VPVNP.MotifBase Tally

variable {n d blocks b h K s : ℕ}

/-- The selector prefix of one actual strict symbol-pair row. -/
def commonSelectors (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d) : List Bool :=
  (packetVisits blocks i sym).flatMap (selectorStream ∘ select)

/-- The stable crossing suffix of one actual strict row. It visits both singleton orientations once. -/
def commonCrossings (b : ℕ) (i : Fin (n+1)) (sym : Symbols d)
    (select : Packet n d blocks → Selector n K h)
    (z : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot n d blocks (h*b) → Bool) : List Bool :=
  (packetVisits blocks i sym).flatMap (fun p => crossingStream b (select p) i (z p)) ++
    (singleVisits blocks (h*b) i sym.val.1 sym.val.2).map single ++
    (singleVisits blocks (h*b) i sym.val.2 sym.val.1).map single

/-- The public row descriptor reserves exactly the emitted little-endian selector words. -/
theorem commonSelectors_length (select : Packet n d blocks → Selector n K h) (i : Fin (n+1)) (sym : Symbols d) :
    (commonSelectors select i sym).length = rowSelectorBits n d blocks K h i (Sym2.mk sym.val.1 sym.val.2) := by
  simp only [commonSelectors,List.length_flatMap,Function.comp_def,selectorStream_length]
  rw [packetVisits_sum,strict_rowSelectorBits]
  simp [card_packets_row,selectorWidth,VPVNP.MotifWidths.selectorBits,Selector]

private theorem single_ones {n d blocks b h K s : ℕ} (select : Packet n d blocks → Selector n K h)
    (i : Fin (n+1)) (a t : Fin d) (neq : a ≠ t) :
    ((singleVisits blocks (h*b) i a t).map fun q => crossCount b s select (.inr q) i).sum =
      (singleVisits blocks (h*b) i a t).length := by
  have fixed : (singleVisits blocks (h*b) i a t).map (fun q => crossCount b s select (.inr q) i) =
      (singleVisits blocks (h*b) i a t).map (fun _ => (1 : ℕ)) := by
    apply List.map_congr_left
    intro q hq
    obtain ⟨ha,ht⟩ := (mem_singleVisits _ _ _ _ _ q).mp hq
    simp [crossCount,ha,ht,neq]
  rw [fixed]
  simp

/-- The shared bit list after the selector prefix has exactly the declared cut width. -/
theorem commonCrossings_length (i : Fin (n+1)) (sym : Symbols d)
    (select : Packet n d blocks → Selector n K h)
    (z : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot n d blocks (h*b) → Bool) :
    (commonCrossings b i sym select z single).length =
      subtotals itemRow (crossCount b s select) i (Sym2.mk sym.val.1 sym.val.2) i := by
  rw [← strictVisits_subtotal b s select i i sym,single_ones select i _ _ sym.property.ne,
    single_ones select i _ _ sym.property.ne']
  simp only [commonCrossings,List.length_append,List.length_map,List.length_flatMap,
    crossingStream_length,crossCount]

/-- If the binary declaration passes, its actual reserved selector-plus-crossing
length is exactly the number of words produced in canonical order. -/
theorem strictShared_length (sym : Symbols d)
    (select : Packet n d blocks → Selector n K h)
    (z : (p : Packet n d blocks) → (e : Edge (n+1)) → Fin (payload (onEdge s) (select p).2 e) → Bool)
    (single : SingleSlot n d blocks (h*b) → Bool) (D : LengthDeclaration n d)
    (valid : passesLengths b s select D) :
    (commonSelectors select D.1 sym ++ commonCrossings b D.1 sym select z single).length =
      rowSelectorBits n d blocks K h D.1 (Sym2.mk sym.val.1 sym.val.2)+D.2 (Sym2.mk sym.val.1 sym.val.2) D.1 := by
  rw [List.length_append,commonSelectors_length,commonCrossings_length,valid.1]

end Cube.Scatter

end BorderVNP
end Computability
end OAI
