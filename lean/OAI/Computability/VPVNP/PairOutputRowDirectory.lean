import OAI.Computability.VPVNP.PairVertexLevelBounds

/-!
# Decoding the output rows of a traversal

The leaf layer precedes the selected output layers. A popped word identifies
an output row precisely when it is the header of a site of one of these
layers. Empty layers contribute no candidates to the finite directory.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.OutputRowDirectory

open BurstRAM TraversalRoles TraversalRows VertexLevelBounds
open scoped Fin.CommRing

variable {w : ℕ}

/-- An output row identified by a tagged output layer and a site ordinal bounded by that
layer’s count. The traversal uses the pair to recover the absolute descriptor address. -/
abbrev Row (outputs : List TaggedLayer) :=
  Σ j : Fin outputs.length, Fin outputs[j].layer.count

variable (cap base : ℕ) (leaf : TaggedLayer) (outputs : List TaggedLayer)

/-- The site number is relative to its output layer. Layer zero of the
physical layout holds the leaves. -/
def rowAddress (row : Row outputs) : ℕ :=
  address cap (layerBase cap base (leaf :: outputs) (row.1.val + 1)) row.2.val

theorem rowAddress_injective : Function.Injective (rowAddress cap base leaf outputs) := by
  rintro ⟨j, x⟩ ⟨k, y⟩ eqn
  let start := endPos cap base leaf.layer
  change address cap (layerBase cap base (leaf :: outputs) (j.val + 1)) x.val =
    address cap (layerBase cap base (leaf :: outputs) (k.val + 1)) y.val at eqn
  rw [layerBase_cons, layerBase_cons] at eqn
  obtain ⟨lo, _, _, later, _⟩ := node_interval cap start outputs j x
  obtain ⟨lo', _, _, later', _⟩ := node_interval cap start outputs k y
  have same : j = k := by
    apply Fin.ext
    rcases lt_trichotomy j.val k.val with h | h | h
    · exact False.elim ((later k.val h).not_ge (eqn.symm ▸ lo'))
    · exact h
    · exact False.elim ((later' j.val h).not_ge (eqn ▸ lo))
  subst k
  have sameSite : x = y :=
    Fin.ext (Nat.eq_of_mul_eq_mul_left (by omega : 0 < cap + 2) (Nat.add_left_cancel eqn))
  cases sameSite
  rfl

theorem rowAddress_lt_end (row : Row outputs) :
    rowAddress cap base leaf outputs row <
      layerBase cap base (leaf :: outputs) (outputs.length + 1) := by
  rw [rowAddress, layerBase_cons, layerBase_cons]
  exact (node_interval cap (endPos cap base leaf.layer) outputs row.1 row.2).2.1.trans_le
    (layerBase_mono cap (endPos cap base leaf.layer) outputs row.1.isLt)

private def rows (outputs : List TaggedLayer) : List (Row outputs) :=
  (List.finRange outputs.length).flatMap fun j =>
    (List.finRange outputs[j].layer.count).map (Sigma.mk j)

private theorem mem_rows (row : Row outputs) : row ∈ rows outputs :=
  List.mem_flatMap.mpr ⟨row.1, List.mem_finRange _,
    List.mem_map.mpr ⟨row.2, List.mem_finRange _, rfl⟩⟩

/-- Search the fixed row headers in level and site order using machine-word equality. -/
def decode (node : Word w) : Option (Row outputs) :=
  (rows outputs).find? fun row => decide (node = (rowAddress cap base leaf outputs row : Word w))

variable (fit : layerBase cap base (leaf :: outputs) (outputs.length + 1) ≤ 2 ^ w)

include fit

/-- Each valid output header selects its unique level and site. -/
theorem decode_eq_some_iff (node : Word w) (row : Row outputs) :
    decode cap base leaf outputs node = some row ↔
      node.val = rowAddress cap base leaf outputs row := by
  have match_word (x : Row outputs) :
      node = (rowAddress cap base leaf outputs x : Word w) ↔
        node.val = rowAddress cap base leaf outputs x := by
    rw [Fin.ext_iff, Fin.val_natCast,
      Nat.mod_eq_of_lt ((rowAddress_lt_end cap base leaf outputs x).trans_le fit)]
  constructor
  · intro found
    unfold decode at found
    have hit := List.find?_some found
    exact (match_word row).mp (of_decide_eq_true hit)
  · intro addr
    unfold decode
    cases found : (rows outputs).find?
        (fun x => decide (node = (rowAddress cap base leaf outputs x : Word w))) with
    | none =>
      exact False.elim ((List.find?_eq_none.mp found row (mem_rows outputs row))
        (decide_eq_true ((match_word row).mpr addr)))
    | some x =>
      have hit := List.find?_some found
      have hx := (match_word x).mp (of_decide_eq_true hit)
      exact congrArg some (rowAddress_injective cap base leaf outputs (hx.symm.trans addr))

/-- Words in the leaf region, row interiors, or beyond the directory have no output row. -/
theorem decode_eq_none_iff (node : Word w) :
    decode cap base leaf outputs node = none ↔
      ∀ row, node.val ≠ rowAddress cap base leaf outputs row := by
  constructor
  · intro noneFound row addr
    have found := (decode_eq_some_iff cap base leaf outputs fit node row).mpr addr
    simp [noneFound] at found
  · intro miss
    cases found : decode cap base leaf outputs node with
    | none => rfl
    | some row =>
      exact False.elim (miss row ((decode_eq_some_iff cap base leaf outputs fit node row).mp found))

end PairSimulation.OutputRowDirectory

end VPVNP
end Computability
end OAI
