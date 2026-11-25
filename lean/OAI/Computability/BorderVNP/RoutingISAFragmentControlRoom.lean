import OAI.Computability.BorderVNP.RoutingISAFragmentArena

/-! # Machine word bounds for the fragment writer's control table -/

namespace OAI
namespace Computability
namespace BorderVNP

set_option autoImplicit false

namespace RoutingISA.FragmentArena

/-- Each fragment control fits the machine word when the complete allocation
does. A positive cell count provides a reserved window of at least one stride. -/
theorem Layout.controls_fit (l : Layout) {w : ℕ} (old : ℕ → ℕ) (room : l.limit < 2^w)
    (cells : 0 < l.cells) (oldFit : ∀ j < 37, old j < 2^w) (j : ℕ) (hj : j < 37) :
    l.controls old j < 2^w := by
  have stride := Nat.le_mul_of_pos_left l.stride cells
  simp only [limit, counts, external, cursors, triples, pairs, quads] at room
  unfold controls
  split <;> first
    | exact oldFit j hj
    | omega
    | simp only [counts, external, cursors, triples, pairs, quads]
      omega

end RoutingISA.FragmentArena

end BorderVNP
end Computability
end OAI
