import OAI.Hierarchy.TaggedWireChordRouter
import OAI.Hierarchy.TaggedWireSiteTurns

namespace OAI
/-! # The routed terminal equality array in the native weighted prefix order -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing
open scoped Classical BigOperators

variable {S n r rows : ℕ} (old : Fin n→Chord S) (edge : Fin r→Chord S)
    (route : Fin n→List (Fin r)) (bits : Fin n→ℕ) (ord : Fin rows≃Σi,Fin (route i).length)
    (walk : ∀i,Traverses (rowGraph edge) ((old i).1.1) (route i) ((old i).1.2))

def routerChecks (s : Fin S) :=
  siteTurns (bitGraph (rowGraph edge) (routeLoad route bits)) (bitGraph (rowGraph old) bits)
    (placedRoute route bits (NativeSlot.allocation route bits ord))
    (placedSpine route bits (NativeSlot.allocation route bits ord) (NativeSlot.allocation_edge route bits ord)
      (rowGraph edge) (rowGraph old) walk) s

def routerNetwork (F : Type*) [Zero F] [One F] (s : Fin S) :=
  Equality.listNetwork F (routerChecks old edge route bits ord walk s)

theorem routerNetwork_eval (F : Type*) [Field F] (s : Fin S)
    (v : State (installedWidths old bits) s) (z : State (installedWidths edge (routeLoad route bits)) s) :
    TypedWiring.value (routerNetwork old edge route bits ord walk F s)
      (Sum.elim (rowBits old bits v) (rowBits edge (routeLoad route bits) z)) =
      chordRouter (F:=F) old edge route bits ord walk s v z :=
  bitMatrixNetwork_eval _ _ _ _ F _ _ _

/-- The two physical ends read the same reported word via the weighted offset
of this traversal, even if the same route meets the same edge several times. -/
theorem routerNetwork_reported (F : Type*) [Field F] (s : Fin S)
    (v : State (installedWidths old bits) s) (data : ∀e,Fin (2^(routeLoad route bits e))) :
    TypedWiring.value (routerNetwork old edge route bits ord walk F s)
      (Sum.elim (rowBits old bits v) ((bitGraph (rowGraph edge) (routeLoad route bits)).atVertex
        (wordBitsEquiv (routeLoad route bits) data) s)) =
      chordRouter (F:=F) old edge route bits ord walk s v (readEdges edge _ data s) := by
  rw [←rowBits_readEdges edge (routeLoad route bits) data s]
  exact routerNetwork_eval ..

theorem routerNetwork_cells (F : Type*) [Field F] :
    (∑ s,((routerNetwork old edge route bits ord walk F s).cells+
      (routerNetwork old edge route bits ord walk F s).internal)) =
      ∑ i,bits i*((route i).length+1) := by
  have total := bitMatrixNetwork_size (bitGraph (rowGraph edge) (routeLoad route bits)) (bitGraph (rowGraph old) bits)
    (placedRoute route bits (NativeSlot.allocation route bits ord))
    (placedSpine route bits (NativeSlot.allocation route bits ord) (NativeSlot.allocation_edge route bits ord)
      (rowGraph edge) (rowGraph old) walk) F
  refine total.trans ?_
  simp only [Bundle,Fintype.sum_sigma,placedRoute,List.length_ofFn,Finset.sum_const,
    Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]

end Hierarchy.WireTelescope

end
end OAI
