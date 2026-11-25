import OAI.Hierarchy.TaggedWireHopBits

namespace OAI
/-! # The orientation of a native word route is independent of its bit index -/
noncomputable section
namespace Hierarchy.WireTelescope.Spine
open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators

variable {S : ℕ} {E T : Type} {G : PortGraph (Fin S) E} {a b : Fin S} {es : List E}

def signs : {a b : Fin S} → {es : List E} → Spine G a es b → List Bool
  | _,_,_,.nil _=>[]
  | _,_,_,.cons _ t tail=>t::signs tail

/-- A single comparison with the head determines which end is the departing
end of an edge. The construction reads each native edge once. -/
def follow (G : PortGraph (Fin S) E) : Fin S → List E → List Bool
  | _,[]=>[]
  | v,e::xs=>
    let t := decide (G.head e=v)
    t :: follow G (G.vertex e (!t)) xs

theorem signs_eq (sp : Spine G a es b) (diff : ∀ e,G.tail e≠G.head e) :
    signs sp=follow G a es := by
  induction sp with
  | nil v=>rfl
  | cons e t tail ih=>
    cases t <;> simp [signs,follow,PortGraph.vertex,Ne.symm (diff e)] at * <;> exact ih

theorem follow_map (G : PortGraph (Fin S) E) (C : PortGraph (Fin S) T) (row : T→E)
    (lo : ∀e,C.tail e=G.tail (row e)) (hi : ∀e,C.head e=G.head (row e))
    (a : Fin S) (xs : List T) : follow C a xs=follow G a (xs.map row) := by
  induction xs generalizing a with
  | nil=>rfl
  | cons i rest ih=>
    have side (t : Bool) : C.vertex i t=G.vertex (row i) t := by cases t <;> simp [PortGraph.vertex,lo,hi]
    simp only [List.map_cons,follow,hi,side,ih]

end Hierarchy.WireTelescope.Spine

namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open scoped Classical BigOperators

variable {S n m : ℕ} (G : PortGraph (Fin S) (Fin m)) (C : PortGraph (Fin S) (Fin n))
    (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
    (a : Hop route bits≃Bundle (routeLoad route bits)) (located : ∀q,(a q).1=hopEdge route bits q)
    (path : ∀i,Traverses G (C.tail i) (route i) (C.head i))

/-- All bit-indexed spines of a single word follow the one genuine physical
word-level itinerary. This includes the repeated occurrences of any link. -/
theorem placedSpine_word (diff : ∀i,G.tail i≠G.head i) (q : Bundle bits) :
    (placedSpine route bits a located G C path q).signs=
      Spine.follow G (C.tail q.1) (route q.1) := by
  rw [Spine.signs_eq _ (fun i=>diff i.1)]
  change Spine.follow (bitGraph G _) (C.tail q.1) (placedRoute route bits a q)=_
  rw [Spine.follow_map G (bitGraph G _) Sigma.fst (fun _=>rfl) (fun _=>rfl),
    placedRoute_edges route bits a located]

end Hierarchy.WireTelescope

end
end OAI
