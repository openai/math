import OAI.Hierarchy.TaggedWireDormantRowBits
import OAI.Hierarchy.TaggedWireWidthRebase

namespace OAI
/-! # Physical routing only observes the two supported bit graphs -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph
open AdaptiveProbe
open scoped Classical
set_option quotPrecheck false
variable {F : Type*} [Field F] {K n r : ℕ} (route : Fin n→List (Fin r)) (bits : Fin n→ℕ)
    (alloc : Hop route bits ≃ Bundle (routeLoad route bits))
    (located : ∀h,(alloc h).1=hopEdge route bits h)
local notation "src" => BitRows K n bits
local notation "dst" => BitRows K r (routeLoad route bits)

private def onBitRows (A : src) (B : dst)
    (walk : ∀i,Nonempty (Spine B.2.1 (A.2.1.tail i) (placedRoute route bits alloc i) (A.2.1.head i))) :
    SiteMatrix (State A.1) (State B.1) F :=
  fun s x y=>bitMatrix B.2.1 A.2.1 (placedRoute route bits alloc) (fun i=>(walk i).some)
    F s (A.2.2 s x) (B.2.2 s y)

private theorem onBitRows_congr {A A' : src} {B B' : dst} (a : A=A') (b : B=B')
    (paths : ∀i,Nonempty (Spine B.2.1 (A.2.1.tail i) (placedRoute route bits alloc i) (A.2.1.head i)))
    (paths' : ∀i,Nonempty (Spine B'.2.1 (A'.2.1.tail i) (placedRoute route bits alloc i) (A'.2.1.head i))) :
    HEq (onBitRows (F:=F) route bits alloc A B paths) (onBitRows (F:=F) route bits alloc A' B' paths') := by
  cases a
  cases b
  rfl

private theorem with_supported {old old' : Fin n→Chord K} {edge edge' : Fin r→Chord K}
    (previous : ∀i,0<bits i → old i=old' i)
    (current : ∀i,0<routeLoad route bits i→edge i=edge' i)
    (path : ∀i,Traverses (rowGraph edge) (old i).1.1 (route i) (old i).1.2)
    (path' : ∀i,Traverses (rowGraph edge') (old' i).1.1 (route i) (old' i).1.2) :
    HEq (chordRouterWith (F:=F) old edge route bits alloc located path)
      (chordRouterWith (F:=F) old' edge' route bits alloc located path') := by
  let witness (before : Fin n→Chord K) (after : Fin r→Chord K)
      (walk : ∀i,Traverses (rowGraph after) (before i).1.1 (route i) (before i).1.2) :=
    fun i=>show Nonempty (Spine (bitGraph (rowGraph after) (routeLoad route bits))
      ((bitGraph (rowGraph before) bits).tail i) (placedRoute route bits alloc i)
      ((bitGraph (rowGraph before) bits).head i)) from
      ⟨placedSpine route bits alloc located (rowGraph after) (rowGraph before) walk i⟩
  exact onBitRows_congr (F:=F) route bits alloc
    (BitRows.data_congr old old' bits previous) (BitRows.data_congr edge edge' (routeLoad route bits) current)
    (witness old edge path) (witness old' edge' path')

/-- The exact occurrence directory is kept, including duplicate visits.
Every difference in either endpoint table is supported on rows of width zero. -/
theorem chordRouter_supported {old old' : Fin n→Chord K} {edge edge' : Fin r→Chord K}
    (previous : ∀i,0<bits i → old i=old' i) (current : ∀i,0<routeLoad route bits i→edge i=edge' i)
    {m : ℕ} (rank : Fin m≃Σi,Fin (route i).length)
    (path : ∀i,Traverses (rowGraph edge) (old i).1.1 (route i) (old i).1.2)
    (path' : ∀i,Traverses (rowGraph edge') (old' i).1.1 (route i) (old' i).1.2) :
    HEq (chordRouter (F:=F) old edge route bits rank path)
      (chordRouter (F:=F) old' edge' route bits rank path') :=
  with_supported route bits (NativeSlot.allocation route bits rank)
    (NativeSlot.allocation_edge route bits rank) previous current path path'

omit [Field F] in
theorem rebase_heq {A B U V : Widths K} (p : A=B) (q : U=V)
    (M : SiteMatrix (State A) (State U) F) : HEq (rebase p q M) M := by
  cases p
  cases q
  rfl

end Hierarchy.WireTelescope
end

end OAI
