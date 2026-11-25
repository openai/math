import OAI.Hierarchy.TaggedWireTurnBoundaries
import OAI.Hierarchy.TaggedWireTurnMatrix

namespace OAI
/-! # The fixed local circuit on canonical visits of the original word walks -/
noncomputable section
namespace Hierarchy.WireTelescope.TurnShelf
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing Tagged
open scoped Classical BigOperators
variable {S n m r p e h : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
  (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
  (rank : Fin h≃Σi,Fin (route i).length)
  (walk : ∀i,Traverses (rowGraph edge) ((old i).1.1) (route i) ((old i).1.2))

abbrev Positions := Σi : Fin n,Fin ((route i).length+1)
variable (sp : ∀i,Spine (rowGraph edge) (old i).1.1 (route i) (old i).1.2)

/-- A physical itinerary has one original source row and a split immediately
before/after a hop. This includes initial/final positions and repeated visits. -/
abbrev At (s : Fin S) :=
  {q : Positions route // 0<bits q.1 ∧ (sp q.1).visit q.2=s}

def refAt (q : Positions route) (b : Bool) : TurnRef :=
  let pair := (sp q.1).sides (.inl false) (.inl true) 0 q.2
  if b then pair.2 else pair.1

/-- Each fixed word gate reads the two RAM endpoints of the same chronological
visit. Width zero makes unused public slots vacuous. No permutation of the
visits within the local party is required. -/
theorem chronological_matrix (F : Type*) [Field F] (s : Fin S)
    (x : State (installedWidths old bits) s) (y : State (installedWidths edge (routeLoad route bits)) s)
    (z : Fin r→RowData p e) (v : Aperture p e→Bool)
    (room : ∀t b,((z t).start b).val+(z t).live.val≤2^e)
    (seat : At old edge route bits sp s ↪ Fin r)
    (rows : ∀u,(z (seat u)).live.val=bits u.val.1)
    (empty : ∀t,t∉Set.range seat→(z t).live.val=0)
    (datum : ∀u b (j : Fin (bits u.val.1)),
      reads (z (seat u)) v b (j.cast (rows u).symm) (room (seat u) b)=
        readTurn (rowGraph edge) (rowGraph old) route bits (NativeSlot.allocation route bits rank)
          ⟨u.val.1,j⟩ s (rowBits old bits x,rowBits edge _ y) (refAt old edge route sp u.val b)) :
    TypedWiring.value (network F r p e) (pins z v)=chordRouter old edge route bits rank walk s x y := by
  rw [value F z v room]
  unfold chordRouter chordRouterWith bitMatrix
  congr 1
  apply propext
  refine Iff.trans ?_ (word_turns_iff (rowGraph edge) (rowGraph old) route bits
    (NativeSlot.allocation route bits rank) (NativeSlot.allocation_edge route bits rank)
    walk (fun j => (edge j).property.ne) s (rowBits old bits x) (rowBits edge _ y)).symm
  have hit (i : Fin n) (pair : TurnRef×TurnRef) :
      pair∈actualTurns (rowGraph edge) (rowGraph old) route i s ↔
        ∃j,(sp i).visit j=s ∧ (sp i).sides (.inl false) (.inl true) 0 j=pair := by
    have law := (sp i).in_wordTurns (.inl false) (.inl true) 0 s pair
    rw [(sp i).itinerary_eq (fun j=>(edge j).property.ne)] at law
    exact law
  constructor
  · intro all i t occurs j
    obtain ⟨pos,atSite,eq⟩:=(hit i t).mp occurs
    subst t
    let u : At old edge route bits sp s:=⟨⟨i,pos⟩,Nat.zero_lt_of_lt j.isLt,atSite⟩
    have layer:=all (seat u) (j.cast (rows u).symm)
    have compare:=((datum u false j).symm.trans layer).trans (datum u true j)
    exact compare
  · intro all t j
    by_cases h:t∈Set.range seat
    · obtain ⟨u,rfl⟩:=h
      let i:=u.val.1
      let pair:=(sp i).sides (.inl false) (.inl true) 0 u.val.2
      have mem:pair∈actualTurns (rowGraph edge) (rowGraph old) route i s:=
        (hit i pair).mpr ⟨u.val.2,u.property.2,rfl⟩
      let b := j.cast (rows u)
      have compare:=((datum u false b).trans (all i pair mem b)).trans (datum u true b).symm
      simpa [b] using compare
    · have zero:=empty t h
      exact False.elim (by have := j.isLt;omega)

end Hierarchy.WireTelescope.TurnShelf

end
end OAI
