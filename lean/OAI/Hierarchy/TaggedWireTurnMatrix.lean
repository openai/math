import OAI.Hierarchy.TaggedWireTurnShelf
import OAI.Hierarchy.TaggedWireWordTurns
import OAI.Hierarchy.TaggedWireChordRouter

namespace OAI
/-! # Native populated turn slots give the terminal equality matrix -/
noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing Tagged
open scoped Classical BigOperators

namespace TurnShelf
variable {S n m r p e h : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
  (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
  (rank : Fin h≃Σi,Fin (route i).length)
  (walk : ∀i,Traverses (rowGraph edge) ((old i).1.1) (route i) ((old i).1.2))

abbrev Pending (s : Fin S) := Σ i : Fin n,Fin (actualTurns (rowGraph edge) (rowGraph old) route i s).length
abbrev Live (s : Fin S) := {v : Pending old edge route s // 0<bits v.1}

def hand (s : Fin S) (t : Pending old edge route s) (side : Bool) : TurnRef :=
  let lr := (actualTurns (rowGraph edge) (rowGraph old) route t.1 s).get t.2
  if side then lr.2 else lr.1

/-- An elementary readback interface: a true live width, a zero width at each
unused seat, and the two individual bits read at the emitted addresses.
The network and its table sizes are independent of this instance. -/
theorem route_matrix (F : Type*) [Field F] (s : Fin S)
    (x : State (installedWidths old bits) s) (y : State (installedWidths edge (routeLoad route bits)) s)
    (z : Fin r→RowData p e) (v : Aperture p e→Bool)
    (room : ∀t b,((z t).start b).val+(z t).live.val≤2^e)
    (seat : Live old edge route bits s ↪ Fin r)
    (rows : ∀u,(z (seat u)).live.val=bits u.val.1)
    (empty : ∀t,t∉Set.range seat→(z t).live.val=0)
    (datum : ∀u b (j : Fin (bits u.val.1)),
      reads (z (seat u)) v b (j.cast (rows u).symm) (room (seat u) b)=
        readTurn (rowGraph edge) (rowGraph old) route bits (NativeSlot.allocation route bits rank)
          ⟨u.val.1,j⟩ s (rowBits old bits x,rowBits edge _ y) (hand old edge route s u.val b)) :
    TypedWiring.value (network F r p e) (pins z v)=chordRouter old edge route bits rank walk s x y := by
  rw [value F z v room]
  unfold chordRouter chordRouterWith bitMatrix
  congr 1
  apply propext
  refine Iff.trans ?_ (word_turns_iff (rowGraph edge) (rowGraph old) route bits
    (NativeSlot.allocation route bits rank) (NativeSlot.allocation_edge route bits rank)
    walk (fun j => (edge j).property.ne) s (rowBits old bits x) (rowBits edge _ y)).symm
  constructor
  · intro all i turn present j
    obtain ⟨index,loc⟩:=List.mem_iff_get.mp present
    subst turn
    let u : Live old edge route bits s:=⟨⟨i,index⟩,Nat.zero_lt_of_lt j.isLt⟩
    have eq := ((datum u false j).symm.trans (all (seat u) (j.cast (rows u).symm))).trans (datum u true j)
    exact eq
  · intro all t j
    by_cases used : t∈Set.range seat
    · obtain ⟨u,rfl⟩:=used
      let i := j.cast (rows u)
      have eq := all u.val.1 _ (List.get_mem _ u.val.2) i
      have left := datum u false i
      have right := datum u true i
      simpa [i,hand] using (left.trans eq).trans right.symm
    · have none:=empty t used
      have lt:=j.isLt
      omega

end TurnShelf
end Hierarchy.WireTelescope

end
end OAI
