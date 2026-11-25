import OAI.Hierarchy.TaggedWirePacketShiftedRows
import OAI.Hierarchy.TaggedWirePacketTurnMatrix

namespace OAI
/-! # Read the reached party's gathered chord directly at its original row's cumulative shift -/

noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open ThreeFlat Routing Tagged Computability.VPVNP.BurstRAM PrivateRAM
open TurnShelf
open scoped Classical

variable {S n m t count p e W : ℕ}
    (old : Fin n→Chord S) (edge : Fin m→Chord S) (route : Fin n→List (Fin m)) (bits : Fin n→ℕ)
    (rank : Fin t≃Σi,Fin (route i).length) (before : Fin n→Bool→ℕ) (after : Fin m→Bool→ℕ)
    (short : ∀i,(route i).length≤2) (order : Fin count≃Positions route)
    (walk : ∀i,Traverses (rowGraph edge) (old i).1.1 (route i) (old i).1.2)

variable (shift : Fin m→ℕ)
local notation "col" => shiftedFields old edge route bits rank shift before after short order
local notation "putAt" => put old edge route bits rank before after short order
local notation "mass" => routeLoad route bits

theorem shifted_matrix (F : Type*) [Field F] (s : Fin S) (base : ℕ) (mem : Memory W)
    (written : ∀f : Fin 5,∀a : Fin S×Fin (n*3),mem (addr base a.1 a.2 f)=ProtocolRAMTurnShelf.entry col putAt f a)
    (fit : ∀u : ProtocolRAMTurnShelf.Live col,∀f : Fin 5,col u.val (f.castLE (by decide))<2^W)
    (lo : ∀i b,before i b<2^p) (hi : ∀i b,after i b<2^p)
    (oldFit : ∀i,bits i≤2^e) (newFit : ∀i,shift i+mass i≤2^e)
    (x : State (installedWidths old bits) s) (y : State (installedWidths edge mass) s) (slab : Aperture p e→Bool)
    (prior : ∀i (j : Fin (bits i)) b (atSite : (rowGraph old).vertex i b=s),
      plane slab (before i b) j.val=rowBits old bits x (priorPort old bits i j b atSite))
    (paid : ∀i (j : Fin (bits i)) (q : Fin (route i).length) b
      (atSite : (rowGraph edge).vertex ((route i).get q) b=s),
      plane slab (after ((route i).get q) b) (shift ((route i).get q)+NativeSlot.start route bits rank i q+j.val)=
        rowBits edge mass y (paidPort edge route bits rank i j q b atSite)) :
    TypedWiring.value (TurnShelf.network F (n*3) p e) (nativeView base s mem slab)=
      chordRouter old edge route bits rank walk s x y := by
  let sp := fun i=>(Spine.exists_of_walk (walk i)).some
  have valid (u : ProtocolRAMTurnShelf.Live col) (b : Bool) :
      ValidRef old edge route (order u.val).1 (sp (order u.val).1 |>.visit (order u.val).2)
        (refAt old edge route sp (order u.val) b) := by
    have hh:=valid_pair old edge route _ (sp (order u.val).1) (order u.val).2
    cases b <;> first | exact hh.1 | exact hh.2
  have positive (u : ProtocolRAMTurnShelf.Live col) : 0<bits (order u.val).1 :=
    Nat.pos_of_ne_zero u.property
  apply scattered_matrix old edge route bits sp order col putAt
    (width_read old edge route bits rank before after short order)
    (field_site old edge route bits rank before after short order sp) F base mem rank walk written fit
    (s:=s) (x:=x) (y:=y) (slab:=slab)
  · intro u b
    rw [shifted_role_read old edge route bits rank shift before after short order sp]
    rcases key : refAt old edge route sp (order u.val) b with v|⟨q,v⟩
    · exact lo _ _
    · have ok:=valid u b
      rw [key] at ok
      obtain ⟨hq,_⟩:=ok
      simpa [refRole,hq] using hi (((route (order u.val).1).get ⟨q,hq⟩)) v
  · intro u b
    rw [shifted_start_read old edge route bits rank shift before after short order sp]
    change shiftedStart route bits rank shift (order u.val).1 (refAt old edge route sp (order u.val) b)+bits (order u.val).1≤_
    rcases key : refAt old edge route sp (order u.val) b with v|⟨q,v⟩
    · simpa [shiftedStart] using oldFit (order u.val).1
    · have ok:=valid u b;rw [key] at ok
      obtain ⟨hq,_⟩:=ok
      let j : Fin (route (order u.val).1).length:=⟨q,hq⟩
      have bound:=NativeSlot.start_room route bits rank _ j (positive u)
      have total:=newFit ((route (order u.val).1).get j)
      simpa only [shiftedStart,dite_eq_left hq,Nat.add_assoc] using
        (Nat.add_le_add_left bound (shift ((route (order u.val).1).get j))).trans total
  · intro u atSite b j d role off
    have eq : (sp (order u.val).1).visit (order u.val).2=s :=
      (field_site old edge route bits rank before after short order sp u).symm.trans atSite
    have use := valid u b
    rw [eq] at use
    have datum := shifted_read old edge route bits rank shift _ j s _ use (rowBits old bits x) (rowBits edge mass y)
        before after (plane slab) (prior _ j) (paid _ j)
    rw [shifted_role_read old edge route bits rank shift before after short order sp] at role
    rw [shifted_start_read old edge route bits rank shift before after short order sp] at off
    rw [←role,←off] at datum
    simpa [plane,d.1.isLt,d.2.isLt] using datum

end Hierarchy.WireTelescope.PacketTurns

end
end OAI
