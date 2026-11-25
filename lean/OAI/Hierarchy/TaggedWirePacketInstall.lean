import OAI.Hierarchy.TaggedWirePacketMiddle
import OAI.Hierarchy.TaggedWirePacketTurnMatrix
import OAI.Hierarchy.TaggedWidePacketHidden
import OAI.Hierarchy.TaggedWireTransportAt
import OAI.Hierarchy.TaggedShorterPullCost

namespace OAI
/-! # A fixed packet install circuit on the hidden intermediate port states -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Routing Diagonal.MotifOuterTerms Tagged AdaptiveProbe
open Computability.VPVNP.BurstRAM PrivateRAM TurnShelf CalendarTape
open scoped Classical

variable {V F : Type} [Fintype V] [Field F] {S N H copies middle p e W count : ℕ}

/-- The pin map is fixed by the public circuit. Dynamic widths, port IDs,
and starts arrive exclusively through the five CPU header columns. -/
def installNet (F : Type) [Field F] {slots : ℕ} (ctl : Fin slots×Control p e→V)
    (data : Aperture p e→V⊕Fin middle) :=
  RadixStage.pullPins (TurnShelf.network F slots p e)
    (Sum.elim (fun k=>Sum.inl (Sum.inl (ctl k))) (fun d=>Sum.inl (data d)))

theorem installNet_size {slots : ℕ} (ctl : Fin slots×Control p e→V) (data : Aperture p e→V⊕Fin middle) :
    (installNet F ctl data).cells+(installNet F ctl data).internal=
      (TurnShelf.network F slots p e).cells+(TurnShelf.network F slots p e).internal := by simp [installNet, RadixStage.pullPins, BitNetwork.glue_cells, BitNetwork.glue_internal]

variable {row : Row F S H copies} {phys : Fin N→Chord S} (R : RowRouting row phys)
    (c : Histogram (Fin H) copies) (s : Fin S)
local notation "old" => Installs.starts (source:=R.source) R.order
local notation "run" => R.install.steps R.order
local notation "w" => Installs.numbered R.order (R.bits c)
local notation "mass" => routeLoad run w
local notation "win" => (Installs.packed (source:=R.source) R.order (R.bits c)).trans (R.shape c)
local notation "wout" => congrArg (installedWidths phys) (R.install.counted R.order (R.bits c))

omit [Field F] in
theorem transport_at {U U' V V' : Widths S} (a : U=U') (b : V=V')
    (M : SiteMatrix (State U) (State V) F) (x : State U' s) (y : State V' s) :
    Installs.transport a b M s x y=M s (cast (congrArg (fun t=>State t s) a.symm) x)
      (cast (congrArg (fun t=>State t s) b.symm) y) := by subst U';subst V';rfl

omit [Field F] in
private theorem composed_transport {X X' X'' Y Y' : Widths S} (left : X=X') (next : X'=X'')
    (right : Y=Y') (M : SiteMatrix (State X) (State Y) F) (x : State X'' s) (y : State Y' s) :
    M s (cast (congrArg (fun t => State t s) (left.trans next).symm) x)
      (cast (congrArg (fun t => State t s) right.symm) y) =
        Installs.transport next rfl (Installs.transport left right M) s x y := by
  cases left
  cases next
  cases right
  rfl

/-- The hypothesis expected by the hidden-state sum. The two private-wire
conditions are literal coordinate equalities. On the old side, the pin is
the chosen physical padding location of an intermediate bit; on the new
side it is the exposed bit of the outgoing party state. -/
theorem installed_eval
    (short : ∀i,(run i).length≤2) (order : Fin count≃Positions run)
    (before : Fin (Fintype.card R.Roles)→Bool→ℕ) (after : Fin N→Bool→ℕ)
    (ctl : Fin (Fintype.card R.Roles*3)×Control p e→V) (data : Aperture p e→V⊕Fin middle)
    (place : SiteBit (row.output c) s ↪ Fin middle) (postPin : SiteBit (R.post c) s→V)
    (v : V→Bool) (out : State (R.post c) s) (base : ℕ) (mem : Memory W)
    (controlRead : ∀t f,v (ctl (t,f))=(mem (addr base s t (projection f).1)).val.testBit (projection f).2)
    (postRead : ∀a,v (postPin a)=siteBits (R.post c) s out a)
    (written : let cols := PacketTurns.fields old phys run w R.ordinal before after short order
      let put := PacketTurns.put old phys run w R.ordinal before after short order
      ∀f : Fin 5,∀a,mem (addr base a.1 a.2 f)=ProtocolRAMTurnShelf.entry cols put f a)
    (fit : let cols := PacketTurns.fields old phys run w R.ordinal before after short order
      ∀u : ProtocolRAMTurnShelf.Live cols,∀f : Fin 5,cols u.val (f.castLE (by decide))<2^W)
    (lo : ∀i b,before i b<2^p) (hi : ∀i b,after i b<2^p)
    (oldFit : ∀i,w i≤2^e) (newFit : ∀i,mass i≤2^e)
    (oldWire : ∀i (j : Fin (w i)) b (here : (rowGraph old).vertex i b=s) (d : Aperture p e),
      d.1.val=before i b → d.2.val=j.val →
      data d=.inr (place (NamedAperture.transportAt win (NamedAperture.atPort old w (PacketTurns.priorPort old w i j b here)))))
    (newWire : ∀i (j : Fin (w i)) (q : Fin (run i).length) b (here : (rowGraph phys).vertex ((run i).get q) b=s)
      (d : Aperture p e),d.1.val=after ((run i).get q) b → d.2.val=NativeSlot.start run w R.ordinal i q+j.val →
      data d=.inl (postPin (NamedAperture.transportAt wout (NamedAperture.atPort phys mass
        (PacketTurns.paidPort phys run w R.ordinal i j q b here))))) :
    ∀ y,TypedWiring.value (installNet F ctl data) (Sum.elim v (packedMiddle c s place y))=
      Installs.transport (R.shape c) rfl (R.install.operator R.order (R.bits c) R.ordinal) s y out := by
  intro y
  let slab : Aperture p e→Bool := (Sum.elim v (packedMiddle c s place y)) ∘ data
  have pinRead : (Sum.elim (Sum.elim v (packedMiddle c s place y)) id ∘
      Sum.elim (fun k=>Sum.inl (Sum.inl (ctl k))) (fun d=>Sum.inl (data d)))=nativeView base s mem slab := by
    funext q
    rcases q with ⟨t,f⟩|d
    · exact controlRead t f
    · rfl
  rw [installNet,RadixStage.pullPins_value,pinRead]
  have receipt := PacketTurns.matrix old phys run w R.ordinal before after short order (fun i=>R.install.path (R.order i))
    F s base mem written fit lo hi oldFit newFit
    (cast (congrArg (fun U=>State U s) (win).symm) y) (cast (congrArg (fun U=>State U s) (wout).symm) out) slab
  refine (receipt ?_ ?_).trans ?_
  · intro i j b here
    let a : Aperture p e := (⟨before i b,lo i b⟩,⟨j.val,j.isLt.trans_le (oldFit i)⟩)
    have wire := oldWire i j b here a rfl rfl
    rw [NamedAperture.rowBits_transport old w win y]
    simp [PacketTurns.plane,lo i b,j.isLt.trans_le (oldFit i),slab,Function.comp_def,a,wire,middle_at]
  · intro i j q b here
    have room := NativeSlot.start_room run w R.ordinal i q (Nat.zero_lt_of_lt j.isLt)
    have bound : NativeSlot.start run w R.ordinal i q+j.val<2^e :=
      (Nat.add_lt_add_left j.isLt _).trans_le (room.trans (newFit _))
    let a : Aperture p e := (⟨after ((run i).get q) b,hi _ b⟩,⟨_,bound⟩)
    have wire := newWire i j q b here a rfl rfl
    rw [NamedAperture.rowBits_transport phys mass wout out]
    unfold PacketTurns.plane
    rw [dite_eq_left (hi _ b), dite_eq_left bound]
    change Sum.elim v (packedMiddle c s place y) (data a) = _
    rw [wire]
    exact postRead _

  · unfold Installs.operator
    exact composed_transport s (Installs.packed (source:=R.source) R.order (R.bits c)) (R.shape c) wout _ y out

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
