import OAI.Hierarchy.TaggedWirePacketShiftedMatrix
import OAI.Hierarchy.TaggedWirePacketGatheredBit
import OAI.Hierarchy.TaggedWirePacketLocalGate

namespace OAI
/-! # The selected packet installation on the old bits and the native gathered chord shelf -/
noncomputable section
open scoped Fin.CommRing
set_option quotPrecheck false
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat Diagonal.MotifOuterTerms Routing Tagged AdaptiveProbe TurnShelf CalendarTape
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical BigOperators

variable {F V : Type} [Field F] [Fintype V] {S N H copies D K count p e W : ℕ}
    {row : Row F S H copies} {phys : Fin N→Chord S}

/-- Immutable pin map for the aggregate neighbor words at this party.
All rewriting of physical row IDs and all shifts happen on public words. -/
def neighborPin (oldRoles : ℕ) (zero : V) (post : Fin D×Fin K→V) (d : Aperture p e) : V :=
  if q : d.1.val-oldRoles*2<D then if j:d.2.val<K then post (⟨_,q⟩,⟨_,j⟩) else zero else zero

variable (R : RowRouting row phys) (c : Histogram (Fin H) copies) (s : Fin S)
local notation "roles" => Fintype.card R.Roles
local notation "old" => Installs.starts (source:=R.source) R.order
local notation "run" => R.install.steps R.order
local notation "w" => Installs.numbered R.order (R.bits c)
local notation "mass" => routeLoad run w
local notation "shift" => AggregatePrefix.paidShift run w R.ordinal phys
local notation "win" => (Installs.packed (source:=R.source) R.order (R.bits c)).trans (R.shape c)
local notation "wout" => congrArg (installedWidths phys) (R.install.counted R.order (R.bits c))
local notation "before" => fun (i : Fin roles) (b : Bool)=>(halfCode i b).val
variable {total : (portGraph S).Port s→ℕ} (parts : PassiveWindow.Parts ((portGraph S).Port s) (Fin D) K total)
local notation "after" => fun (i : Fin N) (b : Bool)=>roles*2+PacketNeighbor.index parts ((rowGraph phys).vertex i (!b))

theorem gathered_gate (short : ∀i,(run i).length≤2) (turns : Fin count≃Positions run)
    (ctl : Fin (roles*3)×Control p e→V) (post : Fin D×Fin K→V) (zero : V) (v : V→Bool)
    (out : State (R.post c) s) (state : (portGraph S).Port s→ℕ→Bool) (cap : ∀p,total p≤K)
    (roleRoom : roles*2+D<2^p) (oldFit : ∀i,w i≤2^e) (chordFit : ∀i,installedWidths phys mass (phys i)≤2^e)
    (width : ∀p : (portGraph S).Port s,installedWidths phys mass p.val.1≤total p)
    (active : ∀p : (portGraph S).Port s,∀j : Fin (installedWidths phys mass p.val.1),state p j.val=(out p).val.testBit j.val)
    (publicRead : let cols:=PacketTurns.shiftedFields old phys run w R.ordinal shift before after short turns
      let put:=PacketTurns.put old phys run w R.ordinal before after short turns
      ∀t f,v (ctl (t,f))=(ProtocolRAMTurnShelf.entry (W:=W) cols put (projection f).1 (s,t)).val.testBit (projection f).2)
    (external : ∀q j,v (post (q,j))=ChordAperture.canonical parts state q j) (pad : v zero=false)
    (fit : let cols:=PacketTurns.shiftedFields old phys run w R.ordinal shift before after short turns
      ∀u : ProtocolRAMTurnShelf.Live cols,∀f : Fin 5,cols u.val (f.castLE (by decide))<2^W) :
    ∀y,TypedWiring.value (installNet F ctl (packetData roles (2^e) (neighborPin roles zero post)))
      (Sum.elim v (packedMiddle c s (middlePlace R c s (2^e) oldFit) y))=
      Installs.transport (R.shape c) rfl (R.install.operator R.order (R.bits c) R.ordinal) s y out := by
  intro y
  let cols:=PacketTurns.shiftedFields old phys run w R.ordinal shift before after short turns
  let put:=PacketTurns.put old phys run w R.ordinal before after short turns
  let cell:=ProtocolRAMTurnShelf.entry (W:=W) cols put
  let mem:=headerView cell
  let mid:=packedMiddle c s (middlePlace R c s (2^e) oldFit) y
  let data : Aperture p e → V ⊕ Fin (middleRoom roles (2^e)) :=
    packetData roles (2^e) (neighborPin roles zero post)
  let slab := (Sum.elim v mid) ∘ data
  have pinRead : (Sum.elim (Sum.elim v mid) id ∘
      Sum.elim (fun k=>Sum.inl (Sum.inl (ctl k))) (fun d=>Sum.inl (data d)))=nativeView 0 s mem slab := by
    funext a
    rcases a with ⟨t,f⟩|d
    · change v (ctl (t,f))=(headerView cell (addr 0 s t (projection f).1)).val.testBit _
      rw [header_at];exact publicRead t f
    · rfl
  change TypedWiring.value (installNet F ctl data) (Sum.elim v mid)=_
  rw [installNet,RadixStage.pullPins_value,pinRead]
  have lo (i : Fin roles) (b : Bool) : before i b<2^p :=
    (halfCode i b).isLt.trans_le ((Nat.le_add_right _ _).trans roleRoom.le)
  have hi (i : Fin N) (b : Bool) : after i b<2^p :=
    (Nat.add_le_add_left (PacketNeighbor.index_le parts _) (roles*2)).trans_lt roleRoom
  have fits (i : Fin N) : shift i+mass i≤2^e := (AggregatePrefix.shift_room run w R.ordinal phys i).trans (chordFit i)
  let x:=cast (congrArg (fun U=>State U s) (win).symm) y
  let z:=cast (congrArg (fun U=>State U s) (wout).symm) out
  have receipt:=PacketTurns.shifted_matrix old phys run w R.ordinal before after short turns
    (fun i=>R.install.path (R.order i)) shift F s 0 mem (fun f v=>header_at cell _ _ _) fit lo hi oldFit fits x z slab
  refine (receipt ?_ ?_).trans ?_
  · intro i j b here
    let a : Aperture p e := (⟨before i b,lo i b⟩,⟨j.val,j.isLt.trans_le (oldFit _)⟩)
    have wired:=packetData_old R c s _ oldFit (neighborPin roles zero post) i j b here a rfl rfl
    rw [NamedAperture.rowBits_transport old w win y]
    change PacketTurns.plane slab (before i b) j.val=_
    simp [PacketTurns.plane,lo i b,j.isLt.trans_le (oldFit i),slab,Function.comp_def,data,mid,a,wired,middle_at]
  · intro i j q b here
    let key:=(run i).get q
    let rep:=PacketNeighbor.index parts ((rowGraph phys).vertex key (!b))
    let digit:=shift key+NativeSlot.start run w R.ordinal i q+j.val
    have oldRoom:=NativeSlot.start_room run w R.ordinal i q (Nat.zero_lt_of_lt j.isLt)
    have room : digit<2^e := by
      have used := (Nat.add_lt_add_left j.isLt _).trans_le oldRoom
      exact (Nat.add_assoc ..).trans_lt ((Nat.add_lt_add_left used (shift key)).trans_le (fits key))
    have actual (p : (portGraph S).Port s) (j : Fin (installedWidths phys mass p.val.1)) :
        state p j.val=(z p).val.testBit j.val := by
      rw [active p j]
      exact congrArg (fun a : ℕ=>a.testBit j.val) (PacketNeighbor.state_cast_val (wout).symm s out p).symm
    have native:=PacketNeighbor.paid_bit phys run w R.ordinal s parts cap state z width actual i j q b here
    change PacketTurns.plane slab (roles*2+rep) digit=_
    have addrFit : roles*2+rep<2^p := hi key b
    have val : PacketTurns.plane slab (roles*2+rep) digit=PacketNeighbor.bank parts state rep digit := by
      simp only [PacketTurns.plane,dite_eq_left addrFit,dite_eq_left room,slab,Function.comp_apply,data]
      let a : Aperture p e := (⟨roles*2+rep,addrFit⟩,⟨digit,room⟩)
      change Sum.elim v mid (packetData roles (2^e) (neighborPin roles zero post) a)=_
      have upper : roles*2≤a.1.val := Nat.le_add_right _ _
      rw [packetData_new (cap:=2^e) (neighborPin roles zero post) a upper]
      dsimp only [a]
      simp only [Sum.elim_inl,neighborPin,Nat.add_sub_cancel_left,PacketNeighbor.bank]
      by_cases qfit:rep<D <;> by_cases jfit:digit<K <;> simp [qfit,jfit,pad,external]
    exact val.trans native
  · have joined {U U' U'' T T' : Widths S} (first : U=U') (last : U'=U'') (postEq : T=T')
        (M : SiteMatrix (State U) (State T) F) (a : State U'' s) (b : State T' s) :
        M s (cast (congrArg (fun q=>State q s) (first.trans last).symm) a)
          (cast (congrArg (fun q=>State q s) postEq.symm) b) =
        Installs.transport last rfl (Installs.transport first postEq M) s a b := by
      cases first
      cases last
      cases postEq
      rfl
    unfold Installs.operator
    exact joined (Installs.packed (source:=R.source) R.order (R.bits c)) (R.shape c) wout _ y out

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
