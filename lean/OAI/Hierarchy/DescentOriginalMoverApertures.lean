import OAI.Hierarchy.DescentResetSelectedMoverPrice
import OAI.Hierarchy.DescentOriginalRetainedSpace

namespace OAI
/-! # Word apertures of the selected chronological primitive mover -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentCompiler DescentSIMDLookup DescentSixParty DescentPlacedInvoiceVolume
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h e prev nextM C packet : ℕ)
    (prior : Prior) (base : ℕ)
local notation "V" => fromBoard G S board k tail age p f g drift degree h e prev (2^e) nextM C packet prior base
local notation "z" => (V).birth
local notation "q" => (V).primitive
local notation "M" => 2^e
local notation "H" => S.hostSize age
local notation "O" => S.groupCount age
local notation "growth" => 2^S.hostGain*S.radix
local notation "area" => receiptArea h H (chunks O M)


open DescentResetRetainedSetup DescentPackedWalsh
local notation "role" => (V).roleTransfer
local notation "L" => (role).transfer
local notation "c" => S.groupWidth k tail age
local notation "U" => (V).retainedRoleUnit
local notation "X" => 2^k

theorem original_role_lookup (priorNodes : prior.nodes≤S.retainedNodes) : (L).lookupUnit≤U:=by
  let v:=(L)
  let b:=v.bits
  let N:=S.retainedNodes
  let core:=(b*(2*N+1)+b)*X
  let sel:=b*X+X*Nat.clog 2 (X+1)
  have pitch:v.CalendarPitch c k h U:=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have nonzero:0<X:=Nat.two_pow_pos _
  have donors:v.donors=X:=(DescentResetRetainedSetup.Layout.CalendarPitch.geometry v pitch).2.1
  have width:U=max 1 (max core sel):=rfl
  change v.lookupUnit≤U
  rw [width]
  apply le_trans _ (Nat.le_max_right 1 _)
  apply max_le
  · apply le_trans _ (Nat.le_max_left core sel)
    have n:=priorNodes
    change b*prior.nodes≤(b*(2*N+1)+b)*X
    exact ((Nat.mul_le_mul_left b (n.trans (by dsimp [N];omega))).trans (Nat.le_add_right ..)).trans
      (Nat.le_mul_of_pos_right _ nonzero)
  · apply max_le
    · apply le_trans _ (Nat.le_max_left core sel)
      change b*X+b≤(b*(2*N+1)+b)*X
      have bh : b≤b*X:=Nat.le_mul_of_pos_right _ nonzero
      have mid : b*X≤(b*(2*N+1))*X:=Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ (Nat.succ_pos _))
      rw [Nat.add_mul]
      exact Nat.add_le_add mid bh
    · apply max_le
      · apply le_trans _ (Nat.le_max_left core sel)
        change (b*v.donors)*((2+7*0)*prior.nodes)+b*v.donors≤core
        rw [donors]
        have n:=Nat.mul_le_mul_left (b*X*2) priorNodes
        dsimp [core,N] at *
        nlinarith only [n,Nat.zero_le (b*X)]
      · apply le_trans _ (Nat.le_max_right core sel)
        change b*v.donors+v.donors*Nat.clog 2 (v.donors+1)≤ sel
        rw [donors]

theorem original_mover_apertures (priorNodes : prior.nodes≤S.retainedNodes)
    (old : (L).wholeWord*(L).previousLanes≤h/2) (oldPitch : (L).previousLanes≤h)
    (width : (c+k)*(c+k)≤h/2) (room : 8*(V).groupWidth≤h)
    (paid : ∀u,u∈(V).rootUnits ∨ u∈(V).receiverUnits→u*M≤h/2) : (role).pitches.Apertures h:=by
  have pitch:(L).CalendarPitch c k h U:=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have lookup:=(original_role_lookup G S board k tail age p f g drift degree h e prev nextM C packet prior base priorNodes)
  have budget:8*U≤h:=(Nat.mul_le_mul_left 8 ((V).groupWidth_fit (t:=U) (Or.inr (by simp [receiverUnits])))).trans room
  have up:0<U:=Nat.le_max_left 1 _
  have m:=pitch.movement_aperture up budget lookup old oldPitch width
  have args:=DescentResetRetainedSetup.Layout.CalendarPitch.words (L) pitch up budget lookup
  have ds:(L).donors=X:=(DescentResetRetainedSetup.Layout.CalendarPitch.geometry (L) pitch).2.1
  have xp:0<X:=Nat.two_pow_pos k
  have prec:=paid ((V).setup.packets.oldBits*((V).setup.packets.stage 0 true).fields) (Or.inl (by simp [rootUnits]))
  have panel:=paid (2^(V).middle.rootDepth*Nat.clog 2 (2^(V).middle.rootDepth+1)) (Or.inl (by simp [rootUnits]))
  change (X*Nat.clog 2 (X+1))*M≤h/2 at panel
  have digit:=paid ((L).bits*(V).sheets.blocks) (Or.inr (by simp [receiverUnits]))
  have one:0<Nat.clog 2 (X+1):=by
    by_contra! zero
    have eq_:Nat.clog 2 (X+1)=0:=Nat.eq_zero_of_le_zero zero
    have size:=Nat.le_pow_clog (by decide : 1<2) (X+1)
    rw [eq_,pow_zero] at size
    omega
  have mx:M*X≤h:=(by
    rw [Nat.mul_comm M X]
    exact ((Nat.mul_le_mul_right M (Nat.le_mul_of_pos_right X one)).trans panel).trans (Nat.div_le_self ..))
  have mp:M≤h:=(Nat.le_mul_of_pos_right _ xp).trans mx
  refine ⟨m,Nat.two_pow_pos e,mp,?_,?_,?_,args.2.2.2.2.1,?_,Nat.two_pow_pos _,xp,mx,
    args.2.2.2.2.2.1,digit⟩
  · change ((V).middle.rootField*DescentRotorWindowArchive.count _ (L).donors _)*M≤h/2
    rw [ds]
    exact prec
  · change (max (L).bits ((L).bits*(L).donors)+Nat.clog 2 ((L).donors+1)*(L).donors)*(L).decodedLanes≤_
    rw [max_eq_right (Nat.le_mul_of_pos_right _ (ds.symm ▸ xp)),Nat.mul_comm (Nat.clog 2 _)]
    exact args.2.2.2.2.2.2
  · change (Nat.clog 2 ((L).donors+1)*(L).donors)*M≤_
    rw [ds,Nat.mul_comm (Nat.clog 2 _)]
    exact panel
  · change 0<(L).decodedLanes
    rw [pitch.decoded,pitch.gather]
    exact Nat.two_pow_pos _

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

end OAI
