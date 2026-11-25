import OAI.Hierarchy.DescentRetainedSevenBits
import OAI.Hierarchy.DescentOriginalRetainedSpace

namespace OAI
/-! # Word apertures of the selected chronological seven-field operand transfer -/
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
local notation "role" => (V).setup.seven
local notation "L" => (role).retained
local notation "c" => S.groupWidth k tail age
local notation "U" => (V).retainedUnit
local notation "X" => 2^k

theorem original_seven_apertures (priorNodes : prior.nodes≤S.retainedNodes)
    (priorArgs : prior.arguments≤S.retainedArgumentsAt G drift) (baseGroups : S.baseGroups=2^tail)
    (radix : S.radix=2^k) (live : age<S.length)
    (old : (L).wholeWord*(L).previousLanes≤h/2) (oldPitch : (L).previousLanes≤h)
    (width : (c+k)*(c+k)≤h/2) (room : 8*(V).groupWidth≤h)
    (paid : ∀u,u∈(V).rootUnits ∨ u∈(V).receiverUnits→u*M≤h/2) : (role).Apertures h:=by
  have pitch:(L).CalendarPitch c k h U:=⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩
  have all:=S.previousWidth G k tail drift degree p age h prior.nodes prior.arguments prior.operandLanes
    priorNodes priorArgs baseGroups radix live
  have sel:=S.selector_width G k tail drift degree p age h prior.nodes prior.arguments prior.operandLanes baseGroups radix live
  have lookup:(L).lookupUnit≤U:=max_le all.1 (max_le ((Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..)))
    (max_le all.2 sel))
  have budget:8*U≤h:=(Nat.mul_le_mul_left 8 ((V).groupWidth_fit (t:=U) (Or.inr (by simp [receiverUnits])))).trans room
  have up:0<U:=Nat.le_max_left 1 _
  have m:=pitch.movement_aperture up budget lookup old oldPitch width
  have args:=DescentResetRetainedSetup.Layout.CalendarPitch.words (L) pitch up budget lookup
  have ds:(L).donors=X:=(DescentResetRetainedSetup.Layout.CalendarPitch.geometry (L) pitch).2.1
  have xp:0<X:=Nat.two_pow_pos k
  have prec:=paid ((V).setup.packets.oldBits*((V).setup.packets.stage 0 true).fields) (Or.inl (by simp [rootUnits]))
  have panel:=paid (2^(V).middle.rootDepth*Nat.clog 2 (2^(V).middle.rootDepth+1)) (Or.inl (by simp [rootUnits]))
  change (X*Nat.clog 2 (X+1))*M≤h/2 at panel
  have digit:=paid ((V).setup.retainedFields.bits*(V).sheets.blocks) (Or.inr (by simp [receiverUnits]))
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
