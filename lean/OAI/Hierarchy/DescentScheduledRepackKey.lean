import OAI.Hierarchy.DescentScheduledResetChart
import OAI.Hierarchy.DescentMeasuredLaneRoom
import OAI.Hierarchy.DescentTerminalChartScale

namespace OAI
/-! # The repacking dictionary at the measured Walsh and receiver pitches -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentCompiler.TerminalScale DescentPackedWalsh ProtocolRAM Filter
open DescentPacking.PackedMatch.Local.Stage
noncomputable section

theorem repack_dictionary {b k m h e : ℕ} (hb : 0<b) (short : 8*b≤h)
    (cube : k≤laneBits m h b) (receiver : e≤laneBits m h b-k) :
    let l:=laneBits m h b
    (l-k-e)+(b*2^k)*(2^(l-k-e)*2^e)≤h/2:=by
  intro l
  have sum : k+(l-k-e)+e=l:=by dsimp [l] at *;omega
  have dictionaryFields : (b*2^k)*(2^(l-k-e)*2^e)=b*2^l:=by
    calc _=b*(2^k*2^(l-k-e)*2^e):=by ring
         _=b*2^l:=by rw [←pow_add,←pow_add,sum]
  have index : l-k-e≤b*2^l:=
    ((Nat.sub_le ..).trans (Nat.sub_le ..)).trans
      ((Nat.lt_two_pow_self (n:=l)).le.trans (Nat.le_mul_of_pos_left _ hb))
  have total:=keys_fit (m:=m) hb short
  change 1+(b+b)*2^l≤h/2 at total
  rw [Nat.add_mul] at total
  rw [dictionaryFields]
  omega

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (previous nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (addr : ℕ→ℕ→Bank) (roster : Bank)
local notation "dim" => S.groupWidth k tail age+k
local notation "price" => S.localWalshBits p dim f (quota S.rounds)
local notation "sel" => selected G S board k tail age p f g drift degree h previous nextM C packet oldLanes
  primitiveLanes printedBits venue addr roster

theorem selected_repack_dictionary (base : ℕ) (short : 8*price≤h) (cube : k≤laneBits dim h price) :
    let a:=sel base
    a.re+a.field*(2^a.re*2^a.e)≤a.payload/2:=by
  let e:=receiverCut G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits venue
  have cut : e≤laneBits dim h price-k:=(selected_cut G S board k tail age p f g drift degree h previous nextM C packet
    oldLanes primitiveLanes printedBits venue).2.1
  have pos : 0<price:=by unfold AtomSchedule.localWalshBits DescentWalshPrecision.bits;omega
  exact repack_dictionary pos short cube cut

theorem scheduled_repack_dictionary (op : RotorSpec) (t f g reset τ B : ℕ)
    (cutoff : 2*(1+(hostRate t reset+capRate G t g)*(t+1)+8+cutRate t f g)≤B) :
    ∀ᶠ h : ℕ in atTop, let J:=Nat.log 2 h/(2*B)
    ∀sites age p drift degree,let S:=stageNumbers G t J f g reset sites (τ*(J+1))
    let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
    ∀(ordinary : ℕ→Dated.Ordinary) (old : StageVenueTail.Date) (s Z operandLanes primitiveLanes base : ℕ)
        (addr : ℕ→ℕ→Bank) (roster : Bank),
      age≤S.length → p≤h →
        let a:=scheduled G S board k (τ*(J+1)) age p f g drift degree h ordinary op s Z operandLanes primitiveLanes
          old addr roster base
        a.re+a.field*(2^a.re*2^a.e)≤a.payload/2:=by
  filter_upwards [measured_lane_room G t f g reset τ B (quota t) cutoff,
    eventually_actual_width G t f g reset B (quota t) τ] with h low words
  intro J sites age p drift degree S k ordinary old s Z operandLanes primitiveLanes base addr roster within paid
  have jle : J≤Nat.log 2 h:=Nat.div_le_self ..
  have bounded : τ*(J+1)≤τ*(Nat.log 2 h+1)^2:=Nat.mul_le_mul_left _ ((Nat.succ_le_succ jle).trans (by nlinarith))
  have short:=(words sites (τ*(J+1)) age p paid bounded within).1
  exact selected_repack_dictionary G S board k (τ*(J+1)) age p f g drift degree h
    (NativePitch.resetCut S k (τ*(J+1)) p f h age) (NativePitch.incoming S k (τ*(J+1)) p f h ordinary (age+1))
    op.C op.w operandLanes primitiveLanes (DescentPrimitivePalette.printedBits G s Z op) old addr roster base
    (short.trans (Nat.div_le_self ..)) (low sites age p within paid)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
