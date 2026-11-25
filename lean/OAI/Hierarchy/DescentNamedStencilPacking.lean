import OAI.Hierarchy.DescentStencilLaneRoom
import OAI.Hierarchy.DescentResetStencilCalendar
import OAI.Hierarchy.DescentNamedResetAtlas

namespace OAI
/-! The public endpoint pitch also certifies the two signed stencil operand sizes in the
native reset on the chosen named input. The degree comes from the previous physical venue. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPlainTerminal.Suffix PackedFlow.Padded
open DescentPackedWalsh DescentGLPacked ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
    (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor : ℕ)
local notation "aₛ" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "Qₛ" => S.endpointBook k tail age p f venue.degree payload n
local notation "eₛ" => S.endpointExponent k tail age p f venue.degree payload n

/-- The same purchase supplies the exponent inequality consumed by 'namedStencil'. -/
theorem endpoint_walsh_cut (short : e ≤ eₛ) (wide : 4*sharedWidth Qₛ ≤ payload) :
    e ≤ laneBits (S.groupWidth k tail age+k) payload (S.localWalshBits p (S.groupWidth k tail age+k) f (quota S.rounds))-k :=by
  have hb : 0 < (Qₛ).b:=by
    change 0 < DescentWalshPrecision.bits _ _ _ _
    unfold DescentWalshPrecision.bits;omega
  have axes : (Qₛ).c ≤ (Qₛ).m:=Nat.le_add_right ..
  have bought:=pitch_inside Qₛ payload hb axes wide
  have depth : (Qₛ).r=k:=by change S.groupWidth k tail age+k-S.groupWidth k tail age=k;omega
  change eₛ+(Qₛ).r ≤ laneBits (S.groupWidth k tail age+k) payload ((Qₛ).b) at bought
  rw [depth] at bought
  change e ≤ laneBits (S.groupWidth k tail age+k) payload ((Qₛ).b)-k
  omega

theorem named_stencil_packing (count : Bank) (w : ℕ) (sh : (aₛ).StencilShape)
    (short : e ≤ eₛ) (wide : 4*sharedWidth Qₛ ≤ payload) (word : payload ≤ w) :
    let txn:=(aₛ).stencilPhase sh ((aₛ).stageStart floor) count io.hubs g (2^n)
    txn.S.M*max (txn.S.n*Stencil.count txn.S.r (txn.S.degree+txn.S.degree)) (txn.S.t*2^txn.S.r) ≤ w/2 ∧
      txn.S.n*txn.S.M ≤ w :=by
  have hb : 0 < (Qₛ).b:=by
    change 0 < DescentWalshPrecision.bits _ _ _ _
    unfold DescentWalshPrecision.bits;omega
  exact stencil_lane_room Qₛ e payload w hb wide short word

/-- A single hardware threshold works for all reached degrees, dates and initial sizes.
The work bound below uses the real count-source instruction in the physical phase. -/
theorem eventually_named_stencil_packing (t reset τ B maximum : ℕ) (den : 0 < B)
    (bought : 2*(3*stencilRate G t f g reset+1) ≤ B) :
    ∀ᶠ h : ℕ in atTop, ∀fund i size bus,
      let J:=Nat.log 2 h/(2*B)
      let sched:=stageNumbers G t J f g reset fund (DescentCompiler.TerminalScale.tail τ J)
      let radixBits:=groupBits t J sched.hostGain sched.capGain (cutRate t f g)
      ∀(drift degree actual previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ)
        (venue : StageVenueTail.Date) (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor : ℕ) (count : Bank),
      let a:=named G sched board radixBits (DescentCompiler.TerminalScale.tail τ J) i size f g drift degree h actual
        previous M nextM C packet oldLanes primitiveLanes printedBits venue io.wire io.roster floor
      ∀sh : a.StencilShape, let txn:=a.stencilPhase sh (a.stageStart floor) count io.hubs g (2^n)
      i ≤ sched.length → size ≤ h → venue.degree ≤ maximum → h ≤ bus →
      actual ≤ sched.endpointExponent radixBits (DescentCompiler.TerminalScale.tail τ J) i size f venue.degree h n →
      txn.S.M*max (txn.S.n*Stencil.count txn.S.r (txn.S.degree+txn.S.degree)) (txn.S.t*2^txn.S.r) ≤ bus/2 ∧
        txn.S.n*txn.S.M ≤ bus :=by
  filter_upwards [Filter.eventually_all.mpr (fun D : Fin (maximum+1)=>
    endpoint_shape_at G t f g reset τ B D.val n den bought)] with h receipts
  intro fund i size bus J sched radixBits drift degree actual previous M nextM C packet oldLanes primitiveLanes
    printedBits venue io floor count a sh txn date dataSize degreeFit machine chosen
  let D : Fin (maximum+1):=⟨venue.degree,by omega⟩
  have low : txn.X.count.work ≤ 6:=by rfl
  have shape:=receipts D fund i size txn.X date dataSize low
  exact named_stencil_packing G sched board radixBits (DescentCompiler.TerminalScale.tail τ J) i size f g drift degree h
    actual previous M nextM C packet oldLanes primitiveLanes printedBits venue io floor count bus sh
    chosen shape.2.1 machine

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
