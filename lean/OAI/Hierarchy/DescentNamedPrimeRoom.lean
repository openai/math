import OAI.Hierarchy.DescentNamedIngressCode
import OAI.Hierarchy.DescentResetCanvasInputBanks
import OAI.Hierarchy.DescentMeasuredResetArena

namespace OAI
/-! The fixed Walsh input addresses and estimator bounds at a public reset date. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh DescentSIMDLookup DescentWalshPrecision
open DescentPlainTerminal.Suffix DescentSixParty.PackedFlow.Canvas ProtocolRAM
noncomputable section
set_option quotPrecheck false

theorem estimator_before_repacking (a : PhysicalReset) (start : ℕ) :
    (a.estimator start).endAddress ≤ a.rebased start := by
  let P:=a.chart start
  have h:=(P.estimator_range a.payload a.gain a.positive).2.2
  change (P.estimator a.payload a.gain a.positive).endAddress≤P.repackedEnd _ _ _ _ _ _ _
  unfold Placement.repackedEnd Placement.rotationEnd Subwords.finish Subwords.destination
  dsimp only
  omega

variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
  (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree payload : ℕ)
  (e previous M nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
  (io : DescentPacking.PackedMatch.Local.Stage.Dated.Operands) (floor : ℕ)
local notation "a₀" => named G S board k tail age p f g drift degree payload e previous M nextM C packet
  oldLanes primitiveLanes printedBits venue io.wire io.roster floor
local notation "start" => (a₀).stageStart floor
local notation "cc" => S.groupWidth k tail age
local notation "mm" => cc+k
local notation "bb" => S.localWalshBits p mm f (quota S.rounds)
local notation "ll" => laneBits mm payload bb

/-- Both transfer widths are the literal calendar widths. The only incoming memory
requirements concern the preceding count and its physical roster. -/
theorem named_prime_room (count : Bank) (w : ℕ)
    (groups : 2^cc=S.groupCount age) (block : k≤ll) (small : 8*bb≤payload) (word : payload≤w)
    (decay : DescentBaseProfile.decayExponent venue.degree<2^w)
    (countBefore : count.base+count.size≤floor)
    (rosterBefore : io.roster.base+io.roster.size≤floor)
    (rosterRows : S.hostSize age*venue.degree≤ io.roster.size)
    (roof : (a₀).fullEnd floor<2^w) :
    (a₀).PrimeRoom start ((a₀).ingress.source floor) count (S.groupCount age) venue.degree w := by
  let a:=a₀
  let L:=a.ingress
  let P:=a.chart (a.stageStart floor)
  have early : floor≤a.stageStart floor:=by
    obtain ⟨r,s,t⟩:=L.order floor
    exact r.trans (s.trans t)
  have scope:=a.occupied (a.stageStart floor)
  have ingressRoom : L.endAddress floor<2^w:=((scope.1.trans scope.2.1).trans scope.2.2).trans_lt roof
  obtain ⟨src,_,ports⟩:=L.input_banks ingressRoom
  have low : ll≤ mm:=Nat.min_le_left _ _
  have dim : a.high+a.low=mm:=Nat.sub_add_cancel low
  have gdim : mm-ll+(ll-k)=cc:=by omega
  have blocks : S.groupCount age=2^(mm-ll)*2^(ll-k):=by rw [←pow_add,gdim,groups]
  have width : 0<bb:=a.positive
  have unit : bb*2^ll≤payload/2:=by
    have short:=keys_fit (m:=mm) width small
    change 1+(bb+bb)*2^ll≤payload/2 at short
    rw [Nat.add_mul] at short
    omega
  have gain : a.gain≤a.bits:=DescentWalshPrecision.gain_le ..
  have estimatorRoom : (a.estimator (a.stageStart floor)).endAddress<2^w:=
    ((estimator_before_repacking a _).trans scope.2.2).trans_lt roof
  have capacity : a.gain+a.bits*2^a.low≤w:=by
    change _+bb*2^ll≤w
    change _≤bb at gain
    omega
  have fitted := P.native_fits a.payload a.gain w a.positive
    (show laneBits (a.high+a.low) a.payload a.bits=a.low from by rw [dim];rfl) capacity estimatorRoom
  have axes : mm≤bb:=by
    change mm≤DescentWalshPrecision.bits mm f (quota S.rounds) (S.censusBits p)
    unfold DescentWalshPrecision.bits
    omega
  refine ⟨?_,src.2.2,?_,rosterBefore.trans early,rosterRows,countBefore.trans early,decay,?_,fitted,estimatorRoom,word⟩
  · change chunks (S.groupCount age) (2^(ll-k))=2^(mm-ll)
    rw [blocks,Subwords.chunks_exact _ _ (Nat.two_pow_pos _)]
  · intro j
    rw [named_ingress_token floor G S board k tail age p f g drift degree payload e previous M nextM C packet
      oldLanes primitiveLanes printedBits venue io j]
    have actual:=ports (j.1.cast (by rfl),j.2.cast (by rfl))
    refine ⟨actual.1.2.2,?_⟩
    rw [←groups]
    exact actual.2
  · change a.high+a.low<2^w
    rw [dim]
    exact lt_of_le_of_lt (by omega) (Nat.lt_two_pow_self (n:=w))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
