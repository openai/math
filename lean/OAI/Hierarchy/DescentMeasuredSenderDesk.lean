import OAI.Hierarchy.DescentObservedSenderDesk
import OAI.Hierarchy.DescentRecordedRootSnapshot
import OAI.Hierarchy.DescentCalendarSenderPrior

namespace OAI
/-! # The attained contact sender register and the original matrix with padded hosts -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentResetHostSize DescentSIMDLookup DescentSharedBookScan
open DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected DescentGroupPeerOrder
open DescentPaidResidentCount.Reset DescentOldContactSender DescentStageEdgeReceipt DescentRosterOrder
open DescentSharedCableNames.Stage DescentIssuedFallbackPanel DescentResetLocalRoster DescentPacking
open scoped Classical Fin.CommRing
noncomputable section
set_option hygiene false
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail field : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "c" => (T).commonDepth
local notation "r" => (Z).k-c
local notation "Y" => 2^(Z).n
local notation "H" => S.hostSize i
local notation "dep" => GroupStage.depthBound D n f g
local notation "host" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "dim" => S.groupWidth k tail i+k
local notation "L" => 2^(dim-c)
local notation "short" => B.frame.enough.trans (Nat.sub_le ..)
local notation "name" => Recorded.oldName input
local notation "next" => PackedFlow.Padded.roster (D:=(A).degree) (A) name input.valid.host
local notation "paid" => Recorded.paddedValue (b:=field) c r next (Recorded.oldDepth B) (Recorded.oldWidth B)
variable (obs : PaddedSnapshot B input.valid.host field)
local notation "rank" => ranks (a:=r) («Y»:=Y) (D:=(A).degree) obs.chart (2^dep) (dep+2) obs.memory

/-- The input matrix on the original host rectangle. Its last six digits use the
observed cap, true peer order, and neighbor depths of the reservation lookup. -/
def senderMatrix : Fin H→Block c→Fin (DescentRotorWindowArchive.count (A).degree L (A).cap)→Cell field :=
  RootSources.paddedRow obs.stencil obs.peers obs.marks (fun u j=>((rank) u j).val)
    (fun _=>GroupStage.previousDigit B.frame.basis short) paid

def senderRank (v : Fin H) (j : Fin (DescentSharedBookScan.width r Y (A).degree)) : Cell field:=((rank) v j).val

theorem measured_sender_desk (elapsed : 0< i) (sorted : SourceSorted W input.order)
    (baseRoom : max (max r Y) (2^r)<2^field) (dimRoom : (Z).n<field)
    (socketRoom : rootSlots r Y*(Y+2^dep)<2^field) (heightRoom : dep<2^field)
    (portRoom : (A).degree≤2^field) :
    ∃setup : (senderDesk B field).Inputs,∀v hi,
      decode (RootSources.senderWords (senderMatrix B obs) (senderRank B obs) (host v) hi)=
        (senderDesk B field).sample setup v hi:=by
  have rows:=Recorded.old_roster (reset:=B)
  rw [PackedFlow.mutual_near (A)] at rows
  have paidRead (v : input.V) (j l : Fin (A).degree) (s : Fin 6):=
    Recorded.paddedValue_at (b:=field) (reset:=B) v j l s
  have donor:=GroupStage.scheduledDonorOrder (S:=S) (A) ctl.base ctl.radix input.vertex
    input.valid.coordinates (input.siteName elapsed)
  have jo (s : Bool) (t : (Z).placement.Contact) : (Z).senderJoint T s t<2^field:=by
    let key:=rootId r Y ((Z).rootTicket T ((Z).placement.owner s t))
    let slot : Fin (Y+2^dep):=⟨_,(Z).contactSlotWord_lt T s t⟩
    apply Nat.lt_of_le_of_lt _ socketRoom
    apply Nat.succ_le_of_lt
    change key.val * (Y + 2^dep) + slot.val < rootSlots r Y * (Y + 2^dep)
    have inside := (finProdFinEquiv (key,slot)).isLt
    change slot.val + (Y + 2^dep) * key.val < rootSlots r Y * (Y + 2^dep) at inside
    simpa only [Nat.add_comm,Nat.mul_comm] using inside
  rcases input with @⟨V,vFin,vDec,phase,ready,rfl,rfl,history,degree,oldOrder,compact,edgeOrder,siteOrder⟩
  rcases B with ⟨ct,rfl,fit₀,order,eq_,Z₀,T₀,age,date,extent,tickets,unit,dimension,tape,board,
    frame,listed,raw,geometry,hubs,valid,grain,wire,atoms,branch,capacity⟩
  subst order
  let digits:=S.resetInputDigits ctl.base ctl.radix i
  let groups:=Fin.valEmbedding (n:=S.groupCount i)
  let large:=compact.trans (Fin.castLEEmb ready.host)
  let args:=GroupStage.observedSenderInputs phase S ready digits oldOrder Z₀ T₀ frame groups compact
    ready.host obs f (phase.wire*(phase.z*G.b)*phase.cap) phase.wire (quota S.rounds) (phase.resetFlow digits)
    (phase.resetLoad digits) rows donor sorted tickets baseRoom dimRoom jo heightRoom portRoom
  refine ⟨args,?_⟩
  intro v hi
  apply GroupStage.observed_sender_words phase S ready digits oldOrder Z₀ T₀ frame groups compact
    ready.host obs f (phase.wire*(phase.z*G.b)*phase.cap) phase.wire (quota S.rounds) (phase.resetFlow digits)
    (phase.resetLoad digits) rows donor sorted tickets baseRoom dimRoom jo heightRoom portRoom
  intro u j l s
  refine (paidRead u j l s).trans ?_
  dsimp only
  unfold GroupStage.peerData
  cases first : hostRoster phase (compact.trans Fin.valEmbedding) u j <;>
    cases last : hostRoster phase (compact.trans Fin.valEmbedding) u l <;> rfl

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
