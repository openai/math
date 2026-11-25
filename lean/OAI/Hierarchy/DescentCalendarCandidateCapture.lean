import OAI.Hierarchy.DescentCalendarMeasuredChannels
import OAI.Hierarchy.DescentCalendarJointRegisters
import OAI.Hierarchy.DescentPhysicalContactInputs
import OAI.Hierarchy.DescentResetPeerCorrectionRoom
import OAI.Hierarchy.DescentGenuineRosterDistinct

namespace OAI
/-! # Physical reachability bounds for every measured reset candidate channel -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

local notation "measured" => measured_menu B oldBatch batch calendar I cal pad prior xs raw near
local notation "oldScene" => (v₀).issuedScene base₀ I.earlier
local notation "start₀" => (v₀).actorEnd base₀
local notation "pre₀" m => (phys₀).preScalar start₀ oldScene I.sceneFits m
local notation "look₀" => (v₀).jointRegisters base₀ I.earlier
local notation "trunk₀" m => ((phys₀).trunkScene start₀ oldScene I.sceneFits).image m

private theorem endpoint_capacity (D shapes capacity : ℕ) :
    shapes*DescentResetPeerJointRAM.radix D≤2^CandidateFront.endpointWidth D shapes capacity := by
  have width := Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.le_max_right (DescentResetLocalRoster.fieldBits capacity) (Nat.clog 2 (D+2)+Nat.clog 2 (shapes+1)))
  refine Nat.le_trans ?_ width
  rw [Nat.pow_add]
  change shapes*2^Nat.clog 2 (D+2)≤_
  rw [Nat.mul_comm shapes]
  exact Nat.mul_le_mul_left _ ((Nat.le_succ shapes).trans (Nat.le_pow_clog (by decide) _))

private theorem cast_neighbors {srcHosts dstHosts srcPorts dstPorts : ℕ} (h : srcHosts=dstHosts) (q : srcPorts=dstPorts)
    (xs : Fin dstHosts→Fin dstPorts→Option (Fin dstHosts))
    (inj : ∀v i j z,xs v i=some z→xs v j=some z→i=j) :
    ∀(v : Fin srcHosts) (i j : Fin srcPorts) (z : Fin srcHosts),
      (xs (v.cast h) (i.cast q)).map (Fin.cast h.symm)=some z →
      (xs (v.cast h) (j.cast q)).map (Fin.cast h.symm)=some z → i=j := by
  subst dstHosts;subst dstPorts
  simpa using inj

/-- Previous physical root pages, the measured donor scan and the directory on its native cut
supply the full list of machine and word bounds for the mixed collector. -/
theorem capture_menu (ok : I.Ready) (m : Memory bw) (oldPositive : 0<oldBatch)
    (low : ∀s t,(I.earlier.pages s t).Fits bw ((phys₀).peers start₀))
    (roots : ∀s t,DescentPackedZip.Source (.lookup (I.earlier.pages s t) .row)
      (chartPages B oldBatch batch calendar I cal prior s t) (Q₀).oldBatch (pre₀ m))
    (senders : ∀q j,DescentPackedZip.Source ((K₀).fieldsAt don₀ ((v₀).trunkEnd base₀) (oldScene).donor q j)
      ((measured).contactValues q j) (K₀).donor.batch
      ((K₀).held don₀ ((v₀).trunkEnd base₀) (oldScene).donor (trunk₀ m)))
    (roster : DescentResetPeerJointRAM.Reads look₀ used (measured).names (measured).now (measured).prior (pre₀ m))
    (three : ∀h j,(pre₀ m) (((v₀).initialPeers base₀).base+(j:Fin 3).val*(peer₀).hosts+(h:Fin (peer₀).hosts).val)=
      ((((measured).near h j).elim (peer₀).hosts Fin.val : ℕ) : Word bw)) :
    PhysicalReset.DateInputs.CaptureRoom (measured) m := by
  obtain ⟨captured,kept⟩:=PhysicalReset.DateInputs.retained_registers (measured) ok m roster three
  have axes := two_le_roster_card (Z).graph r ht
  have field : (peer₀).shapes*DescentResetPeerJointRAM.radix (peer₀).oldDegree≤2^I.masked.field := by
    change _≤2^(v₀).sheets.metaBits
    rw [cal.peerShapes,cal.oldDegree,input.branch,cal.fieldWidth]
    exact endpoint_capacity ..
  refine ⟨low,roots,senders,captured,kept,?_,?_,?_,field,?_,?_⟩
  · exact cast_neighbors cal.oldCount cal.oldDegree adj_ (hostRotor_distinct (A) portChart)
  · change used≤(v₀).sheets.hosts
    rw [cal.currentCount];exact B.next.valid.host
  · rw [cal.peerShapes];omega
  · have width:=field
    rw [cal.peerShapes] at width
    exact predecessor_sign_fits (Z).graph r ht _ _ width
  · rw [cal.contactDeck,cal.privateDeck]
    exact ⟨oldPositive,oldPositive⟩


end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
