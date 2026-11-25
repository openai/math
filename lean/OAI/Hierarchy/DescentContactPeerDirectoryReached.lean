import OAI.Hierarchy.DescentResetPeerDirectory
import OAI.Hierarchy.DescentContactDonorReached

namespace OAI
/-! # The three-port directory after the genuine preceding sender exchange -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentSortedRoster DescentSharedCableNames DescentCompiler DescentColonies DescentDenseHostOrder DescentResetPeerUnionRAM DescentGroupPeerOrder
open DescentPackedColony DescentSIMDLookup DescentPackedZip ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {pinBits : P→ℕ} {W : MarkedWorld F d P pinBits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "height" => GroupStage.depthBound D n f g
local notation "r" => (Z).k-(T).commonDepth
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r height).card
local notation "J" => 2^(T).commonDepth
local notation "D₀" => input.placement.degree
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "Host" => DescentSharedCableNames.Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

variable (base H M field keyBits bits contactBits queryBits cargoBits : ℕ) (old : PeerInputs B)
local notation "L" => peerLayout B base H M field keyBits bits
local notation "front" => peerDonorShape B H M contactBits queryBits cargoBits
local notation "donorStart" => (L).endAddress
local notation "contactStart" => (front).endAddress donorStart
local notation "A" => contactLayout B contactStart H M contactBits bits
local notation "pitch" => H*shelf
local notation "E" => peerEvidenceRows B
local notation "tpl" => peerTemplate B
local notation "terms" => (peerTerms B base H M field keyBits bits contactBits contactStart old).all
local notation "floor_" => (A).endAddress
local notation "stop_" => Program.endAddress floor_ H shelf D₀ E bits M
local notation "scratch_" => Program.scratchAt floor_ H shelf D₀ E bits M
local notation "firstCode" => RawTables.program (Z).graph r height L tpl
local notation "firstOut" => RawTables.image (Z).graph r height L tpl
variable {w : ℕ} (u₀ : DescentContactSenderDate.Prior D₀ (front).lows (front).cap (front).n (front).residual)
local notation "boardReads" => (front).oldBoard u₀
local notation "donorReads" => (front).priorSensor donorStart
local notation "donorCode" => (front).program donorStart u₀ w
local notation "donorTime" => (front).ticks donorStart u₀
local notation "donorOut" => (front).memory donorStart u₀
variable (donorRoom : (front).Space donorStart u₀ w) (ends : floor_<2^w)
    (packedMarker : M*max (contactBits*8) bits≤w/2)
local notation "space" => (front).markerSpace donorStart shelf bits u₀ donorRoom ends packedMarker
local notation "contactCode" => (A).program (Z).graph boardReads donorReads space
local notation "contactOut" => (A).memory (Z).graph boardReads donorReads space
local notation "contactTime" => (A).ticks (Z).graph boardReads donorReads space
local notation "lastCode" => Program.program w floor_ H shelf D₀ bits M J old.oldPorts marked terms
local notation "lastOut" => Program.output floor_ H shelf D₀ bits M J old.oldPorts marked terms
local notation "lastTime" => Program.clock floor_ H shelf D₀ bits M J old.oldPorts terms

variable (m : Memory w) {count : ℕ} (pad : Fintype.card input.V ≤ H)
local notation "padded" => (vertex).trans (Fin.castLEEmb pad)
local notation "named" => (Z).rawHostRank T padded
variable (prior : PriorPeerWords B H field keyBits) (unit : 0 < (Z).unit)
    (panel : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel height count)
    (peers : Fin H→Fin D₀→Option (Fin H))
    (xs : Fin H→Fin J→Fin (DescentOldContactSender.count D₀ (front).lows (front).cap (front).n (front).residual)→Cell contactBits)
    (raw : Fin (front).lows→Fin (2*(front).cap)→Fin H→Fin J→Cell contactBits)
local notation "board" => (front).boardValues xs
local notation "sensed" => (front).sensorValue donorStart xs peers raw
local notation "fish" => fun (v : Fin pitch) (l : Fin J) (s : Bool) (j : Fin (A).half) (a : Fin 5)=>
  DescentContactProbePitch.lift (S:=shelf) (sensed s j a) v l
local notation "paid" => fun (v : Fin pitch) (l : Fin J) (s : Bool) (j : Fin (A).half) (a : Fin 2)=>
  DescentContactProbePitch.lift (S:=shelf) ((A).viewValue board ((A).view s j a)) v l
local notation "observed" => issuedContactValue B contactStart H M contactBits bits fish paid
local notation "endMem" => lastOut (contactOut (donorOut (firstOut m)))

variable (setup : (senderDesk B contactBits).Inputs)
local notation "hosts" => input.vertex.trans (Fin.castLEEmb pad)
local notation "gr" => Function.Embedding.refl (Fin (S.groupCount i))
local notation "names" => DescentPacking.PackedMatch.Local.Stage.cableNames k (DescentStageEdgeReceipt.groupRank
  ((gr).trans Fin.valEmbedding) ((hosts).trans Fin.valEmbedding))
local notation "native" => input.order.trans Fin.valEmbedding
local notation "small" => B.frame.enough.trans (Nat.sub_le ..)
local notation "words" => S.resetInputDigits ctl.base ctl.radix i

/-- The same execution prints the four shared raw tables, builds the complete contact catalog from
old stored reservations and a native donor-and-halo pass, and emits three peer words for each possible receiver. -/
theorem issued_peer_directory_reached
    (measured : ∀v l,DescentOldContactSender.decode (xs (hosts v) l)=(senderDesk B contactBits).sample setup v l)
    (signed : ∀v l lo j,raw lo j (hosts v) l=DescentResetOppositePayload.widened D₀ input.placement.cap contactBits
      (DescentSharedCableNames.Stage.signedPanel input.placement native S input.valid names
        (DescentIssuedFallbackPanel.donor words B.frame.basis small v l lo) j))
    (coded : DescentSignedCableCodec.width D₀ input.placement.cap≤contactBits) (wordPositive : 0<contactBits)
    (positions : OldPeerReads B base H M field keyBits old prior m)
    (origins : PeerOrigins B pad prior unit panel)
    (rosterRead : ∀(v : input.V) j,peers ((input.vertex v).castLE pad) j=
      (hostRoster input.placement (input.vertex.trans Fin.valEmbedding) v j).map (fun a=>(input.vertex a).castLE pad))
    (portFit : old.oldPorts.Fits w base) (portSize : H*D₀ ≤ old.oldPorts.size)
    (portRead : ∀(h : Fin H) (j : Fin D₀),m (old.oldPorts.base+(h.val*D₀+j.val))=(target (peers h j):Word w))
    (donorPacked : ((front).sender donorStart).Packed w)
    (donorPrior : ((front).sender donorStart).Before u₀ xs peers raw (firstOut m))
    (boardWidth : M*max (contactBits*(A).oldFields) (A).viewBits ≤ w/2)
    (shapeWidth : shelf ≤ 2^contactBits) (markerWidth : (D₀+1)*shelf < 2^bits) (room : stop_ < 2^w) :
    let code:=(((firstCode w).seq donorCode).seq contactCode).seq lastCode
    code.Exec m endMem ((((L).ticks+donorTime)+contactTime)+lastTime) ∧ CheapCode code ∧
    (∃found : Fin pitch→Fin 3→Option (Fin pitch),
      (∀(v : Fin pitch) (j : Fin 3),endMem (outBase scratch_ pitch (Candidates.count shelf D₀)+j.val*pitch+v.val)=(target (found v j):Word w)) ∧
      (∀v : B.next.V,present (selfPeers found) (named v)=(insert v ((Z).emittedNear T v)).map named) ∧
      (∀v : B.next.V,(∀j,found (named v) j≠some (named v)) ↔ v∉(Z).emittedNear T v)) ∧
    ∀a,a < base ∨ stop_ ≤ a → endMem a=m a := by
  have generated:=reached_donor_sensors B H M contactBits queryBits cargoBits donorStart bits pad xs peers raw setup measured
    rosterRead signed coded wordPositive
  have attained (a : Fin (A).oldFields) : Source (boardReads a) (fun h l=>board h l a) M (donorOut (firstOut m)):=fun p=>
    (eval_below _ _ _ _ (donorRoom.sender.board _) (fun x low=>((front).any donorStart u₀ donorRoom (firstOut m)).2.2 x (.inl low))).trans
      (donorPrior.input _ p)
  exact issued_peer_directory B base H M field keyBits bits contactBits queryBits cargoBits old boardReads u₀ space
    m pad prior unit panel peers board xs raw positions origins rosterRead portFit portSize portRead donorRoom donorPacked donorPrior
    attained generated donorPacked.positive boardWidth shapeWidth markerWidth room

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
