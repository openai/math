import OAI.Hierarchy.DescentResetPeerCalibration
import OAI.Hierarchy.DescentContactDonorFront

namespace OAI
/-! # The native three-port reset neighbor directory from original predecessor words -/
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
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "Slot" => Fin (2^(S.groupWidth k tail i+k-(T).commonDepth))×Fin (2*input.placement.cap)
local notation "kind_" => Axes.kind (stemsCount B) (contactCount B) (privateCount B)

def peerDonorShape (H M contactBits queryBits cargoBits : ℕ) : DescentContactDonorFront.Shape :=
  ⟨H,J,M,D₀,2^(S.groupWidth k tail i+k-(T).commonDepth),input.placement.cap,
    (Z).n,r,height,contactBits,queryBits,cargoBits⟩

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
variable {w : ℕ} (boardReads : Fin (A).oldFields→Expr)
  (u₀ : DescentContactSenderDate.Prior D₀ (front).lows (front).cap (front).n (front).residual)
local notation "donorReads" => (front).priorSensor donorStart
local notation "donorCode" => (front).program donorStart u₀ w
local notation "donorTime" => (front).ticks donorStart u₀
local notation "donorOut" => (front).memory donorStart u₀
variable (space : (A).Space boardReads donorReads w)
local notation "contactCode" => (A).program (Z).graph boardReads donorReads space
local notation "contactOut" => (A).memory (Z).graph boardReads donorReads space
local notation "contactTime" => (A).ticks (Z).graph boardReads donorReads space
local notation "lastCode" => Program.program w floor_ H shelf D₀ bits M J old.oldPorts marked terms
local notation "lastOut" => Program.output floor_ H shelf D₀ bits M J old.oldPorts marked terms
local notation "lastTime" => Program.clock floor_ H shelf D₀ bits M J old.oldPorts terms

def directoryCode : Procedure w := (((firstCode w).seq donorCode).seq contactCode).seq lastCode
def directoryImage (m : Memory w) : Memory w := lastOut (contactOut (donorOut (firstOut m)))
def directoryClock := (((L).ticks+donorTime)+contactTime)+lastTime

variable (m : Memory w) {count : ℕ} (pad : Fintype.card input.V ≤ H)
local notation "padded" => (vertex).trans (Fin.castLEEmb pad)
local notation "named" => (Z).rawHostRank T padded
variable (prior : PriorPeerWords B H field keyBits) (unit : 0 < (Z).unit)
    (panel : Bool→(Z).Fallback→DescentPackedFallbackTree.Panel height count)
    (peers : Fin H→Fin D₀→Option (Fin H))
    (board : Fin H→Fin J→Fin (A).oldFields→Cell contactBits)
    (xs : Fin H→Fin J→Fin (DescentOldContactSender.count D₀ (front).lows (front).cap (front).n (front).residual)→Cell contactBits)
    (raw : Fin (front).lows→Fin (2*(front).cap)→Fin H→Fin J→Cell contactBits)
local notation "sensed" => (front).sensorValue donorStart xs peers raw
local notation "fish" => fun (v : Fin pitch) (l : Fin J) (s : Bool) (j : Fin (A).half) (a : Fin 5)=>
  DescentContactProbePitch.lift (S:=shelf) (sensed s j a) v l
local notation "paid" => fun (v : Fin pitch) (l : Fin J) (s : Bool) (j : Fin (A).half) (a : Fin 2)=>
  DescentContactProbePitch.lift (S:=shelf) ((A).viewValue board ((A).view s j a)) v l
local notation "observed" => issuedContactValue B contactStart H M contactBits bits fish paid
local notation "endMem" => lastOut (contactOut (donorOut (firstOut m)))

/-- The same execution prints the four shared raw tables, builds the complete contact catalog from
old stored reservations and a native donor-and-halo pass, and emits three peer words for each possible receiver. -/
theorem issued_peer_directory
    (positions : OldPeerReads B base H M field keyBits old prior m)
    (origins : PeerOrigins B pad prior unit panel)
    (rosterRead : ∀(v : input.V) j,peers ((input.vertex v).castLE pad) j=
      (hostRoster input.placement (input.vertex.trans Fin.valEmbedding) v j).map (fun a=>(input.vertex a).castLE pad))
    (portFit : old.oldPorts.Fits w base) (portSize : H*D₀ ≤ old.oldPorts.size)
    (portRead : ∀(h : Fin H) (j : Fin D₀),m (old.oldPorts.base+(h.val*D₀+j.val))=(target (peers h j):Word w))
    (donorRoom : (front).Space donorStart u₀ w)
    (donorPacked : ((front).sender donorStart).Packed w)
    (donorPrior : ((front).sender donorStart).Before u₀ xs peers raw (firstOut m))
    (oldBoard : ∀a,Source (boardReads a) (fun h l=>board h l a) M (donorOut (firstOut m)))
    (sensors : ∀v l,ContactSensors B (contactReceiver B v l) (fish (named v) l) (paid (named v) l))
    (positive : 0 < M) (boardWidth : M*max (contactBits*(A).oldFields) (A).viewBits ≤ w/2)
    (shapeWidth : shelf ≤ 2^contactBits) (markerWidth : (D₀+1)*shelf < 2^bits) (room : stop_ < 2^w) :
    let code:=(((firstCode w).seq donorCode).seq contactCode).seq lastCode
    code.Exec m endMem ((((L).ticks+donorTime)+contactTime)+lastTime) ∧ CheapCode code ∧
    (∃found : Fin pitch→Fin 3→Option (Fin pitch),
      (∀(v : Fin pitch) (j : Fin 3),endMem (outBase scratch_ pitch (Candidates.count shelf D₀)+j.val*pitch+v.val)=(target (found v j):Word w)) ∧
      (∀v : B.next.V,present (selfPeers found) (named v)=(insert v ((Z).emittedNear T v)).map named) ∧
      (∀v : B.next.V,(∀j,found (named v) j≠some (named v)) ↔ v∉(Z).emittedNear T v)) ∧
    ∀a,a < base ∨ stop_ ≤ a → endMem a=m a := by
  intro code
  have ord:=(A).ordered
  have ll:=(L).bounds
  have lo : base ≤ (L).endAddress := ll.1.trans (ll.2.1.trans (ll.2.2.1.trans ll.2.2.2))
  have donorOrder:=(front).ordered donorStart
  have donorBefore : (L).endAddress ≤ contactStart :=
    donorOrder.1.trans (donorOrder.2.1.trans donorOrder.2.2)
  have contacted : contactStart ≤ floor_ :=
    ord.1.trans (ord.2.1.trans (ord.2.2.1.trans (ord.2.2.2.1.trans ord.2.2.2.2)))
  have mid:=donorBefore.trans contacted
  have last : floor_ ≤ stop_ := by
    dsimp only [Program.endAddress,stop,outBase,Program.scratchAt,Program.tablesAt]
    omega
  obtain ⟨exec₁,cheap₁,_,keep₁⟩:=RawTables.any (Z).graph r height L tpl m (mid.trans_lt space.extent)
  have ⟨donorRun,donorCheap,donorFrame⟩:=(front).any donorStart u₀ donorRoom (firstOut m)
  have donorData:=(front).sources donorStart u₀ donorRoom xs peers raw (firstOut m) donorPacked donorPrior
  have fitted : D₀*shelf < 2^bits := (Nat.mul_le_mul_right shelf (Nat.le_succ _)).trans_lt markerWidth
  obtain ⟨exec₂,cheap₂,reads₂,_,keep₂⟩:=
    contact_date B contactStart H M contactBits bits pad peers rosterRead boardReads donorReads space
      (donorOut (firstOut m)) board sensed positive boardWidth oldBoard donorData sensors shapeWidth fitted
  have contactDigit (u : Host) key donor :
      (observed key donor (named u.1.2) (peerLane B u)).val=contactSheet B u key donor := by
    have cell:=issued_contact_mark B contactStart H M contactBits bits pad fish paid sensors shapeWidth fitted
      key donor u.1.2 (peerLane B u)
    change _=contactSheet B (peerReceiver B u.1.2 (peerLane B u)) key donor at cell
    rwa [receiver_lane] at cell
  have cert:=peer_origins B pad prior unit panel origins peers rosterRead markerWidth observed contactDigit
  have operands:=measured_operands B base H M field keyBits bits contactBits contactStart old prior m
    (contactOut (donorOut (firstOut m))) positions donorBefore space.extent
    (fun a ha=>(keep₂ a (.inl (ha.trans_le donorBefore))).trans (donorFrame a (.inl ha))) observed reads₂
  have oldSize : H*D₀ ≤ old.oldPorts.size := portSize
  have safe : Program.Space floor_ H shelf D₀ E bits M J w old.oldPorts terms :=
    ⟨⟨portFit.1,portFit.2.1,portFit.2.2.trans (lo.trans mid)⟩,oldSize,fun e=>(operands e).1,room⟩
  have tape (h₀ : Fin H) (j : Fin D₀) :
      contactOut (donorOut (firstOut m)) (old.oldPorts.base+(h₀.val*D₀+j.val))=(target (peers h₀ j):Word w) := by
    let slot:=finProdFinEquiv (h₀,j)
    have pos : slot.val=h₀.val*D₀+j.val:=by simp [slot,finProdFinEquiv_apply_val,Nat.add_comm,Nat.mul_comm]
    have below : old.oldPorts.base+(h₀.val*D₀+j.val) < base :=
      (Nat.add_lt_add_left ((pos ▸ slot.isLt).trans_le portSize) _).trans_le portFit.2.2
    have beforeDonor:=below.trans_le lo
    exact (keep₂ _ (.inl (beforeDonor.trans_le donorBefore))).trans
      ((donorFrame _ (.inl beforeDonor)).trans ((keep₁ _ (.inl below)).trans (portRead h₀ j)))
  obtain ⟨exec₃,cheap₃,published,keep₃⟩:=
    genuine_program B pad old.oldPorts terms safe peers kind_ _ (contactOut (donorOut (firstOut m))) tape
      (fun e h₀ c=>(operands e).2 c h₀) positive cert
  refine ⟨Procedure.Exec.then (Procedure.Exec.then (Procedure.Exec.then exec₁ donorRun) exec₂) exec₃,cheap_seq (cheap_seq (cheap_seq cheap₁ donorCheap) cheap₂) cheap₃,published,?_⟩
  intro a outer
  have saved₃:=keep₃ a (outer.imp (fun low=>low.trans_le (lo.trans mid)) id)
  have saved₂:=keep₂ a (outer.imp (fun low=>low.trans_le (lo.trans donorBefore)) (fun high=>last.trans high))
  have savedDonor:=donorFrame a (outer.imp (fun low=>low.trans_le lo) (fun high=>contacted.trans (last.trans high)))
  have saved₁:=keep₁ a (outer.imp id (fun high=>mid.trans (last.trans high)))
  exact saved₃.trans (saved₂.trans (savedDonor.trans saved₁))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
