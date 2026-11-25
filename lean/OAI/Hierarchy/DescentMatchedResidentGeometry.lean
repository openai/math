import OAI.Hierarchy.DescentPackedOrdinaryLayout
import OAI.Hierarchy.DescentReadyGeometryPhase
import OAI.Hierarchy.DescentStageResidentGeometry

namespace OAI
/-! # The same measured matcher output produces the geometrical donor registers -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentRawCablePanel DescentPackedZip DescentCompiler DescentSixParty DescentStageEdgeReceipt DescentKernelHistory.BitDescription
open DescentSIMDLookup DescentPackedColony DescentTerminalEpochDecoder DescentPackedProfileWindow
open DescentSixParty.Chronology DescentTerminalEpochChart DescentPackedProfileArchive DescentPackedProfileWide
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
open DescentSixParty.StarKeys
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 850000
attribute [local irreducible] Gather.ROM.donorExpr Owners.LayoutBit.field topologyWords terrain spread
  slot pairNumber slabPacking

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {d k age L G ℓ w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : AtomSchedule) (ready : A.StateBounds S age)
  (he : 0≤ε) (groups : J≃Fin G) (hosts : V≃Fin L) (hv : L≤2^ℓ) (C : Chooser.Layout)
  (b payload unit ratio profile seats romBase : ℕ)
local notation "H" => 2^ℓ
local notation "M" => lanes payload unit
local notation "gid" => groups.toEmbedding
local notation "vid" => GroupStage.plane hosts hv
local notation "rank" => groupRank ((gid).trans Fin.valEmbedding) ((vid).trans Fin.valEmbedding)
local notation "rdx" => 2^k
local notation "cap2" => 2*A.cap
local notation "K" => 2^(k+1)
local notation "panelBits" => max (k+3) (Nat.clog 2 (A.degree+1))
local notation "s" => shape rdx A.degree cap2 profile
local notation "grain" => M*(s).pairs
variable (P₀ : Ports A.degree) (act : Bank) (wire : Fin (2^k)→Fin (2*A.cap)→Bank)
local notation "vals" => C.winners A.degree k b H G M
local notation "base" => Prepare.ROM.sortBase romBase k A.degree A.cap (k+3) M H G
local notation "bits_" => Prepare.bits H G M
local notation "outB" => Prepare.rosterBank base H A.degree
local notation "nextBase" => Prepare.next k H G M A.degree A.cap base
local notation "prep" => Prepare.ROM.chart romBase A.degree (k+3) M bits_ act vals wire
local notation "sort_" => Prepare.ROM.roster romBase k A.degree A.cap (k+3) M H G (Prepare.ROM.headBits H A.degree) P₀.roster
local notation "ps" => Prepare.passes prep sort_ base H G M A.degree
local notation "wins_" => Prepare.gatedBank (k:=k) base H G M A.degree bits_
local notation "marks_" => Prepare.markedBank (k:=k) (cap:=A.cap) base H G M A.degree bits_
local notation "field" => Gather.expr wins_ marks_ {P₀ with roster:=outB} H
local notation "donor" => Gather.ROM.donorExpr s panelBits rdx A.degree cap2 K H G M unit nextBase seats field
local notation "plan" => Gather.ROM.place s panelBits rdx A.degree cap2 K H G M unit nextBase seats
local notation "N" => (K*H)*chunks G M
local notation "top" => (plan).layout.topology
local notation "profiles" => (plan).layout.out
local notation "ft" => LayoutSum.Finish.first top profiles N
local notation "B" => LayoutSum.Finish.chart s M top profiles N
local notation "births" => LayoutSum.Finish.births s M top profiles N
local notation "doneAt" => LayoutSum.Finish.stop s M top profiles N
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "number" => (fun c : ScanColonies he A.stage=>pairNumber (DescentPacking.amount (live T))
  (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions)
local notation "pairProfile" choice => (scannedRows he A.stage).profile choice
local notation "truthFlag" choice => bestLayout (branchWidth gadget (fun _=>A.z) (pairProfile choice))


variable (rootAt cut : ℕ) (hubBank : Bank) (Q : Owners.LayoutBit.Banks)
local notation "D" => A.degree
local notation "fmt" => Owners.inputBits rdx D cap2 panelBits
local notation "L₀" => DepotRAM.Resident.Dynamic.Placement.layout H G M D fmt rootAt outB hubBank
local notation "term" => Owners.LayoutBit.field Q donor
local notation "full" => DepotRAM.Resident.Dynamic.Placement.issuedPhase H G M D rdx cap2 panelBits A.cap profile w rootAt outB hubBank term
local notation "pub" i:arg j:arg rs:arg => A.publishedTicket groups hosts rs i j
local notation "win" i:arg j:arg rs:arg => fun h : J×V=>(pub i j rs) (vid h.2) (gid h.1)
local notation "pp" i:arg j:arg rs:arg => spread gid vid (terrain (short:=panelBits) A native S ready (cableNames k rank) (win i j rs) (rotor A rank))
local notation "next" => hostRotor vid (DescentGroupPeerOrder.hostRoster A ((vid).trans Fin.valEmbedding))
local notation "tags" => fun h : Fin H=>if yes:∃v,vid v=h then A.hub yes.choose else false
local notation "owner" => Owners.Board.venue fmt M (L₀).ownerBase (H*chunks G M)

theorem LayoutReportAt.resident (choice : (A.stage.result he).Choice) (rs : DescentColonies.DynamicSplit.Roster ℓ D)
    (m matched warmed : Memory w) (code : Procedure w) (time : ℕ) (protectedAt : ℕ→Prop)
    (actual : LayoutReportAt A native S ready he groups hosts hv C b payload unit profile seats romBase P₀ choice rs m code time protectedAt matched)
    (continuation : ∀i,i<cut→warmed i=matched i) (afterOld : cut≤rootAt)
    (earlier : nextBase≤cut ∧ (plan).source.base≤cut ∧ (B).out<cut ∧ (top).base+N≤cut ∧ births+N≤cut)
    (serialized : DepotRAM.Resident.Dynamic.Room L₀ rdx D cap2 panelBits H G M w term)
    (rawFits : Owners.LayoutBit.Room Q donor H G M (panelBits*DescentPacking.PackedMatch.Local.fields rdx D cap2) w (L₀).ownerBase)
    (flag : Q.gate.base=(B).out) (live : Q.live=RootTables.liveBank H G M D rootAt)
    (look : Static Q.widen (Owners.LayoutBit.join (panelBits*DescentPacking.PackedMatch.Local.fields rdx D cap2)) M warmed)
    (keysLow : Q.widen.shift.base+Q.widen.shift.size≤rootAt ∧ Q.widen.apply.base+Q.widen.apply.size≤rootAt)
    (adjacency : (outB).base+(outB).size≤rootAt) (hubs : hubBank.base+hubBank.size≤rootAt)
    (hubRead : ∀j : Fin H,warmed (hubBank.base+j.val)=((Census.hub A vid j).val:Computability.VPVNP.BurstRAM.Word w)) (hubLen : H≤hubBank.size) :
    let post:=(full).image warmed
    (full).Runs warmed ∧ (∀x,x<rootAt→post x=warmed x) ∧
    ∃i : Fin (2^k-1),∃j : DescentAffineColors.Candidate k,∃nz : 0<M,
      let scenery:=pp i j rs
      let topKeys:=topologyWords («M»:=M) s (Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap scenery))
      DescentColonies.seedAt k i=(scannedRows he A.stage).μ ∧ j=DescentAffineColors.code (scannedRows he A.stage).α (scannedRows he A.stage).β ∧
      (∀u,((win i j rs) (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (home u)).2+(color u).toNat) ∧
      Source term (fun h g=>Owners.register (truthFlag choice) (scenery h g)) M post ∧
      Reads (Owners.Board.bank owner (H*chunks G M)) (fun h g=>Owners.render rdx D cap2 panelBits A.cap profile
        (Owners.register (truthFlag choice) (scenery h g))) M post ∧
      DescentHaloPackedRebase.Reads (DonorHeaders.shelf H G M D (L₀).literal (L₀).rankOut) (DonorHeaders.ordValue next) M G post ∧
      DescentHaloPackedRebase.Reads (DonorHeaders.shelf H G M D (L₀).literal (L₀).hubOut) (DonorHeaders.tagValue next tags) M G post ∧
      Mounted {P₀ with roster:=outB} next post G M ∧ (∀v : Fin N,post ((top).base+v.val)=((topKeys v).val:Computability.VPVNP.BurstRAM.Word w)) ∧
      ∀c e,∃v : Fin (s).pairs,v.val=(number c e).val ∧ ∀q : Fin 6,
        let ix:=SixBirths.slot (slot he A gid vid nz c).2 v q
        SixBirths.atom A.z (digit ((s).digit+1) ix.val (post (births+(slot he A gid vid nz c).1.val)).val) ix.val=
        some (A.z,DescentTerminalEpochFlags.encode ((pairProfile choice) ⟨c,e⟩),q.val) := by
  intro post
  obtain ⟨i,j,nz,run,best,muRead,mu,paintRead,paint,wins,rails,original,boards,selector,holes,guarded⟩:=actual
  let firstPass:=RootTables.image H G M D rootAt warmed
  have start_ : rootAt+RootTables.length H G M D≤(L₀).ownerBase:=by
    change _≤DepotRAM.Resident.Dynamic.Placement.first H G M D rootAt;unfold DepotRAM.Resident.Dynamic.Placement.first;omega
  have ceiling : rootAt+RootTables.length H G M D<2^w:=by
    have span:=serialized.owner_end
    have upper:=serialized.order.output
    have after_ : (L₀).ranks.endpoints.base+H*DescentHaloWalkRAM.breadth D≤(L₀).rankOut :=
      (Nat.add_le_add_left serialized.order.sizeEnd _).trans serialized.order.endpoints.2.2
    have old_ : (L₀).ownerBase≤owner:=by
      simp only [Owners.Board.venue,Owners.Board.rom,Nat.add_assoc]
      exact Nat.le_add_right _ _
    omega
  obtain ⟨put,printed,stable,cheap⟩:=RootTables.mount H G M D rootAt warmed ceiling
  have save (x : ℕ) (hx : x<cut) : firstPass x=matched x :=
    (stable x (.inl (hx.trans_le afterOld))).trans (continuation x hx)
  have sorted:=rails.moved (0:Fin rdx) (fun x hx=>save x (hx.trans_le earlier.1))
  have word:=original.moved (fun x hx=>save x (hx.trans_le earlier.2.1))
  obtain ⟨ngh,starts,mask⟩:=RootTables.row_data H G M D rootAt next outB firstPass printed
    (fun h q=>by simpa [Nat.add_assoc,DescentPackedColony.target,DescentHaloWalkRAM.number] using sorted.roster.roster h q)
  have originalHub (u:Fin H) : firstPass (hubBank.base+u.val)=((tags u).toNat:Computability.VPVNP.BurstRAM.Word w):=by
    refine (stable _ (.inl ((Nat.add_lt_add_left (u.isLt.trans_le hubLen) _).trans_le hubs))).trans ((hubRead u).trans ?_)
    by_cases yes:∃v,vid v=u
    · obtain ⟨v,rfl⟩:=yes
      have h:∃v',vid v'=vid v:=⟨v,rfl⟩
      simp only [dite_eq_left h,(vid).injective h.choose_spec,DescentHubBits.live]
    · simp [yes,DescentHubBits.absent A vid u yes]
  have presets : Static Q.widen (Owners.LayoutBit.join (panelBits*DescentPacking.PackedMatch.Local.fields rdx D cap2)) M firstPass:=by
    constructor
    · intro x
      have len:x.val<Q.widen.shift.size:=by simpa [Bank.size,rawFits.widen.shiftBits] using x.isLt
      exact (stable _ (.inl ((Nat.add_lt_add_left len _).trans_le keysLow.1))).trans (look.1 x)
    · intro x
      have len:x.val<Q.widen.apply.size:=by simp [Bank.size,rawFits.widen.applyBits]
      exact (stable _ (.inl ((Nat.add_lt_add_left len _).trans_le keysLow.2))).trans (look.2 x)
  have gated : firstPass Q.gate.base = (if truthFlag choice then (1 : Computability.VPVNP.BurstRAM.Word w) else 0) :=
    (congrArg firstPass flag).trans ((save _ earlier.2.2.1).trans best)
  have masked (x : DescentSIMDLookup.Row H G M) :
      firstPass (Q.live.base+(DescentSIMDLookup.row H G M x).val)=
        ((DescentSIMDLookup.data (fun (_ : Fin H) (_ : Fin G) => (1 : Cell 1)) x).val : Computability.VPVNP.BurstRAM.Word w) :=
    (congrArg (fun bank : Bank => firstPass (bank.base+(DescentSIMDLookup.row H G M x).val)) live).trans (mask x)
  have resident := DepotRAM.Resident.Dynamic.resident_dynamic
    (r:=rdx) («D»:=D) (p:=cap2) (d:=panelBits) («H»:=H) (G:=G) («M»:=M) (w:=w)
    (cap:=A.cap) (profile:=profile) L₀ Q donor (truthFlag choice) (pp i j rs) next tags firstPass serialized rawFits
    (DepotRAM.Resident.Dynamic.Placement.prior H G M D fmt rootAt outB hubBank adjacency hubs)
    hubLen gated masked presets word.read ngh starts originalHub
  obtain ⟨execute,terrain_,owners,ordinal,flags,hold⟩ := resident
  have total:=DepotRAM.Resident.Dynamic.Placement.any H G M D rdx cap2 panelBits A.cap profile w rootAt outB hubBank term serialized warmed
  have final (x : ℕ) (hx : x<cut) : post x=matched x:=(total.2.1 x (hx.trans_le afterOld)).trans (continuation x hx)
  refine ⟨total.1,total.2.1,i,j,nz,mu,paint,wins,terrain_,owners,ordinal,flags,?_,?_,?_⟩
  · exact (rails.moved (0:Fin rdx) (fun x hx=>final x (hx.trans_le earlier.1))).roster
  · intro v;exact (final _ ((Nat.add_lt_add_left v.isLt _).trans_le earlier.2.2.2.1)).trans (boards v)
  · intro c e
    let v := (selector c e).choose
    have facts := (selector c e).choose_spec
    refine ⟨v, facts.1, ?_⟩
    intro q
    let seat := slot he A gid vid nz c
    let ix := SixBirths.slot seat.2 v q
    exact (congrArg (fun val : Computability.VPVNP.BurstRAM.Word w =>
      SixBirths.atom A.z (digit ((s).digit+1) ix.val val.val) ix.val)
      (final _ ((Nat.add_lt_add_left seat.1.isLt _).trans_le earlier.2.2.2.2))).trans (facts.2.2 q)

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
