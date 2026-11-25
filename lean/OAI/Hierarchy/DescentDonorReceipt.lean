import OAI.Hierarchy.DescentDonorDepot

namespace OAI
/-! # Exact present donor from the physically issued old and new ports -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentKernelHistory.BitDescription
open DescentRawCablePanel DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option maxHeartbeats 1000000
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "K" => 2^(k+1)
local notation "r" => 2^k
local notation "p" => 2*A.cap
local notation "names" => cableNames k rank
local notation "peers" => rotor A rank
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "C" => ScanColonies he A.stage
local notation "panel" => terrain (short:=short) A native S ready names win peers
local notation "real" => spread groups hosts panel
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀u : W.graph.Site,(win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (edgeOrder : ∀e f,native e<native f ↔ originalId W.graph.Edge e<originalId W.graph.Edge f)
    (profile : ℕ)
local notation "s" => shape r A.degree p profile
local notation "fieldsAt" => Gather.flat (Gather.descriptorInputs («K»:=K) s A.cap real)
local notation "seat" => slot he A groups hosts hm
variable (b : ℕ) (m : Memory w) (sumSize : (shape (2^k) A.degree (2*A.cap) profile).outputBits*M≤w)
    (stored : ∀i : Fin ((2^(k+1)*H)*chunks G M),
      m (b+i.val)=((topologyWords (M:=M) (shape (2^k) A.degree (2*A.cap) profile)
        (Gather.flat (Gather.descriptorInputs («K»:=2^(k+1)) (shape (2^k) A.degree (2*A.cap) profile) A.cap
          (spread groups hosts (terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank))))) i).val:Word w))
local notation "old" => colorPick W.graph W.core home color A.cap
local notation "nativeC" => normBits A.cap gadget.b gadget.C gadget.k
local notation "PairSet" => NativePair W.graph W.core home color A.cap
variable (choice : (A.stage.result he).Choice) (dest : ℕ) (issuedMem : Memory w)
local notation "selected" => (scannedRows he A.stage).profile choice


variable (roster : Fin H→Fin A.degree→Option (Fin H))
    (physical : ∀z j v,rotor A rank z j=some v → roster (hosts z.2) j=some (hosts v.2))
    (hub : V→Bool) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "flag" => fun j=>if hv : ∃v,hosts v=j then hub hv.choose else false
local notation "P₀" => coloredPack W.graph W.core home color A.cap
local notation "key" => nativeKey W.graph W.core home color A.cap addr same lay
local notation "here" => fun h x=>resolved A.cap profile (panel h) lay x
local notation "adj" => fun h v x=>(peers h v).elim (0,0,0) (fun other=>here other x)
local notation "source" => DescentSharedCableNames.Stage.home A
local notation "S₀" => DescentSharedCableNames.Stage.outgoing A native S ready

include coord named fit winner df edgeOrder physical sumSize stored in
/-- The numerical inputs are the original encoded signed raster, the funded
old-owner lookup, the genuine two-hop roster, and the newly emitted six-party
selector tape at the selected source. Its output is the chronological donor. -/
theorem depot_at
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))

    (q : DescentSharedCableNames.Stage.Positive A) (slots bytes age : ℕ) :
    let u:=W.graph.src q.val
    let h:=A.pos u
    let raw:=(fun j=>DescentSignedCableCodec.encode (DescentSharedCableNames.Stage.signedPanel A native S ready names (source u) j))
    let seen:=readWalk roster (hosts h.2) flag
    let supply:=measureSupply (short:=short) A native S ready rank win he groups hosts hm profile dest issuedMem q
    depot bytes nativeC slots gadget.b A.cap profile (panel h) raw seen (here h) (adj h) supply lay (A.block u) (S₀ q)=
      measuredDonor (hCode:=age) A S ready old lay P₀ key (fun z=>hub z.2) slots selected (relative old lay P₀ key) q := by
  intro u h raw seen supply
  have value:=donor_read A native S ready rank win he coord named fit winner df edgeOrder profile same lay hosts roster physical hub q slots bytes age selected
  have amount:=DescentSharedCableNames.Stage.source_grains A native S ready names q
  have active : DescentSharedCableNames.Stage.sourceGrains raw (S₀ q)≠0 := by rw [show DescentSharedCableNames.Stage.sourceGrains raw (S₀ q)=A.grainCount q.val from amount];exact q.property.ne'
  have destPeer:=source_peer A native S ready rank q
  have width_:=funext (supply_read A native S ready rank win he groups hosts hm coord named fit winner df edgeOrder profile b m sumSize stored choice dest issuedMem birth q)
  unfold depot
  rw [ite_eq_right active,destPeer]
  dsimp only [supply]
  rw [width_]
  exact value

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
