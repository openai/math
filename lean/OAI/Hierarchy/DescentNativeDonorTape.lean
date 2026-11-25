import OAI.Hierarchy.DescentDonorNativeParts

namespace OAI
/-! # A native chronological read of the physical donor tape for the priced stage register -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentKernelHistory.BitDescription
open DescentRawCablePanel DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentOrdinaryAtomFieldRAM DescentHaloWalkRAM
open Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] nativeParts physicalRows DepotRAM.chip DepotRAM.after DepotRAM.program
  DepotRAM.output packDonor
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→Fin (2^k)→Cell a) (he : 0≤ε)
    (group : J≃Fin G) (hosts : V↪Fin H) (hm : 0<M)
local notation "groups" => group.toEmbedding
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
          (spread group.toEmbedding hosts (terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank))))) i).val:Word w))

local notation "old" => colorPick W.graph W.core home color A.cap
local notation "nativeC" => normBits A.cap gadget.b gadget.C gadget.k
local notation "PairSet" => NativePair W.graph W.core home color A.cap
variable (choice : (A.stage.result he).Choice) (dest : ℕ) (issuedMem : Memory w)
local notation "selected" => (scannedRows he A.stage).profile choice


variable (roster : Fin H→Fin A.degree→Option (Fin H))
    (mounted : ∀(z : J×V) j,roster (hosts z.2) j=(rotor A rank z j).map (fun other=>hosts other.2))
    (hub : V→Bool) (same : ∀e∈W.core,scanColorAt he A.stage (W.graph.src e)=scanColorAt he A.stage (W.graph.dst e)) (lay : Bool)
local notation "flag" => fun j=>if hv : ∃v,hosts v=j then hub hv.choose else false
local notation "P₀" => coloredPack W.graph W.core home color A.cap
local notation "key" => nativeKey W.graph W.core home color A.cap addr same lay
local notation "here" => fun h x=>resolved A.cap profile (panel h) lay x
local notation "adj" => fun h v x=>(peers h v).elim (0,0,0) (fun other=>here other x)
local notation "source" => DescentSharedCableNames.Stage.home A
local notation "S₀" => DescentSharedCableNames.Stage.outgoing A native S ready


include coord named fit winner df edgeOrder sumSize stored mounted in
theorem donor_tape
    (birth : ∀c : C,∀e : Matched T A.cap (thinList home color c) (thickList home color c),
      ∃j : Fin (s).pairs,j.val=(pairNumber (DescentPacking.amount (live T)) (slabPacking T A.cap (thinList home color c) (thickList home color c)).decisions e).val ∧
      ∀q : Fin 6,let ip:=SixBirths.slot (seat c).2 j q
        SixBirths.atom A.stage.z (digit ((s).digit+1) ip.val (issuedMem (dest+(seat c).1.val)).val) ip.val=
          some (A.stage.z,DescentTerminalEpochFlags.encode (selected ⟨c,e⟩),q.val))


    (slots bytes age out : ℕ) (positive : 0<A.cap)
    (books : DepotRAM.Tables6) (inputs : DepotRAM.Fields) (rom : DescentSIMDLookup.Banks) (mem : Memory w)
    (fitCode : DepotRAM.FitsInputs (shapeOf (short:=short) A bytes) books inputs M rom.source.base w)
    (endAt : DescentSIMDLookup.Fits rom (DepotRAM.totalBits (shapeOf (short:=short) A bytes))
      (DepotRAM.outputBits (shapeOf (short:=short) A bytes)) M H G w out)
    (static : DepotRAM.Fixed (shapeOf (short:=short) A bytes) books M mem)
    (sources : DepotRAM.Loaded (shapeOf (short:=short) A bytes) inputs
      (nativeParts A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes) M mem)
    (literal : ∀pin : Cell (DepotRAM.totalBits (shapeOf (short:=short) A bytes)*M) ⊕ Fin (H*chunks G M),∀bit : Fin w,
      wordBits w (mem (fixedAddr rom pin)) bit=wordBits w (fixedWord
        (DepotRAM.output (shapeOf (short:=short) A bytes) A.cap profile gadget.b slots) pin) bit)
    (earlier : rom.dictionary.base+rom.dictionary.size≤rom.source.base ∧ rom.mask.base+rom.mask.size≤rom.source.base) :
    let result:=DepotRAM.after books inputs rom out H G M mem
    (DepotRAM.program books inputs rom out H G M w).Exec mem result (DepotRAM.clocks books inputs H G M) ∧
      (∀row₀ : Row H (G*r*A.cap) (M*(r*A.cap)),result (out+(row H (G*r*A.cap) (M*(r*A.cap)) row₀).val)=
        ((data (fun h j=>packDonor (physicalRows (a:=bytes) (hCode:=age) A S ready native hosts group old lay P₀ key
          (fun z=>hub z.2) slots selected (relative old lay P₀ key) h j)) row₀).val:Word w)) ∧
      (∀a,a<rom.source.base→ result a=mem a) ∧ CheapCode (DepotRAM.program books inputs rom out H G M w) := by
  intro result
  let fmt:=shapeOf (short:=short) A bytes
  let x:=nativeParts (short:=short) A native S ready rank win group hosts hm profile dest issuedMem roster hub lay bytes
  obtain ⟨exec_,printed,low,cheap⟩:=DepotRAM.run fmt books inputs rom out A.cap profile gadget.b slots fitCode endAt x mem static sources literal earlier
  refine ⟨exec_,?_,low,cheap⟩
  have seats:0<fmt.blocks*fmt.cap:=Nat.mul_pos (Nat.two_pow_pos _) positive
  let donors := physicalRows (a:=bytes) (hCode:=age) A S ready native hosts group old lay P₀ key
    (fun z=>hub z.2) slots selected (relative old lay P₀ key)
  apply DepotRAM.flat_read fmt A.cap profile gadget.b slots out x result hm seats donors _ printed
  exact all_seats A native S ready rank win he group hosts hm coord named fit winner df edgeOrder profile b m sumSize stored
    choice dest issuedMem roster mounted hub same lay birth slots bytes age

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
