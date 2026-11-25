import OAI.Hierarchy.DescentPackedMatchStageReturn
import OAI.Hierarchy.DescentOrdinaryCountScan

namespace OAI
/-! # The measured packed matching table gives the selector's true pair count -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentStageEdgeReceipt DescentSIMDLookup DescentPackedProfileWindow
open DescentTerminalEpochDecoder DescentKernelHistory.BitDescription DescentTerminalEpochFlags
open Computability.VPVNP.BurstRAM DescentSixParty.StarKeys Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k t short a H G M w : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {gadget : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S t)
variable (rank : (J×V)↪ℕ) (win : J×V→ Fin (2^k)→ Cell a) (he : 0≤ε) (groups : J↪Fin G) (hosts : V↪Fin H) (hm : 0< M)
local notation "keyCount" => 2^(k+1)
local notation "N" => (keyCount*H)*chunks G M
local notation "C" => ScanColonies he A.stage
local notation "panel" => terrain (short:=short) A native S ready (cableNames k rank) win (rotor A rank)
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "ord" => slot he A groups hosts hm
variable (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val=1+2*heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2+(scanColorAt he A.stage u).toNat)
    (df : A.degree<2^short) (profile : ℕ)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile
local notation "real" => spread groups hosts panel
local notation "descriptors" => Gather.flat (Gather.descriptorInputs (K:=keyCount) s A.cap real)
local notation "ks" => topologyWords (M:=M) s descriptors

include hm coord named fit winner df in
theorem topology_count : (∑i : Fin N,chunkCount s M (ks i))=Fintype.card (scannedRows he A.stage).pairs :=by
  classical
  let e:=ord
  let val:Fin N × Fin M→ℕ:=fun p=>(laneCounts s M (ks p.1) p.2).val
  have counts:=measured A native S ready rank win he groups hosts hm coord named fit winner df profile
  have zero_ (p : Fin N × Fin M) (_ : p∈Finset.univ) (absent : p∉Finset.univ.map e) : val p=0 :=by
    apply counts.hole p.1 p.2
    intro c same
    exact absent (Finset.mem_map.mpr ⟨c,Finset.mem_univ _,same⟩)
  have count : (∑p : Fin N × Fin M,val p)=∑c,countIn he A c :=by
    rw [←Finset.sum_subset (Finset.subset_univ (Finset.univ.map e)) zero_,Finset.sum_map]
    exact Finset.sum_congr rfl (fun c _=>counts.live c)
  calc
    (∑i : Fin N,chunkCount s M (ks i))=∑p : Fin N × Fin M,val p:=(Fintype.sum_prod_type val).symm
    _ = ∑c,countIn he A c:=count
    _ = Fintype.card (scannedRows he A.stage).pairs:=Fintype.card_sigma.symm

include hm coord named fit winner df in
theorem topology_scalar (src : ProtocolRAM.Bank) (base : ℕ) (m : Memory w) (prior : src.Fits w base)
    (rows : N≤ src.size) (observed : ∀i : Fin N,m (src.base+i.val)=((ks i).val:Computability.VPVNP.BurstRAM.Word w))
    (space : DescentOrdinaryCountScan.endAddress ((s).outputBits*M) base N<2^w) :
    let func:=chunkCount s M
    let o:=DescentOrdinaryCountScan.output src func base N m
    (DescentOrdinaryCountScan.program w src func base N).Exec m o
      (DescentOrdinaryCountScan.clock ((s).outputBits*M) N) ∧
    o (DescentOrdinaryCountScan.address ((s).outputBits*M) base N)=
      ((Fintype.card (scannedRows he A.stage).pairs):Computability.VPVNP.BurstRAM.Word w) :=by
  intro func o
  refine ⟨(DescentOrdinaryCountScan.run src func base N m prior space).1,?_⟩
  rw [←topology_count A native S ready rank win he groups hosts hm coord named fit winner df profile]
  simpa only [Nat.cast_sum] using DescentOrdinaryCountScan.read src func base N m ks prior rows observed space

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
