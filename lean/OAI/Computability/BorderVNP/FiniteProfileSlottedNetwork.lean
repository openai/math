import OAI.Computability.BorderVNP.FiniteProfileSlottedFrame
import OAI.Computability.BorderVNP.PackedRoutingPrefix
import OAI.Computability.BorderVNP.PackedRoutingTeamAgreement

/-! # Genuine seven-word receiving slots on a finite candidate's selected network -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal

open VPVNP BurstRAM RoutingISA RoutingISA.Evaluator TeamContraction ProcessorSlots
open PackedHistoryCircuit Packing RoutingOutputs Crossing CellAddresses CellAddressCircuit CellAddressPhysical
open Packing.Directory Packing.Directory.PrivateBank
open scoped Classical

private theorem private_size_le {C E : ℕ} {A : Type*} [Fintype A] (sc : A → Fin C) (sw : A → ℕ)
    (old : Fin E → Fin C) (gap desc : ℕ) (c : Fin C) :
    DataSlabs.size (Sum.elim (Sum.elim sc id) old)
      (Sum.elim (Sum.elim sw (fun _ : Fin C => gap)) (fun _ : Fin E => desc)) c ≤
        DataSlabs.size sc sw c+gap+E*desc := by
  let cell := Sum.elim sc (id : Fin C → Fin C)
  let width := Sum.elim sw (fun _ : Fin C => gap)
  change DataSlabs.size (Sum.elim cell old) (Sum.elim width (fun _ => desc)) c ≤ _
  rw [←reservedSize sc sw gap c]
  change (∑ i : (A ⊕ Fin C) ⊕ Fin E, if Sum.elim cell old i = c then Sum.elim width (fun _ => desc) i else 0) ≤ _
  rw [Fintype.sum_sum_type]
  apply Nat.add_le_add_left
  calc
    _ ≤ ∑ _i : Fin E, desc := Finset.sum_le_sum fun i _ => by
      simp only [Sum.elim_inr]
      by_cases h : old i = c <;> simp [h]
    _ = E*desc := by simp

variable {R r lit link inner n w o nt ng : ℕ} {Edge : Type} {Q Γ : Type} {K : Type*} [Field K]
variable (G : Wiring R r lit 0 link inner n Edge) (L : Routing.WireLayout (R+1) r link) (u : Fin (R+1))
variable (ext : Exterior R r link → Bool) (bank : Bank w)
variable (lib : Fin 8 → TeamSite.Macro Q Γ nt ng) (ret : FieldProcessor.Returns Q Γ K nt 8) (fuel : ℕ)

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1000000 in
/-- At a reached finite profile, derive all writer operands from actual network
representation, geometry output and native private placement. The slot model includes
the report gap and every retained original private description. -/
noncomputable def FrontReceipt.slottedNetwork {D s p depth k b : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ}
    {σ : Type*} [Fintype σ] (task : SignedTaskArena.Layout) (dir : Directory.Layout)
    (N : Network D P bits) (cell : N.Site → Fin task.cube.cells) (aux : N.Site → ℕ)
    (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin task.cube.cables) (portID : P ↪ Fin p)
    (F : Fields s task.cube.cables p task.cube.cells depth k b σ) (x : σ → Bool)
    (net : Represents N cell aux siteID edgeID portID F x) (ids : ∀ c, (F.cells c).val=c.val)
    (wireFit : ∀ c, guessedSize N cell c+siteSize N cell c aux+suppliedSize N cell c < 2^b)
    (original : Fin dir.entries → N.Site) (live : (Fin dir.teams × Fin dir.sites) ↪ P)
    (liveWidth : ∀ t, bits (live t)=dir.block)
    (other : Arg → Word w) (extra : Fin 81 → Word w) (start pinClock fresh origin gap : ℕ)
    (headerBits : List Bool) (words : Fin o → ℕ) :
    let A := ProfileArena.arena G L ([] : List (Word w))
    let B := ProfileArena.operands G L ([] : List (Word w)) extra Fin.elim0 start u
    let pub := B.bank (core (withDemandBase (task.routeBank A.frame other) A.next) origin task.cube.cables task.cube.cells)
    let fields := G.processorFields u Fin.elim0 ext A.ibase A.hbase A.dense
    let pl := privateLayout A.frame origin task.cube.cables task.cube.cells dir.entries dir.description gap
    let lo := (bases origin task.cube.cables task.cube.cells dir.entries).livePairs
    let sc := Sum.elim (fun x : SuppliedWord N cell => x.1) (id : Fin task.cube.cells → Fin task.cube.cells)
    let sw := Sum.elim (supplyWidth N cell) (fun _ : Fin task.cube.cells => gap)
    let si := reserveID (C:=task.cube.cells) (suppliedID N cell edgeID portID)
    B.Fits w → A.next ≤ fresh → A.next ≤ origin → A.next < 2^w → task.cube.stop < 2^w →
    (extra 41).val=task.cube.hostDirectory → A.next+7*dir.candidates ≤ task.cube.header.header →
    dir.teams=R+1 → dir.processors=r → dir.literal=G.program.length+lit → 0<dir.fields →
    dir.entries*dir.description ≤ dir.teams*dir.processors*(dir.literal/2) → dir.DestinationBounds →
    (∀ c, suppliedSize N cell c+gap+dir.entries*dir.description ≤ task.cube.cellStride) →
    ∀ (z : Returns profileFront pub (TeamSiteEvents.macros lib fuel) bank (processorMemory fields w)),
      FrontReceipt G u ext A.ibase A.hbase A.dense L.header A.broadcastBase pub bank lib ret fuel z A.copied extra
        headerBits pinClock fresh origin words →
      Image F (siteID ∘ original) (portID ∘ live ∘ finProdFinEquiv.symm) x origin (readings z.val.2.2) →
      pl.Fits w (readings z.val.2.2) →
      ∀ mid : Memory w, pl.Image (readings z.val.2.2) dir.entries (readings mid) →
      SlottedWriter task.cube dir (ISA.placement (readings mid) pl.raw) (ISA.placement (readings mid) lo)
        B.layout pub mid A.next (Sum.elim sc (cell ∘ original)) (numbered si)
        (Sum.elim sw (fun _ => dir.description)) := by
  intro A B pub fields pl lo sc sw si fits freshLo originLo nextFit cubeFit host rawRoom dt dp dl active
    tail bound cap z receipt img fit mid place
  have pointers := receipt.slotted_frame G L u ext bank lib ret fuel task dir other extra start pinClock
    fresh origin gap headerBits words fits freshLo originLo nextFit cubeFit host z mid place
  have placed := img.networkPlacement N cell aux siteID edgeID portID F net ids wireFit dir original live liveWidth
    A.frame origin gap (readings z.val.2.2) (readings mid) place fit
  have sep := task.cube.separated
  have headLow : task.cube.header.header ≤ task.cube.packetEnd := by
    unfold CubeArena.Layout.packetEnd CubeHeaderInstall.bankStop CubeHeaderInstall.Inputs.packetBase; omega
  have upto : A.next ≤ task.cube.pairBase := by omega
  have ht : B.layout.stride=A.stride := by
    dsimp only [B,ProfileArena.operands,operandsAtSite,Wiring.pinLayout,A,ProfileArena.arena,Pins.Layout.stride,
      Pins.Layout.offset,StartupArena.stride]
    omega
  have lower : A.frame+112 ≤ A.next := by
    dsimp only [StartupArena.next,StartupArena.hbase,StartupArena.ibase,StartupArena.broadcastBase,StartupArena.dense]; omega
  refine ⟨pointers.1,pointers.2.2,?_,?_,dt,active,tail,Nat.zero_lt_succ _,dp,dl,?_,?_,placed,bound,?_⟩
  · have base : (pub 0).val=A.frame := B.frameBase_word _ fits
    rw [base]; exact lower
  · have len := dir.directory_length_le (ISA.placement (readings mid) pl.raw) (ISA.placement (readings mid) lo)
    omega
  · rw [ht]; exact (show r*A.stride ≤ A.next by change A.frame ≤ A.next; omega).trans upto
  · change A.ibase+A.count ≤ task.cube.pairBase
    exact (show A.ibase+A.count ≤ A.next by unfold StartupArena.next StartupArena.hbase; omega).trans upto
  · intro c
    apply (private_size_le _ _ _ gap dir.description c).trans
    simpa only [dataSlabs_size] using cap c

end FiniteDiagonal

end BorderVNP
end Computability
end OAI
