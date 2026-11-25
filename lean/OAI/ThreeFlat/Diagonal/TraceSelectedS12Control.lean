import OAI.ThreeFlat.Diagonal.InitialMetadataActual
import OAI.ThreeFlat.Diagonal.PhysicalNodeArchiveRun
import OAI.ThreeFlat.Diagonal.NavigationRootPublication
import OAI.ThreeFlat.RAM.HistoryInitialControl

namespace OAI
/-! # Selected initial control fields from the native S44 and S49 publishers -/
namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM HistoryInitialSeed Computability.VPVNP.Compression NavigationNodeRows
open scoped Classical Fin.CommRing BigOperators
variable {W t : ℕ} {V : Type} {layers : List Layers}

/-- The four coordinates of the actual node. Its pair count is the mass in the selected charge column. -/
def selectedSeedSite (a : NodeArchive) (program : Program layers) (before : Memory W)
    (i : Fin layers.length) (j : Fin (layers.get i).actual.count) (lanes : ℕ) : HistoryInitialSeed.Site :=
  ⟨(layers.get i).actual.first+j.val,j.val%lanes,j.val/lanes,
    2*(program.data i).cost a.banks (prior a (decrement a (state a program before i.val))) j 1⟩

theorem selectedSeedSite_coordinates {k : ℕ} (a : NodeArchive) (program : Program layers) (before : Memory W)
    (i : Fin layers.length) (j : Fin (layers.get i).actual.count) (stage : Fin k) (lane : BitWord k)
    (address : j.val=stage.val*(2^k)+(finFunctionFinEquiv lane).val) :
    let z:=selectedSeedSite a program before i j (2^k)
    z.lane=(finFunctionFinEquiv lane).val ∧ z.stage=stage.val := by
  have digits : (finFunctionFinEquiv lane).val<2^k:=(finFunctionFinEquiv lane).isLt
  dsimp only [selectedSeedSite]
  rw [address,Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt digits,Nat.mul_comm stage.val (2^k),
    Nat.mul_add_div (Nat.two_pow_pos k),Nat.div_eq_of_lt digits]
  exact ⟨rfl,Nat.add_zero stage.val⟩

/-- The native S44 external count is clipped by the global endpoint count
precisely on cursor stage zero. This is the count used before any group packing. -/
theorem selectedSeedSite_count (a : NodeArchive) (program : Program layers) (before : Memory W)
    (i : Fin layers.length) (j : Fin (layers.get i).actual.count) (globalCount low lanes : ℕ)
    (kind : (layers.get i).actual.kind=0) (none : (layers.get i).actual.childCount=0)
    (live : 0<lanes) (bankLanes : a.banks.lanes=lanes)
    (bankPairs : a.banks.totalPairs=globalCount) (perLane : a.banks.perLanePairs=2^low) :
    let z:=selectedSeedSite a program before i j lanes
    z.extPins=(if z.stage=0 then 2*TraceSuffix.pairs globalCount low z.lane else 0) := by
  let h:=prior a (decrement a (state a program before i.val))
  have empty : (∑ x, h ((program.data i).child j x) (1:Fin 2))=0 := by
    apply Finset.sum_eq_zero
    intro x _
    exact False.elim (by have:=x.isLt;omega)
  by_cases active : j.val<lanes
  · have time:=Nat.div_eq_of_lt active
    have lane:=Nat.mod_eq_of_lt active
    have kindAt : (layers[i.val]'i.isLt).actual.kind=0 := kind
    simp [selectedSeedSite,LayerData.cost,kindAt,bankLanes,bankPairs,perLane,active,time,lane,
      TraceSuffix.pairs,show (∑ x, prior a (decrement a (state a program before i.val))
        ((program.data i).child j x) (1:Fin 2))=0 from empty,Nat.min_comm]
  · have time : j.val/lanes≠0:=by have:=Nat.div_pos (Nat.le_of_not_gt active) live;omega
    simp [selectedSeedSite,LayerData.cost,bankLanes,active,time,
      show (∑ x, prior a (decrement a (state a program before i.val))
        ((program.data i).child j x) (1:Fin 2))=0 from empty]

theorem published_seed_kernel (a : NodeArchive) (program : Program layers) (before now : Memory W)
    {budget : ℕ} (room : RunBounds W a layers budget) (address : ℕ)
    (stableAt : ∀ i : Fin 5,stable a layers (address+i.val))
    (frame : ∀ i : Fin 5, now (address+i.val)=state a program before layers.length (address+i.val)) :
    ∀ i : Fin 5,now (address+i.val)=before (address+i.val) :=
  fun i=>(frame i).trans (final_input a program before room _ (stableAt i))

/-- The complete two-field S44 node and two-field S49 cursor readout after
the chronological node program. Subsequent framing is only over the selected rows. -/
theorem selectedSeed_control (a : NodeArchive) (program : Program layers) (before : Memory W)
    {budget : ℕ} (space : RunBounds W a layers budget) (order : Chronological layers)
    (i : Fin layers.length) (j : Fin (layers.get i).actual.count) (archive : Archive)
    (row : Fin archive.initialSites) (ordinal : j.val=row.val)
    (seed : (layers.get i).actual=archive.seedLayer)
    (G : LiftedSlots V archive.initialDegree (BitWord t)) (base : V≃Fin archive.axes)
    (width : SlotImage.Edge V (BitWord t) archive.initialDegree→ℕ) (metadata now : Memory W)
    (s49 : archive.InitialNodeMetadata G base width metadata) (A : HistoryInitialSeed.Layout)
    (base44 : A.nodes=a.banks.nodes)
    (read44 : ∀ c : Fin 8,now (A.nodes+8*((layers.get i).actual.first+j.val)+c.val)=
      state a program before layers.length (A.nodes+8*((layers.get i).actual.first+j.val)+c.val))
    (read49 : ∀ c : Fin 5,now (archive.initialRecords+5*row.val+c.val)=metadata (archive.initialRecords+5*row.val+c.val))
    (cursor : (now A.cursor).val=(layers.get i).actual.first+j.val+1)
    (cursorSafe : SeedSafe A.cursor 1 A.ctrl)
    (nodeSafe : SeedSafe (A.nodes+8*((layers.get i).actual.first+j.val)) 8 A.ctrl)
    (kernelSafe : SeedSafe (archive.initialRecords+5*row.val) 5 A.ctrl)
    (cursorFit : A.cursor<2^W) (nodeFit : A.nodes+8*((layers.get i).actual.first+j.val)+7<2^W)
    (kernelFit : archive.initialRecords+5*row.val+4<2^W)
    (rowFit : row.val<2^W)
    (extFit : (selectedSeedSite a program before i j archive.remainingLanes).extPins<2^W) :
    ControlImage A (selectedSeedSite a program before i j archive.remainingLanes)
      (archive.initialRecords+5*row.val) now := by
  let z:=selectedSeedSite a program before i j archive.remainingLanes
  let k:=archive.initialRecords+5*row.val
  have baseKernel : (layers.get i).actual.kernels=archive.initialRecords :=
    (congrArg Layer.kernels seed).trans rfl
  have pointer:=congrArg Fin.val (final_node_word a program before space order i j (5:Fin 8))
  have seen:=(congrArg Fin.val (read44 (5:Fin 8))).trans (by simpa only [base44] using pointer)
  change (now (A.nodes+8*((layers.get i).actual.first+j.val)+5)).val=
    (((layers.get i).actual.kernels+j.val*5:ℕ):Word W).val at seen
  rw [baseKernel,ordinal,Nat.mul_comm row.val 5,Fin.val_cast_of_lt (by omega)] at seen
  have count:=congrArg Fin.val (final_node_word a program before space order i j (7:Fin 8))
  have countAt:=(congrArg Fin.val (read44 (7:Fin 8))).trans (by simpa only [base44] using count)
  change (now (A.nodes+8*z.index+7)).val=(z.extPins:Word W).val at countAt
  rw [Fin.val_cast_of_lt extFit] at countAt
  have coord (c : Fin 5) : now (k+c.val)=
      ((![archive.seed,row.val,0,row.val%archive.remainingLanes,row.val/archive.remainingLanes] : Fin 5→ℕ) c:Word W) := by
    rw [show k=archive.initialRecords+5*row.val from rfl,read49]
    simpa only [Archive.seedWords,Nat.mul_comm row.val 5,Nat.add_assoc] using s49.kernel row c
  have low:=congrArg Fin.val (coord (3:Fin 5))
  have high:=congrArg Fin.val (coord (4:Fin 5))
  change (now (k+3)).val=((row.val%archive.remainingLanes:ℕ):Word W).val at low
  change (now (k+4)).val=((row.val/archive.remainingLanes:ℕ):Word W).val at high
  rw [Fin.val_cast_of_lt ((Nat.mod_le ..).trans_lt rowFit)] at low
  rw [Fin.val_cast_of_lt ((Nat.div_le_self ..).trans_lt rowFit)] at high
  refine ⟨cursor,?_,?_,?_,countAt,cursorSafe,nodeSafe,kernelSafe,cursorFit,nodeFit,kernelFit⟩
  · simpa only [selectedSeedSite,ordinal] using seen
  · simpa only [selectedSeedSite,ordinal] using low
  · simpa only [selectedSeedSite,ordinal] using high

end ThreeFlat.Diagonal.NavigationPass.NodePublication

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows
variable {F : Type*} [Field F] [Fintype F] {W p H J : ℕ} {B : TickActiveROM.Layout}
    {fit : Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock}

theorem prepared_highArchive (x : TickActiveROM.CellInput B clock fit)
    (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (nodes : Nodes (parameterArchive pars degree stages W)) (teams : ℕ) (layers : List Layers)
    (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (original prepared : Memory W)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers original groups prepared)
    (small : (parameterArchive pars degree stages W).current<2^W)
    (headers : B.bounds+4≤2^W) (highB : B.bounds+4≤TickWorkspace.base pars.age 43)
    (highRequests : B.auxRequest+8*B.bits≤TickWorkspace.base pars.age 43)
    (addr : ℕ) (zone : (TickWorkspace.base pars.age 43≤addr ∧ addr<TickWorkspace.base pars.age 45) ∨
      TickWorkspace.base pars.age 49≤addr) : prepared addr=original addr := by
  let a:=parameterArchive pars degree stages W
  obtain ⟨mid,out,branch,pack,rfl⟩:=done
  have h43 : TickWorkspace.base pars.age 43≤addr := by
    rcases zone with h|h
    · exact h.1
    · have step : TickWorkspace.base pars.age 43≤TickWorkspace.base pars.age 49 := by
        unfold TickWorkspace.base
        omega
      exact step.trans h
  rw [filled_high x out .evaluate addr headers (highB.trans h43) (highRequests.trans h43)]
  exact read_retained a nodes teams layers groups original mid out branch pack small addr
    (parameter_retained pars degree stages W sizes addr (Or.inr zone))


end ThreeFlat.Diagonal.NavigationPass.RootArchive

end OAI
