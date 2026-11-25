import OAI.ThreeFlat.RAM.HistoryStageSetup
import OAI.ThreeFlat.Diagonal.NativeNavigationAdmission
import OAI.ThreeFlat.Diagonal.TraceSelectedS12Control

namespace OAI
/-! # The selection in the successful cursor slot determines the initial S44 row -/
namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression PrivateRAM RAM PhysicalStage NodePublication NavigationNodeRows HistoryInitialSeed
open scoped Fin.CommRing Classical
variable {W d l : ℕ} {F : Type} [Field F] [Fintype F] {X : State d l}
    {start pay : X.Site→ℕ} {budget : ℕ}

private theorem first_columns (n : NodeArchive) (m : Memory W) (O : X.ArchiveSites) (data : LayerData O.layer)
    (parent : Parent) (owners : Fin O.layer.count→ℕ) (tail : List NodeRow)
    (source : State.SeedRows O data n.banks start pay)
    (space : RunBounds W n (records (⟨O.layer,parent,data,owners⟩::tail)) budget)
    (order : Chronological (records (⟨O.layer,parent,data,owners⟩::tail))) (v : X.Site) :
    let xs:=(⟨O.layer,parent,data,owners⟩:NodeRow)::tail
    let out:=state n (program xs) m (records xs).length
    out (n.banks.nodes+8*O.id v+5)=((O.layer.kernels+(O.ord v).val*5:ℕ):Word W) ∧
    out (n.banks.nodes+8*O.id v+7)=((2*pay v:ℕ):Word W) := by
  let xs:=(⟨O.layer,parent,data,owners⟩:NodeRow)::tail
  let i : Fin (records xs).length:=⟨0,by simp [records,xs]⟩
  have one:=final_node_word n (program xs) m space order i (O.ord v) (5:Fin 8)
  have two:=final_node_word n (program xs) m space order i (O.ord v) (7:Fin 8)
  dsimp only
  refine ⟨one,?_⟩
  let ord:=prior n (decrement n (state n (program xs) m 0))
  have payAt : data.cost n.banks ord (O.ord v) 1=pay v := by simpa using source ord v 1
  change _=((2*data.cost n.banks ord (O.ord v) 1:ℕ):Word W) at two
  rwa [payAt] at two

omit [Fintype F] in
theorem Selection.seed_columns {r : Run F X} {C : r.Charges} {O : X.ArchiveSites} {seed : LayerData O.layer}
    {n : NodeArchive} {a : RootArchive} {rows : List Layers} {m out : Memory W}
    (s : Selection r C O seed start pay n a rows budget m)
    (ran : out=state n (program (r.archiveList s.history C O s.path seed)) m rows.length)
    (v : X.Site) :
    out (n.banks.nodes+8*O.id v+5)=((O.layer.kernels+(O.ord v).val*5:ℕ):Word W) ∧
    out (n.banks.nodes+8*O.id v+7)=((2*pay v:ℕ):Word W) := by
  have done:=s.source.room
  have first:=s.source.initial
  have chrono:=archive_chronological r s.history C O s.path seed
  have rowsLength := congrArg List.length s.layout
  rw [ran, ←rowsLength]
  cases r <;> exact first_columns n m O seed _ _ _ first done chrono v

omit [Fintype F] in
/-- Only the actual final node selection, original S49 kernel, S18 cursor and
the two framed row reads are needed at a selected site. -/
theorem Selection.seedControl {r : Run F X} {C : r.Charges} {O : X.ArchiveSites} {seed : LayerData O.layer}
    {n : NodeArchive} {a : RootArchive} {layers : List Layers} {m out now : Memory W}
    (s : Selection r C O seed start pay n a layers budget m)
    (ran : out=state n (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (archive : Archive) {V : Type} {k : ℕ} (G : LiftedSlots V archive.initialDegree (Computability.VPVNP.Compression.BitWord k))
    (base : V≃Fin archive.axes) (width : SlotImage.Edge V (Computability.VPVNP.Compression.BitWord k) archive.initialDegree→ℕ)
    (seedMem : Memory W) («meta» : archive.InitialNodeMetadata G base width seedMem) (v : X.Site) (j : Fin archive.initialSites)
    (rank : (O.ord v).val=j.val) (kernelBase : O.layer.kernels=archive.initialRecords)
    (A : HistoryInitialSeed.Layout) (nodeBase : A.nodes=n.banks.nodes)
    (stays : ∀ col : Fin 8,now (A.nodes+8*O.id v+col.val)=out (A.nodes+8*O.id v+col.val))
    (keep : ∀ col : Fin 5,now (archive.initialRecords+5*j.val+col.val)=seedMem (archive.initialRecords+5*j.val+col.val))
    (cursor : (now A.cursor).val=O.id v+1)
    (low : SeedSafe A.cursor 1 A.ctrl) (nodeSafe : SeedSafe (A.nodes+8*O.id v) 8 A.ctrl)
    (ptrSafe : SeedSafe (archive.initialRecords+5*j.val) 5 A.ctrl)
    (cf : A.cursor<2^W) (nf : A.nodes+8*O.id v+7<2^W) (kf : archive.initialRecords+5*j.val+4<2^W)
    (jf : j.val<2^W) (ef : 2*pay v<2^W) :
    ControlImage A ⟨O.id v,j.val%archive.remainingLanes,j.val/archive.remainingLanes,2*pay v⟩
      (archive.initialRecords+5*j.val) now := by
  have h:=s.seed_columns ran v
  have pointer := stays (5 : Fin 8)
  change now (A.nodes+8*O.id v+5)=out (A.nodes+8*O.id v+5) at pointer
  have extent := stays (7 : Fin 8)
  change now (A.nodes+8*O.id v+7)=out (A.nodes+8*O.id v+7) at extent
  have readPointer : out (A.nodes+8*O.id v+5)=((O.layer.kernels+(O.ord v).val*5:ℕ):Word W) := by
    rw [nodeBase]
    exact h.1
  have readExtent : out (A.nodes+8*O.id v+7)=((2*pay v:ℕ):Word W) := by
    rw [nodeBase]
    exact h.2
  have p:=congrArg Fin.val (pointer.trans readPointer)
  have e:=congrArg Fin.val (extent.trans readExtent)
  rw [kernelBase,rank,Nat.mul_comm j.val 5,Fin.val_cast_of_lt (by omega)] at p
  rw [Fin.val_cast_of_lt ef] at e
  have k (col : Fin 5) : now (archive.initialRecords+5*j.val+col.val)=
      ((![archive.seed,j.val,0,j.val%archive.remainingLanes,j.val/archive.remainingLanes] : Fin 5→ℕ) col:Word W) := by
    rw [keep]
    simpa only [Archive.seedWords,Nat.mul_comm j.val 5,Nat.add_assoc] using «meta».kernel j col
  have lane:=congrArg Fin.val (k 3)
  have stage:=congrArg Fin.val (k 4)
  change _=((j.val%archive.remainingLanes:ℕ):Word W).val at lane
  change _=((j.val/archive.remainingLanes:ℕ):Word W).val at stage
  rw [Fin.val_cast_of_lt ((Nat.mod_le ..).trans_lt jf)] at lane
  rw [Fin.val_cast_of_lt ((Nat.div_le_self ..).trans_lt jf)] at stage
  exact ⟨cursor,p,lane,stage,e,low,nodeSafe,ptrSafe,cf,nf,kf⟩

/-- Witness of the actual selected S44/S49 publications carried by a successful cursor slot. -/
inductive CursorSeed (F : Type) [Field F] [Fintype F] (W T depth : ℕ) :
    HistoryInitialSeed.Layout → HistoryInitialSeed.Site → ℕ → Memory W → Prop where
  | published {d l budget : ℕ} {X : State d l} {start pay : X.Site→ℕ} {r : Run F X} {C : r.Charges} {O : X.ArchiveSites} {seed : LayerData O.layer}
    {n : NodeArchive} {a : RootArchive} {layers : List Layers} {m out now : Memory W}
    (s : Selection r C O seed start pay n a layers budget m)
    (ran : out=state n (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (archive : Archive) {V : Type} {k : ℕ} (G : LiftedSlots V archive.initialDegree (Computability.VPVNP.Compression.BitWord k))
    (base : V≃Fin archive.axes) (width : SlotImage.Edge V (Computability.VPVNP.Compression.BitWord k) archive.initialDegree→ℕ)
    (seedMem : Memory W) («meta» : archive.InitialNodeMetadata G base width seedMem) (v : X.Site) (j : Fin archive.initialSites)
    (rank : (O.ord v).val=j.val) (kernelBase : O.layer.kernels=archive.initialRecords)
    (A : HistoryInitialSeed.Layout) (nodeBase : A.nodes=n.banks.nodes)
    (stays : ∀ col : Fin 8,now (A.nodes+8*O.id v+col.val)=out (A.nodes+8*O.id v+col.val))
    (keep : ∀ col : Fin 5,now (archive.initialRecords+5*j.val+col.val)=seedMem (archive.initialRecords+5*j.val+col.val))
    (cursor : (now A.cursor).val=O.id v+1)
    (low : SeedSafe A.cursor 1 A.ctrl) (nodeSafe : SeedSafe (A.nodes+8*O.id v) 8 A.ctrl)
    (ptrSafe : SeedSafe (archive.initialRecords+5*j.val) 5 A.ctrl)
    (cf : A.cursor<2^W) (nf : A.nodes+8*O.id v+7<2^W) (kf : archive.initialRecords+5*j.val+4<2^W)
    (jf : j.val<2^W) (ef : 2*pay v<2^W)
    (kind : O.layer.kind=0) (positive : 0<archive.remainingLanes)
    (bankLanes : n.banks.lanes=archive.remainingLanes)
    (total : n.banks.totalPairs=T) (perLane : n.banks.perLanePairs=2^depth) :
      CursorSeed F W T depth A ⟨O.id v,j.val%archive.remainingLanes,j.val/archive.remainingLanes,2*pay v⟩
        (archive.initialRecords+5*j.val) now

theorem CursorSeed.control {T depth : ℕ} {A : HistoryInitialSeed.Layout} {z : HistoryInitialSeed.Site}
    {kernel : ℕ} {now : Memory W} (h : CursorSeed F W T depth A z kernel now) : ControlImage A z kernel now := by
  cases h with
  | published s ran archive G base width seedMem metadata v j rank kernelBase A nodeBase stays keep cursor
      low nodeSafe ptrSafe cf nf kf jf ef kind positive bankLanes total perLane =>
    exact s.seedControl ran archive G base width seedMem metadata v j rank kernelBase A nodeBase stays keep cursor
      low nodeSafe ptrSafe cf nf kf jf ef

theorem CursorSeed.firstID {T depth : ℕ} {A : HistoryInitialSeed.Layout} {z : HistoryInitialSeed.Site}
    {kernel : ℕ} {now : Memory W} (h : CursorSeed F W T depth A z kernel now) (first : z.stage=0) :
    z.index=z.lane := by
  cases h with
  | published s ran archive G base width seedMem metadata v j rank kernelBase A nodeBase stays keep cursor
      low nodeSafe ptrSafe cf nf kf jf ef kind positive bankLanes total perLane =>
    change j.val/archive.remainingLanes=0 at first
    have digits:=Nat.mod_add_div j.val archive.remainingLanes
    rw [first,Nat.mul_zero,Nat.add_zero] at digits
    change _+_=j.val%archive.remainingLanes
    rw [s.zero,rank,Nat.zero_add,digits]

omit [Fintype F] in
theorem Selection.seed_count {r : Run F X} {C : r.Charges} {O : X.ArchiveSites} {seed : LayerData O.layer}
    {n : NodeArchive} {a : RootArchive} {layers : List Layers} {m : Memory W}
    (s : Selection r C O seed start pay n a layers budget m) (v : X.Site)
    (T low lanes : ℕ) (kind : O.layer.kind=0) (positive : 0<lanes)
    (bankLanes : n.banks.lanes=lanes) (total : n.banks.totalPairs=T) (perLane : n.banks.perLanePairs=2^low) :
    let ordinal:=(O.ord v).val
    2*pay v=(if ordinal/lanes=0 then 2*TraceSuffix.pairs T low (ordinal%lanes) else 0) := by
  let j:=(O.ord v).val
  have cost : seed.cost n.banks (fun _ _=>0) (O.ord v) 1=pay v := by simpa using s.source.initial (fun _ _=>0) v 1
  by_cases live : j<lanes
  · have lg:=Nat.mod_eq_of_lt live
    have tm:=Nat.div_eq_of_lt live
    simp [←cost,LayerData.cost,kind,bankLanes,total,perLane,TraceSuffix.pairs,show (O.ord v).val=j from rfl,live,lg,tm,Nat.min_comm]
  · have tm:j/lanes≠0:=by have:=Nat.div_pos (Nat.le_of_not_gt live) positive;omega
    simp [←cost,LayerData.cost,kind,bankLanes,show (O.ord v).val=j from rfl,live,tm]

theorem CursorSeed.count {T depth : ℕ} {A : HistoryInitialSeed.Layout} {z : HistoryInitialSeed.Site}
    {kernel : ℕ} {now : Memory W} (h : CursorSeed F W T depth A z kernel now) :
    z.extPins=(if z.stage=0 then 2*TraceSuffix.pairs T depth z.lane else 0) := by
  cases h with
  | published s ran archive G base width seedMem metadata v j rank kernelBase A nodeBase stays keep cursor
      low nodeSafe ptrSafe cf nf kf jf ef kind positive bankLanes total perLane =>
    have h:=s.seed_count v T depth archive.remainingLanes kind positive bankLanes total perLane
    simpa only [rank] using h

omit [Fintype F] in
/-- The S44/S43 words of any genuine archived stage in the successful selection,
observed in the actual state delivered by the node publisher. -/
theorem Selection.stage_directory {r : Run F X} {C : r.Charges} {O : X.ArchiveSites} {seed : LayerData O.layer}
    {n : NodeArchive} {a : RootArchive} {layers : List Layers} {m out : Memory W}
    (s : Selection r C O seed start pay n a layers budget m)
    (ran : out=state n (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (q : NodeRow) (occurs : q∈r.archiveList s.history C O s.path seed) (j : Fin q.layer.count) :
    HistoryStageSetup.DirectoryRow n.banks q.layer j out := by
  let xs:=r.archiveList s.history C O s.path seed
  obtain ⟨i,atRow⟩:=every_view xs q occurs
  subst q
  have rowsLength := congrArg List.length s.layout
  rw [ran, ←rowsLength]
  exact HistoryStageSetup.published_directory n (program xs) m s.source.room
    (archive_chronological r s.history C O s.path seed) i j


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows
variable {F : Type*} [Field F] [Fintype F] {W p H J : ℕ} {B : TickActiveROM.Layout}
    {fit : Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock}

/-- Navigation publication followed by request initialization preserves all three actual
source zones for stage contraction: the stage heap, S43/S44 rows and initial S49 metadata. -/
theorem prepared_stage_cell (x : TickActiveROM.CellInput B clock fit)
    (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (nodes : Nodes (parameterArchive pars degree stages W)) (teams : ℕ) (layers : List Layers)
    (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (original prepared : Memory W)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers original groups prepared)
    (small : (parameterArchive pars degree stages W).current<2^W)
    (headers : B.bounds+4≤2^W) (highB : B.bounds+4≤TickWorkspace.base pars.age 20)
    (highRequests : B.auxRequest+8*B.bits≤TickWorkspace.base pars.age 20)
    (addr : ℕ) (zone : (TickWorkspace.base pars.age 20≤addr ∧ addr<TickWorkspace.base pars.age 40) ∨
      (TickWorkspace.base pars.age 43≤addr ∧ addr<TickWorkspace.base pars.age 45) ∨ TickWorkspace.base pars.age 49≤addr) :
    prepared addr=original addr := by
  obtain ⟨mid,out,branch,pack,rfl⟩:=done
  have h : TickWorkspace.base pars.age 20≤addr := by
    rcases zone with h|h|h
    · exact h.1
    · exact (Nat.le_add_right ..).trans ((TickWorkspace.apart (u:=pars.age) (by decide : 20<43)).trans h.1)
    · exact (Nat.le_add_right ..).trans ((TickWorkspace.apart (u:=pars.age) (by decide : 20<49)).trans h)
  rw [filled_high x out .evaluate addr headers (highB.trans h) (highRequests.trans h)]
  exact read_retained _ nodes teams layers groups original mid out branch pack small addr
    (parameter_retained pars degree stages W sizes addr zone)


end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.RootArchive
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.TickPhysicalABI
variable {F : Type} [Field F] [Fintype F] {W p H J : ℕ} {B : TickActiveROM.Layout}
    {fit : Contraction.Fits (TickWeightedBank.shape F p H J) W} {clock : TickChronology.Clock}

open scoped Fin.CommRing in
/-- The second S11 terminal descriptor word is the base of the node bank at slot entry. -/
theorem prepared_node_base (x : TickActiveROM.CellInput B clock fit)
    (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (nodes : Nodes (parameterArchive pars degree stages W)) (teams : ℕ) (layers : List Layers)
    (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (original prepared : Memory W)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers original groups prepared)
    (headers : B.bounds+4≤2^W) (bounds : B.bounds+4≤TickWorkspace.base pars.age 6)
    (requests : B.auxRequest+8*B.bits≤TickWorkspace.base pars.age 6) :
    prepared (directory pars.age 3+1)=(TickWorkspace.base pars.age 44:Word W) := by
  let a:=parameterArchive pars degree stages W
  let s:=TickWorkspace.stride pars.age
  let loc:=directory pars.age 3+1
  have address : loc=12*s+3*(s/4)+1 := rfl
  have fixed : 128 ≤ s := sizes.fixed
  have n : 8*a.rootsTotal ≤ s := sizes.nodes
  have lanes : a.initialLanes≤a.rootsTotal:=sizes.lanes
  have bits : a.chunkBits ≤ s := sizes.chunks
  have ng : a.groups ≤ s := sizes.groups
  have high : TickWorkspace.base pars.age 6≤loc := by change 7*s≤loc;omega
  obtain ⟨b,o,branch,packed,rfl⟩:=done
  have value:=branch.2.2.1 (1:Fin 3)
  change b loc=(TickWorkspace.base pars.age 44:Word W) at value
  change x.filled .evaluate o loc=_
  rw [filled_high x o .evaluate loc headers (bounds.trans high) (requests.trans high)]
  refine Eq.trans ?_ value
  apply output_frame a groups b o packed loc
  · change outside (6*s) (4*a.initialLanes) loc;dsimp [outside];omega
  · change outside (8*s) a.chunkBits loc;dsimp [outside];omega
  · change outside (9*s) a.groups loc;dsimp [outside];omega
  · change outside (47*s) (3*a.initialLanes) loc;dsimp [outside];omega
  · change outside (48*s) (4*a.initialLanes) loc;dsimp [outside];omega


end ThreeFlat.Diagonal.NavigationPass.RootArchive

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM RAM PhysicalStage NodePublication NavigationNodeRows RootArchive RAM.TickPhysicalABI
variable {F : Type} [Field F] [Fintype F] {W q H J d l : ℕ} {B : TickActiveROM.Layout}
    {fit : Contraction.Fits (TickWeightedBank.shape F q H J) W} {clock : TickChronology.Clock}
    {X : State d l}

open scoped Fin.CommRing in
theorem Selection.prepared_terminal_half_pointers (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer) (start pay : X.Site→ℕ)
    (layers : List Layers) {budget : ℕ} (m out prepared : Memory W)
    (s : Selection r C O seed start pay (pars.nodeArchive (pars.archive degree W) stages W)
      (parameterArchive pars degree stages W) layers budget m)
    (ran : out=state (pars.nodeArchive (pars.archive degree W) stages W)
      (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (x : TickActiveROM.CellInput B clock fit) (nodes : Nodes (parameterArchive pars degree stages W))
    (teams : ℕ) (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers out groups prepared)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (headers : B.bounds+4≤2^W) (bounds : B.bounds+4≤TickWorkspace.base pars.age 6)
    (requests : B.auxRequest+8*B.bits≤TickWorkspace.base pars.age 6) (z : (r.plan.finish s.history).Site) :
    let terminal:=r.finalArchive s.history C O s.path
    let j:=terminal.2 ((r.finalSite s.history).symm z)
    prepared (directory pars.age 3+1)=(TickWorkspace.base pars.age 44:Word W) ∧
    prepared (TickWorkspace.base pars.age 44+8*(r.archivePlanIndex s.history C O s.path z).val+6)=
      ((terminal.1.incident+2*j.val:ℕ):Word W) := by
  intro terminal j
  let a:=parameterArchive pars degree stages W
  let n:=pars.nodeArchive (pars.archive degree W) stages W
  let k:=r.archivePlanIndex s.history C O s.path z
  let loc:=TickWorkspace.base pars.age 44+8*k.val+6
  let stride:=TickWorkspace.stride pars.age
  have hk : k.val<a.rootsTotal := by
    change k.val<a.firstFinal+a.rootCount
    rw [s.first,s.card]
    exact k.isLt
  have num : 8*a.rootsTotal ≤ stride := sizes.nodes
  have fixed : 128 ≤ stride := sizes.fixed
  have zone : TickWorkspace.base pars.age 43≤loc ∧ loc<TickWorkspace.base pars.age 45 := by
    change 44*stride≤45*stride+8*k.val+6 ∧ 45*stride+8*k.val+6<46*stride;omega
  have up : TickWorkspace.base pars.age 6≤TickWorkspace.base pars.age 20 := by change 7*stride≤21*stride;omega
  have small : a.current<2^W := (show a.current≤TickWorkspace.base pars.age 50 by
    change 41*stride≤51*stride;omega).trans_lt sizes.address
  refine ⟨prepared_node_base x pars degree stages sizes nodes teams layers groups out prepared done headers bounds requests,?_⟩
  have keep:=prepared_stage_cell x pars degree stages sizes nodes teams layers groups out prepared done small headers
    (bounds.trans up) (requests.trans up) loc (Or.inr (Or.inl zone))
  change prepared loc=_
  rw [keep,ran,←congrArg List.length s.layout]
  exact final_incident r s.history C O s.path seed n m s.source.room z


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

namespace ThreeFlat.Diagonal.NavigationPass.NativeNavigation
open Computability.VPVNP.BurstRAM RAM PhysicalStage NodePublication NavigationNodeRows RootArchive RAM.TickPhysicalABI
open scoped Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {W q H J d l : ℕ} {B : TickActiveROM.Layout}
    {fit : Contraction.Fits (TickWeightedBank.shape F q H J) W} {clock : TickChronology.Clock}
    {X : State d l}

/-- The node publication and both preparation scans preserve every original
word of the stage heap and the seed metadata, including the terminal live prefixes. -/
theorem Selection.prepared_journal_cell (pars : Parameters) (degree : ℕ) (stages : List NavigationDirectory.Stage)
    (r : Run F X) (C : r.Charges) (O : X.ArchiveSites) (seed : LayerData O.layer) (start pay : X.Site→ℕ)
    (layers : List Layers) {budget : ℕ} (m out prepared : Memory W)
    (s : Selection r C O seed start pay (pars.nodeArchive (pars.archive degree W) stages W)
      (parameterArchive pars degree stages W) layers budget m)
    (ran : out=state (pars.nodeArchive (pars.archive degree W) stages W)
      (program (r.archiveList s.history C O s.path seed)) m layers.length)
    (x : TickActiveROM.CellInput B clock fit) (nodes : Nodes (parameterArchive pars degree stages W))
    (teams : ℕ) (groups : Fin (parameterArchive pars degree stages W).initialLanes→Fin (parameterArchive pars degree stages W).groups)
    (done : (parameterArchive pars degree stages W).preparedInput x nodes teams layers out groups prepared)
    (sizes : PublishSizes (parameterArchive pars degree stages W) W)
    (headers : B.bounds+4≤2^W) (bounds : B.bounds+4≤TickWorkspace.base pars.age 20)
    (requests : B.auxRequest+8*B.bits≤TickWorkspace.base pars.age 20)
    (hdr : 16*layers.length≤TickWorkspace.stride pars.age)
    (volume : ∀ t∈layers,8*(t.actual.first+t.actual.count)≤TickWorkspace.stride pars.age)
    (addr : ℕ) (zone : (TickWorkspace.base pars.age 20≤addr ∧ addr<TickWorkspace.base pars.age 40) ∨
      TickWorkspace.base pars.age 49≤addr) : prepared addr=m addr := by
  let n:=pars.nodeArchive (pars.archive degree W) stages W
  let a:=parameterArchive pars degree stages W
  let rs:=records (r.archiveList s.history C O s.path seed)
  let stride:=TickWorkspace.stride pars.age
  have ord : rs=layers:=s.layout
  have small : a.current<2^W := (show a.current≤TickWorkspace.base pars.age 50 by
    change 41*stride≤51*stride;omega).trans_lt sizes.address
  have after:=prepared_stage_cell x pars degree stages sizes nodes teams layers groups out prepared done small
    headers bounds requests addr (zone.imp_right Or.inr)
  have positional : addr<41*stride ∨ 50*stride≤addr :=
    zone.imp (fun h=>h.2) id
  have fixed : 128 ≤ stride := sizes.fixed
  change 16 * layers.length ≤ stride at hdr
  have ctl : addr≠n.banks.current := by change addr≠41*stride;omega
  have ctr : addr≠n.counter := by change addr≠41*stride+3;omega
  have headerOff : ¬(n.headerBase≤addr ∧ addr<n.headerBase+16*rs.length) := by
    change ¬(42*stride≤addr ∧ addr<42*stride+16*rs.length)
    rw [ord];omega
  have keepsAll (i : Fin rs.length) : keeps n (rs.get i) addr := by
    have member : rs.get i∈layers := by
      rw [←ord]
      exact List.get_mem rs i
    have size : 8 * ((rs.get i).actual.first + (rs.get i).actual.count) ≤ stride :=
      volume (rs.get i) member
    refine ⟨ctr,ctl,?_,?_⟩
    · change addr<44*stride+2*(rs.get i).actual.first ∨
        44*stride+2*(rs.get i).actual.first+2*(rs.get i).actual.count≤addr
      omega
    · change addr<45*stride+8*(rs.get i).actual.first ∨
        45*stride+8*(rs.get i).actual.first+8*(rs.get i).actual.count≤addr
      omega
  rw [after,ran,←congrArg List.length ord]
  rw [state_keeps n _ m addr 0 rs.length (Nat.zero_le _) le_rfl s.source.room.counterSize s.source.room.pointerSize
    (fun i _ _=>keepsAll i)]
  have counterWord : (n.counter : Word W).val = n.counter :=
    Fin.val_cast_of_lt (show n.counter < 2^W from s.source.room.counterSize)
  have pointerWord : (n.banks.current : Word W).val = n.banks.current :=
    Fin.val_cast_of_lt (show n.banks.current < 2^W from s.source.room.pointerSize)
  simp only [state,initial,writeMemory,counterWord,pointerWord,ite_eq_right ctr,ite_eq_right ctl,fillSegment,
    ite_eq_right headerOff]


end ThreeFlat.Diagonal.NavigationPass.NativeNavigation

end OAI
