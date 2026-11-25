import OAI.ThreeFlat.Diagonal.PhysicalNodeHardware
import OAI.ThreeFlat.Diagonal.NavigationRepeatedSize
import OAI.ThreeFlat.Diagonal.PhysicalNodeChargeWork
import OAI.ThreeFlat.Diagonal.NavigationNodeArchive
import OAI.ThreeFlat.Diagonal.RefreshStageWork
import OAI.ThreeFlat.Diagonal.ShrinkRowScan
import OAI.ThreeFlat.RAM.PhysicalProcedureSize

namespace OAI
/-! # Fixed native resource bounds for the complete counted navigation program -/
namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.PhysicalProcedure RAM.DescriptorExpr RAM.PhysicalPinsExpr
open RAM.HistoryStageBody.Physical (resources resources_seq resources_scan)
open CompressorPacking CompressorPacking.Native PhysicalStage NavigationDirectory NavigationNodeRows
open scoped BigOperators Classical
noncomputable section
variable {F : Type} [Field F] {W U : ℕ}

private def zeroParams : Parameters := ⟨0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0⟩

private def archiveNodeBound (B : Block F) :=
  let cap := directoryCap B
  48+∑ x : Fin (cap+1)×Fin (cap+1)×Fin (cap+1),nodeSize x.1.val x.2.1.val x.2.2.val

private theorem published_nodes (B : Block F) (p : Parameters) (blocks r W : ℕ) :
    let a := p.archive (2^B.exponent 0) W
    let ss := (B.repeat blocks).directory r p.axes
    let b := p.nodeArchive a ss W
    ∀ n,resources (b.publish (W:=W) n)≤archiveNodeBound B := by
  intro a ss b n
  have c : b.childCap≤directoryCap B := directory_cap B blocks r p.axes 0 0 (Nat.zero_le _)
  have h : b.halfCap≤directoryCap B := directory_cap B blocks r p.axes 1 (2*2^B.exponent 0) le_rfl
  have m : b.motifCap≤directoryCap B := directory_cap B blocks r p.axes 2 0 (Nat.zero_le _)
  let v : Fin (directoryCap B+1)×Fin (directoryCap B+1)×Fin (directoryCap B+1) :=
    ⟨⟨b.childCap,Nat.lt_succ_of_le c⟩,⟨b.halfCap,Nat.lt_succ_of_le h⟩,⟨b.motifCap,Nat.lt_succ_of_le m⟩⟩
  have e := Finset.single_le_sum (f:=fun x : Fin (directoryCap B+1)×Fin (directoryCap B+1)×Fin (directoryCap B+1)=>
    nodeSize x.1.val x.2.1.val x.2.2.val) (fun _ _=>Nat.zero_le _) (Finset.mem_univ v)
  simp only [NodeArchive.publish,resources_seq,loop_size,node_size]
  change 28+(5+(5+(10+nodeSize b.childCap b.halfCap b.motifCap)))≤_
  change nodeSize b.childCap b.halfCap b.motifCap≤_ at e
  calc
    _ = 48+nodeSize b.childCap b.halfCap b.motifCap := by omega
    _ ≤ archiveNodeBound B := Nat.add_le_add_left e 48


/-- A single block-dependent bound on the resource sum of the two installed publication
scans and their next-header transfer, at every width and residual age. -/
def nodeWriterBudget (B : Block F) := archiveNodeBound B

theorem node_writer_resources (B : Block F) (p : Parameters) (blocks rem W : ℕ) :
    let a := p.archive (2^B.exponent 0) W
    let d := p.nodeArchive a ((B.repeat blocks).directory rem p.axes) W
    resources (NavigationNodeRows.procedure (W:=W) d.banks d.childCap d.halfCap d.motifCap)≤
      nodeWriterBudget B := by
  intro a d
  have ceiling : resources (d.publish (W:=W) 0)≤nodeWriterBudget B :=
    published_nodes B p blocks rem W 0
  apply le_trans _ ceiling
  simp only [NodeArchive.publish,resources_seq,loop_size]
  omega


private theorem root_size (a b : RootArchive) :
    resources (a.publish (W:=W))=resources (b.publish (W:=U)) := by
  simp only [RootArchive.publish,resources_seq,RootArchive.scan,resources_scan,HeaderScan.binds_closed]
  all_goals rfl

private theorem initial_half_work (a b : Archive) (h : a.initialDegree=b.initialDegree) :
    a.initialHalf.work=b.initialHalf.work := by
  let cols (p : Archive) : ShrinkStage.Halves.HalfColumns :=
    ⟨p.initialField 6,p.initialField 0,.op .mul (p.initialField 4) (p.initialField 5),p.initialField 2⟩
  let row (p : Archive) := Formula.op .div (p.initialOffset 11) (.lit 4)
  let site (p : Archive) := Formula.op .div (row p) (.lit (2*p.initialDegree))
  let half (p : Archive) := Formula.op .mod (row p) (.lit (2*p.initialDegree))
  have prefixWork : (ShrinkStage.Halves.prefix (cols a) a.initialDegree (site a) (half a)).work=
      (ShrinkStage.Halves.prefix (cols b) b.initialDegree (site b) (half b)).work := by
    rw [h]
    let term (p : Archive) (i : Fin (2*b.initialDegree)) : Formula 1 :=
      .select .lt (.lit i.val) (half p)
        (ShrinkStage.Halves.half (cols p) b.initialDegree (site p) (.lit i.val)).width (.lit 0)
    exact (RefreshDemandRows.Static.folds (List.finRange (2*b.initialDegree))
      (term a) (term b) (fun _=>rfl)).1
  change _+_+_+(_+_+_+(_+_+_+(ShrinkStage.Halves.prefix _ _ _ _).work+1)+1)+1=_
  rw [prefixWork]
  all_goals rfl

private theorem init_size (a b : Archive) (h : a.initialDegree=b.initialDegree) :
    resources (a.initialMetadata (W:=W))=resources (b.initialMetadata (W:=U)) := by
  simp only [Archive.initialMetadata,resources_seq,resources_scan,HeaderScan.binds_closed,initial_half_work a b h]
  all_goals rfl

private def relaySize := resources (InitialRelayBootstrap.procedure (0:Word 1) ⟨0,0,0⟩ 0 0 0)

private theorem relay_size (cur : Word W) (x : SlotImage.Columns) (v d t : ℕ) :
    resources (InitialRelayBootstrap.procedure cur x v d t)=relaySize := by
  simp only [relaySize,InitialRelayBootstrap.procedure,InitialRelayGraph.procedure,InitialRelayGraph.term,
    resources_seq,resources_scan,HeaderScan.binds_closed]
  all_goals rfl

private theorem wire_size (a b : TerminalWireArchive.Layout) :
    resources (TerminalWireArchive.program (W:=W) a)=resources (TerminalWireArchive.program (W:=U) b) := by
  simp only [TerminalWireArchive.program,resources_seq,resources_scan,HeaderScan.binds_closed]
  change _+((9+(HeaderScan.closed (TerminalWireArchive.checkWord a) : Term W 0 1).labels)+
    (4+(HeaderScan.closed (TerminalWireArchive.checkWord a) : Term W 0 1).binds)+0)=_
  simp only [resources,TerminalWireArchive.check,Term.labels_eq,HeaderScan.binds_closed]
  all_goals rfl


open scoped Fin.CommRing in
theorem Parameters.machine_resources (B : Block F) (K : ℕ) :
    ∃ cut : ℕ,∀ (p : Parameters) (W blocks rem : ℕ),p.symbolCap=K →
      let nav := p.machine (W:=W) B blocks rem
      nav.labels+nav.registers+nav.slots≤cut := by
  let base := zeroParams.archive (2^B.exponent 0) 1
  let ref := zeroParams.rootArchive base (zeroParams.nodeArchive base [] 1) [] 1
  let terminal := base.terminal [] 0 1
  obtain ⟨C,compiled⟩ := compile_text (B.prefix (.done _)) K
  let init := resources (base.initialMetadata (W:=1))
  let final := resources (TerminalWireArchive.program (W:=1) terminal)
  refine ⟨89+relaySize+init+10+(10+C)+final+archiveNodeBound B+resources (ref.publish (W:=1)),?_⟩
  intro p W blocks rem alphabet
  let a := p.archive (2^B.exponent 0) W
  let ss := (B.repeat blocks).directory rem p.axes
  let b := p.nodeArchive a ss W
  let c := p.rootArchive a b ss W
  let current := (a.control : Word W)
  have program := compiled W current
  have publication := published_nodes B p blocks rem W (nodeLayers a.K ss a.cursor a.seedLayer).length
  have ik : resources (a.initialMetadata (W:=W))=init := init_size a base rfl
  have tr := wire_size (W:=W) (U:=1) (a.terminal ss (c.rootCount*a.initialDegree) W) terminal
  have root := root_size (W:=W) (U:=1) c ref
  have hk : a.K=K := alphabet
  have archiveCost (x : PackedStageArchive.Layout) :
      resources (PackedStageArchive.procedure x : Procedure W) = 28 := rfl
  have startCost (cell val : Word W) : resources (start cell val) = 5 := rfl
  change resources (navigation (W := W) a b c B blocks rem (c.rootCount*a.initialDegree))≤_
  simp only [navigation,active,Archive.boot,repeated,resources_seq,loop_size,relay_size,
    archiveCost,startCost]
  change 89+(relaySize+(resources (a.initialMetadata (W:=W))+(5+(5+
    ((10+resources (compile current a.K (B.prefix (.done _))))+
      resources (TerminalWireArchive.program (W:=W) (a.terminal ss (c.rootCount*a.initialDegree) W)))))))+
     (resources (b.publish (W:=W) (nodeLayers a.K ss a.cursor a.seedLayer).length)+resources (c.publish (W:=W)))≤_
  rw [ik,tr,root]
  have comp : resources (compile current a.K (B.prefix (.done _)))≤C := by rw [hk];exact program
  change resources (b.publish (W:=W) (nodeLayers a.K ss a.cursor a.seedLayer).length)≤archiveNodeBound B at publication
  unfold final
  omega

theorem Parameters.cursor_machine_resources [Fintype F] (B : Block F) :
    ∃ cut : ℕ, ∀ (age rem low stride cells : ℕ) (shape : RAM.PhysicalPinsExpr.Shape)
      (tableOffset unitWork W blocks bits : ℕ),
      let p := Parameters.cursor B age rem low stride cells shape tableOffset unitWork
      let nav := p.machine (W:=W) B blocks bits
      nav.labels+nav.registers+nav.slots≤cut := by
  obtain ⟨cut,bound⟩ := Parameters.machine_resources B B.alphabetCap
  exact ⟨cut,fun _ _ _ _ _ _ _ _ _ _ _=>bound _ _ _ _ rfl⟩


end
end ThreeFlat.Diagonal.NavigationPass

end OAI
