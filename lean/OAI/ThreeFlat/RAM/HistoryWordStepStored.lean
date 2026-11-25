import OAI.ThreeFlat.RAM.HistoryInheritedSources
import OAI.ThreeFlat.RAM.HistoryStageNumericTape

namespace OAI
/-! # Real cached gate rows and arities in the chosen rewrite's stage order -/

namespace ThreeFlat.RAM.HistoryStageSetup

open Computability.VPVNP.BurstRAM PrivateRAM HistoryPartyBatchExec HistoryStageRoot HistoryStageBody
open HistoryStageBody.Physical NavigationNodeRows HistoryBoundedJoin HistoryStageNumericTape
open Diagonal.PhysicalStage Diagonal.HistoryContraction Diagonal.TickWorkspace
open scoped BigOperators Fin.CommRing Classical
noncomputable section

variable {W : ℕ} {F Pins E : Type} [Field F] {d l D lanes : ℕ} {A : State d l}
    {R : Move F A D lanes} {branch : Fin R.rules.count}
    (L : A.Words Pins) (step : R.WordStep Pins L branch)
    {old : A.ArchiveSites} {ch : (R.next branch).Site→ℕ} (row : R.ArchiveStep branch old ch)

set_option maxRecDepth 16000 in
theorem stage_stored (order : step.ChildOrder row) (v : (R.next branch).Site)
    (T : Input) (u : ℕ) (mem : Memory W) (b : Banks) (N : Forest F L.ports.form)
    (origin : ∀ x,Fin (L.ext x)→E) (pointer : E→ℕ) (encode : ((Fin 3→Bool)→F)→ℕ)
    (directory : DirectoryRow b row.sites.layer (row.sites.ord v) mem)
    (source : row.data.Reads (numeric mem)) (idx : T.id=row.sites.id v) (baseNodes : T.nodeBase=b.nodes)
    (baseCache : T.resultBase=base u 13)
    (countRoom : row.sites.layer.childCount<2^W)
    (listRoom : row.sites.layer.children+(row.sites.ord v).val*row.sites.layer.childCount<2^W)
    (child : ∀ k : Fin row.sites.layer.childCount,∃ stream ext,
      (NodeValue.ofSite (Run.nodeOfSite L N origin (row.row.children v k).val) pointer stream ext).Cached
        encode u (row.data.child (row.sites.ord v) k) mem)
    (rootPins : (atResult (numeric mem) T.kernel).pins=step.stage.rootWidth (Move.WordStep.targetSite (R:=R) (i:=branch) v))
    (rootRows : (atResult (numeric mem) T.kernel).rows=(step.stage.root (Move.WordStep.targetSite (R:=R) (i:=branch) v)).compile.cells)
    (rootBits : (atResult (numeric mem) T.kernel).bits=(step.stage.root (Move.WordStep.targetSite (R:=R) (i:=branch) v)).compile.internal)
    (kernel : HistoryCompiledRows.Records encode (step.stage.root (Move.WordStep.targetSite (R:=R) (i:=branch) v)).compile
      (atResult (numeric mem) T.kernel).stream mem) :
    let z:=Move.WordStep.targetSite (R:=R) (i:=branch) v
    let raw:=numeric mem
    Stored T raw (fun k=>(step.stage.tapeFactor N z k).compile) (step.stage.tapePin N z) encode mem ∧
    (∀ k : Fin (step.stage.count z),(atResult raw (childPtr T raw k.val)).pins=L.ports.form.width (step.stage.child z k).val) ∧
    (∀ k : Fin (step.stage.count z),(atResult raw (childPtr T raw k.val)).extCount=L.ext (step.stage.child z k).val) := by
  let z:=Move.WordStep.targetSite (R:=R) (i:=branch) v
  let raw:=numeric mem
  let oldRec (k : Fin (step.stage.count z)):=atResult raw (childPtr T raw k.val)
  obtain ⟨_,actual⟩:=recorded_child_addresses T mem b row.data (row.sites.ord v) directory source idx baseNodes countRoom listRoom
  have seen (k : Fin (step.stage.count z)) :
      let site:=(step.stage.child z k).val
      (oldRec k).pins=L.ports.form.width site ∧ (oldRec k).extCount=L.ext site ∧
      (oldRec k).rows=(N site).compile.cells ∧ (oldRec k).bits=(N site).compile.internal ∧
      HistoryCompiledRows.Records encode (N site).compile (oldRec k).stream mem := by
    let i:=k.cast (step.count_eq row v).symm
    obtain ⟨stream,ext,cache⟩:=child i
    have ptr : childPtr T raw k.val=base u 13+8*row.data.child (row.sites.ord v) i := by
      rw [←baseCache];exact actual i
    have location : (row.row.children v i).val=(step.stage.child z k).val := order v i
    have hdr:=cache.header
    change atResult raw (base u 13+8*row.data.child (row.sites.ord v) i)=
      ⟨stream,L.ports.form.width (row.row.children v i).val,(N (row.row.children v i).val).compile.cells,
        (N (row.row.children v i).val).compile.internal,ext,L.ext (row.row.children v i).val⟩ at hdr
    have table:=cache.rows
    change HistoryCompiledRows.Records encode (N (row.row.children v i).val).compile stream mem at table
    rw [location] at hdr table
    dsimp only [oldRec]
    rw [ptr,hdr]
    exact ⟨rfl,rfl,rfl,rfl,table⟩
  refine ⟨⟨?_,?_⟩,fun k=>(seen k).1,fun k=>(seen k).2.1⟩
  · intro i;refine Fin.cases ?_ (fun k=>?_) i
    · change Info.mk _ (atResult raw T.kernel).pins (atResult raw T.kernel).rows (atResult raw T.kernel).bits=_
      rw [rootPins,rootRows,rootBits];rfl
    · change Info.mk (oldRec k).stream (oldRec k).pins (oldRec k).rows (oldRec k).bits =
        Info.mk (oldRec k).stream (L.ports.form.width (step.stage.child z k).val)
          (N (step.stage.child z k).val).compile.cells (N (step.stage.child z k).val).compile.internal
      rw [(seen k).1,(seen k).2.2.1,(seen k).2.2.2.1]
  · intro i;refine Fin.cases kernel (fun k=>?_) i
    change HistoryCompiledRows.Records encode (N (step.stage.child z k).val).compile (oldRec k).stream mem
    exact (seen k).2.2.2.2

end

end ThreeFlat.RAM.HistoryStageSetup

end OAI
