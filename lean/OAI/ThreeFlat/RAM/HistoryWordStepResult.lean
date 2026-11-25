import OAI.ThreeFlat.Diagonal.HistoryStageCharges
import OAI.ThreeFlat.RAM.HistoryStageNumericTape
import OAI.ThreeFlat.RAM.HistoryInheritedSources

namespace OAI
/-! # The actual compiled target forest at a physical history site -/
namespace ThreeFlat.RAM.HistoryWordStepResult
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.HistoryContraction Diagonal.PhysicalStage
open HistoryStageRoot HistoryStageNumericTape HistoryPartyBatchExec HistoryStageBody.Physical
open scoped Classical BigOperators Fin.CommRing
open private forestUncast from OAI.ThreeFlat.Diagonal.PhysicalWordAssembly
noncomputable section
variable {F Pins : Type} [Field F]

omit [Field F] in
private theorem uncast_pair {X Y : Shape} (e : Y=X) (form : Form X Pins)
    (N : Forest F (e.symm ▸ form : Form Y Pins)) (v : X.Site) :
    (⟨_,N ((Equiv.cast (congrArg Shape.Site e)).symm v)⟩ : Σ p,Tree F p)=
      ⟨_,forestUncast e.symm form N v⟩ := by cases e;rfl

variable {d l D lanes : ℕ} {A : State d l} {R : Move F A D lanes} {b : Fin R.rules.count}
    {L : A.Words Pins} (st : R.WordStep Pins L b) (trees : Forest F L.ports.form) (v : (R.next b).Site)
local notation "z" => Move.WordStep.targetSite (R:=R) (i:=b) v
local notation "D₀" => st.stage
local notation "N" => fun k => Tree.compile (Stage.tapeFactor D₀ trees z k)
local notation "links" => Stage.tapePin D₀ trees z

theorem forest_pair :
    (⟨_,((D₀).assemble trees z).compile⟩ : Σ p,BitNetwork F p) =
      ⟨_,(st.nextForest trees v).compile⟩ :=
  congrArg (fun s : (Σ p,Tree F p)=>(⟨s.1,s.2.compile⟩ : Σ p,BitNetwork F p))
    (uncast_pair (R.target_eq b) st.words.ports.form ((D₀).assemble trees) v)

theorem resource_eq :
    ((D₀).assemble trees z).resources=(st.nextForest trees v).resources :=
  congrArg (fun s : Σ p,Tree F p=>s.2.resources)
    (uncast_pair (R.target_eq b) st.words.ports.form ((D₀).assemble trees) v)

variable {W : ℕ} (T : Input) (raw : ℕ→ℕ) (m : Memory W) (tag : ((Fin 3→Bool)→F)→ℕ)
local notation "q" => Typed.copy T raw N links
local notation "compiledStage" => Tree.compile (Stage.assemble D₀ trees z)
local notation "actual" => Tree.compile (Move.WordStep.nextForest st trees v)

/-- The four copy-header columns give exactly the row and bit totals stored by
the physical compiler, using the actual kernel and all earlier S13 headers. -/
theorem values (shape : Wiring T raw links) (saved : Stored T raw N links tag m)
    (ext : outer T raw=st.words.ext v) :
    result T raw = ![T.stream,st.words.ports.form.width v,(actual).cells,(actual).internal,T.ext,st.words.ext v] := by
  have deg : childCount T raw=(D₀).count z:=by have:=shape.size;omega
  have rootRows : (atResult raw T.kernel).rows=((D₀).root z).rows:=by
    have val:=congrArg HistoryBoundedJoin.Info.factors (saved.info (0:Fin ((D₀).count z+1)))
    change (atResult raw T.kernel).rows=((D₀).root z).compile.cells at val
    simpa only [Tree.compiled_rows] using val
  have rootBits : (atResult raw T.kernel).bits=((D₀).root z).bits:=by
    have val:=congrArg HistoryBoundedJoin.Info.hidden (saved.info (0:Fin ((D₀).count z+1)))
    change (atResult raw T.kernel).bits=((D₀).root z).compile.internal at val
    simpa only [Tree.compiled_bits] using val
  have childRows (k : Fin ((D₀).count z)) : (atResult raw (childPtr T raw k.val)).rows=(trees ((D₀).child z k).val).rows:=by
    have val:=congrArg HistoryBoundedJoin.Info.factors (saved.info k.succ)
    change (atResult raw (ptr T raw (k.val+1))).rows=(trees ((D₀).child z k).val).compile.cells at val
    simpa [ptr,Tree.compiled_rows] using val
  have childBits (k : Fin ((D₀).count z)) : (atResult raw (childPtr T raw k.val)).bits=(trees ((D₀).child z k).val).bits:=by
    have val:=congrArg HistoryBoundedJoin.Info.hidden (saved.info k.succ)
    change (atResult raw (ptr T raw (k.val+1))).bits=(trees ((D₀).child z k).val).compile.internal at val
    simpa [ptr,Tree.compiled_bits] using val
  have rowSum:=prefix_value (T:=T) (m:=raw) Result.rows _ childRows ((D₀).count z) le_rfl
  have bitSum:=prefix_value (T:=T) (m:=raw) Result.bits _ childBits ((D₀).count z) le_rfl
  have same:=forest_pair st trees v
  have pins:=shape.pins.trans (congrArg (fun x : Σ p,BitNetwork F p=>x.1) same)
  have rr:=congrArg (fun x : (Σ p,BitNetwork F p)=>x.2.cells) same
  have bb:=congrArg (fun x : (Σ p,BitNetwork F p)=>x.2.internal) same
  change (compiledStage).cells=(actual).cells at rr
  change (compiledStage).internal=(actual).internal at bb
  have rows := rr.symm.trans ((Tree.compiled_rows ((D₀).assemble trees z)).trans
    ((D₀).assemble_rows trees z))
  have bits := bb.symm.trans ((Tree.compiled_bits ((D₀).assemble trees z)).trans
    ((D₀).assemble_bits trees z))
  change outPins T raw = st.words.ports.form.width v at pins
  rw [result,deg,pins,rootRows,rootBits,rowSum,bitSum,shape.shared,ext,rows,bits]
  simp only [Nat.add_assoc, Fin.castLE_refl]

theorem records (stream : ℕ) (initial : HistoryCompiledRows.Records tag compiledStage stream m) :
    HistoryCompiledRows.Records tag actual stream m := by
  let kept := fun b : (Σ p,BitNetwork F p)=>HistoryCompiledRows.Records tag b.2 stream m
  exact (congrArg kept (forest_pair st trees v)).mp initial

end

end ThreeFlat.RAM.HistoryWordStepResult

end OAI
