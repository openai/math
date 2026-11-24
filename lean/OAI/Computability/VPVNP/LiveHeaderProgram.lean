import OAI.Computability.VPVNP.LiveHeaderSchedule
import OAI.Computability.VPVNP.LiveHeaderDescriptors
import OAI.Computability.VPVNP.LiveHeaderBounded
import OAI.Computability.VPVNP.LiveHeaderAllocated
import OAI.Computability.VPVNP.LivePrimedGroupIndices
import OAI.Computability.VPVNP.LiveStageOperands

/-!
# The live group's native header program

The same table parses every group and input length. The public-data function
uses the chain and field sizes and the scratch base. The group number, advice,
mode, cut lengths, field offsets and payloads come from word-memory probes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM LiveHeaderSchedule
open LiveHeaderDescriptors

/-- Uniform scratch-register and local public-operand capacities of a stage. -/
abbrev StageTemplate := (p : ℕ) × Template p 50 17

/-- Embed a smaller register or operand index into a larger bank at the same numerical
position. -/
def includeFin {n m : ℕ} (h : n ≤ m) : Fin n ↪ Fin m :=
  ⟨fun j => j.castLE h, fun _ _ eq => Fin.ext (congrArg (fun x : Fin m => x.val) eq)⟩

/-- Widen a native component template to the common header stage interface of 50 registers and
17 public operands. -/
def entry {p r k : ℕ} (T : Template p r k) (hr : r ≤ 50 := by decide)
    (hk : k ≤ 17 := by decide) : StageTemplate :=
  ⟨p, LiveStageLink.widen T (includeFin hr) (includeFin hk)⟩

/-- The fixed public operand assignment for the scalar cut-width and flag calculations. -/
def widthSlots : LiveHeaderWidths.Parameters := ⟨0,1,2,3,4⟩
/-- The nine public slots assigned to the descriptor worker's width, flags, dimensions, and
output cells. -/
def descriptorSlots : LiveHeaderDescriptors.Parameters := ⟨0,1,2,3,4,5,6,7,8⟩
/-- The four public slots assigned to the field scan's first cursor, source offset,
destination, and runtime count. -/
def scanSlots : LiveHeader.Allocated.Parameters := ⟨0,1,2,3⟩

/-- Each stage either accepts after one microcall or is wrapped with a
public-capacity test. In particular, a zero-capacity scan makes one terminating call. -/
def stageTemplate : Stage → StageTemplate
  | .index => entry (LiveHeaderBounded.bounded (template LiveHeader.indexCell 11))
  | .advice => entry (LiveHeaderBounded.bounded (template (LiveHeader.copyCell 1) 7))
  | .width slot => entry (LiveHeaderWidths.WidthCode.table widthSlots slot)
  | .flag f => entry ((LiveHeaderWidths.PhaseCode.block widthSlots f).template none)
  | .firstTail => entry ((LiveHeaderWidths.PhaseCode.firstTailBlock widthSlots 5).template none)
  | .mode => entry (LiveHeader.Mode.program.template none)
  | .primedInit => entry ((lines LiveHeader.PrimedGroupIndices.setup (by decide)).template none)
  | .primedDigits => entry (LiveHeaderBounded.bounded (template LiveHeader.PrimedGroupIndices.digit 11))
  | .descriptor side f => entry ((Native.block descriptorSlots side f).template none)
  | .scan side f => entry (LiveHeaderBounded.bounded
      (LiveHeader.Allocated.table scanSlots (if side = Side.left then 2 else 3) (decide (f = .padding))))

/-- One row of public operands. The last operand of every bounded stage
holds the capacity at the position expected by its own wrapper. -/
def publicRow (s : Sizes) (base : ℕ) (st : Stage) (j : Fin 17) : ℕ :=
  let widthInputs (out : ℕ) := [s.h+1,s.delta,highAddr s base,populationAddr s base,out,indexBase base]
  let groupInputs := [indexBase base,leftIndexBase s base,rightIndexBase s base,borrowAddr base]
  let row := match st with
    | .index => [indexBase base,highAddr s base,populationAddr s base,s.h+2]
    | .advice => [0,adviceBase s base,s.advice]
    | .width slot => widthInputs (widthAddr base slot)
    | .flag f => widthInputs (flagAddr base f)
    | .firstTail => widthInputs (firstTailAddr base)
    | .mode => [widthAddr base .liveLeft,widthAddr base .liveRight,flagAddr base .firstHalf,tagAddr base]
    | .primedInit => groupInputs
    | .primedDigits => groupInputs ++ [s.h+1]
    | .descriptor side _ =>
        [widthAddr base (if side = Side.left then .liveLeft else .liveRight),tagAddr base,
         flagAddr base .firstHalf,firstTailAddr base,s.delta,s.e,s.config,offsetAddr base,countAddr base]
    | .scan side f =>
        [0,offsetAddr base,dest s base side f,countAddr base] ++ List.replicate 12 0 ++ [s.capacity f]
  row[j.val]?.getD 0

/-- An index into the fixed list of native live-header stages. -/
abbrev StageId := Fin stages.length
/-- An index in the flat bank containing seventeen public words per header stage. -/
abbrev PublicIndex := Fin (stages.length * 17)

/-- Retrieve the scheduled header operation at a given stage index. -/
def stage (i : StageId) := stages.get i

/-- Embed a local operand position in the seventeen-word public row of the selected stage. -/
def rowEmbedding (i : StageId) : Fin 17 ↪ PublicIndex :=
  ⟨fun j => finProdFinEquiv (i,j), fun _ _ h => (Prod.mk.inj (finProdFinEquiv.injective h)).2⟩

/-- Relocate all public operands into their respective fixed rows. -/
def component (i : StageId) : Template (stageTemplate (stage i)).1 50 (stages.length*17) :=
  LiveStageLink.widen (stageTemplate (stage i)).2 (Function.Embedding.refl _) (rowEmbedding i)

/-- Advance to the following header stage, returning no successor at the end of the list. -/
def next (i : StageId) : Option StageId :=
  if h : i.val+1 < stages.length then some ⟨i.val+1,h⟩ else none

/-- A standalone executable native template, which accepts only after the
last padding scan reaches its limit. Inner stage handoffs reset the cursor. -/
def program := LiveStageLink.linked component next

/-- Exact finite operand vector used by the linked header program. `base`
also serves as the inner linker's tag address, initially in zero memory. -/
def publicData (w : ℕ) (s : Sizes) (base : ℕ) : Fin (stages.length*17+1) → Word w :=
  LiveStageLink.publicData (fun j : PublicIndex =>
    let pair := finProdFinEquiv.symm j
    Fin.ofNat _ (publicRow s base (stage pair.1) pair.2)) (Fin.ofNat _ base)

theorem public_at_stage (w : ℕ) (s : Sizes) (base : ℕ) (i : StageId) (j : Fin 17) :
    publicData w s base ((rowEmbedding i j).castSucc) =
      Fin.ofNat _ (publicRow s base (stage i) j) := by
  simp only [publicData,LiveStageLink.publicData,Fin.snoc_castSucc]
  change Fin.ofNat _ (publicRow s base (stage (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2) = _
  rw [Equiv.symm_apply_apply]

theorem public_tag (w : ℕ) (s : Sizes) (base : ℕ) :
    publicData w s base (Fin.last _) = Fin.ofNat _ base := by simp [publicData,LiveStageLink.publicData]

/-- Public operands before relocation into the combined header table. -/
def rowData (w : ℕ) (s : Sizes) (base : ℕ) (st : Stage) (j : Fin 17) : Word w :=
  Fin.ofNat _ (publicRow s base st j)

/-- Read the flattened public operand by recovering its stage row and offset and evaluating the
corresponding row data. -/
def bank (w : ℕ) (s : Sizes) (base : ℕ) (j : PublicIndex) : Word w :=
  let pair := finProdFinEquiv.symm j
  rowData w s base (stage pair.1) pair.2

theorem bank_row (w : ℕ) (s : Sizes) (base : ℕ) (i : StageId) :
    bank w s base ∘ rowEmbedding i = rowData w s base (stage i) := by
  funext j
  change rowData w s base (stage (finProdFinEquiv.symm (finProdFinEquiv (i,j))).1)
    (finProdFinEquiv.symm (finProdFinEquiv (i,j))).2 = _
  rw [Equiv.symm_apply_apply]

theorem entry_start {p r k w : ℕ} (T : Template p r k) (hr : r ≤ 50) (hk : k ≤ 17)
    (pub : Fin 17 → Word w) (fuel : ℕ) (state : Word w) (m : Memory w) (bits : List Bool) :
    let big := ((entry T hr hk).2.instantiate w pub).program
    let small := (T.instantiate w (pub ∘ includeFin hk)).program
    execute big fuel (big.start state) m bits = execute small fuel (small.start state) m bits :=
  LiveStageLink.execute_widen_start T _ _ pub fuel state m bits

/-- A call in a linked operand bank executes the original stage with its
own prescribed public row. The two relocations add no work or branch bits. -/
theorem component_start (w : ℕ) (s : Sizes) (base : ℕ) (i : StageId) (fuel : ℕ)
    (state : Word w) (m : Memory w) (bits : List Bool) :
    let big := ((component i).instantiate w (bank w s base)).program
    let small := ((stageTemplate (stage i)).2.instantiate w (rowData w s base (stage i))).program
    execute big fuel (big.start state) m bits = execute small fuel (small.start state) m bits := by
  simpa only [component,bank_row] using LiveStageLink.execute_widen_start (stageTemplate (stage i)).2
    (Function.Embedding.refl _) (rowEmbedding i) (bank w s base) fuel state m bits

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
