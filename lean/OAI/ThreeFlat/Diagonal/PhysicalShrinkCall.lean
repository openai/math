import OAI.ThreeFlat.Diagonal.ShrinkCursorColumns
import OAI.ThreeFlat.Diagonal.ShrinkRecordBase
import OAI.ThreeFlat.Diagonal.PhysicalShrinkFixed
import OAI.ThreeFlat.Diagonal.RefreshCursorLayout

namespace OAI
/-! # Uniform shrinking call at the navigation ABI's actual word scale -/
namespace ThreeFlat.Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage Native.ShrinkStage.Resident
open NavigationDirectory NavigationPass PhysicalShrink
open scoped Classical
noncomputable section
variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024) (A : State (2^s) (shrinkCharge s+rem))
local notation "d" => (2^s:ℕ)
local notation "t" => CompressorPacking.tagBits d
local notation "S" => shrinkStage s D
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "N" => Fintype.card (State.Base (shrinkRecordState s rem A))
local notation "x" => dims S N t rem

theorem shrink_at_scale {u K : ℕ} (hu : 40≤u) (field : FieldCode F (16*u^10))
    (cur : Word (16*u^10)) (input : Memory (16*u^10)) (c : Cursor)
    (space : CursorSpace cur input c K x) (sep : c.header+64≤c.graph ∧ c.header+64≤c.width)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal _) (RefreshStageNav.oldColumns c (Fintype.card A.Base) d)
      (fun i=>(input i).val) A.width)
    (fit : (Q).Fits K (16*u^10)) (raw : HistogramRegister.Words (Q).motifs K (16*u^10))
    (stream : ∀ i j,input (c.dense+K*i.val+j.val)=raw i j)
    (fixed : shrinkFixedWords T s D≤u) (alphabet : shrinkSymbolBound T≤K)
    (arena : (Stage.shrink x).heapWords≤2^(u^10)) (wire : A.maxWidth+1≤(2^(u^10))^4) :
    let body:=NavigationPass.shrink cur K s D T
    let bits:=List.ofFn (HistogramRegister.bitTable raw)
    TickStageSpec.Admission field body.block body.publicData (fun m=>m=input) (fun _=>(((Q).record fit).read bits).isSome)
      (fun _ out=>∃ j:Fin (M).rules.count,((Q).record fit).read bits=some j ∧
        ShrinkOutput (K:=K) T s D rem hD small A cur input c j out)
      (shrinkBudget T s D rem hD small A K cur c) := by
  obtain ⟨oldcap,outcap,tiles,room,cap,score⟩:=shrink_scalar_room T s D rem hD small A hu fixed arena wire
  have high : 0<16*u^10 := by
    have : 0<u := by omega
    positivity
  have cols : incoming S N (pointers K c x) = RefreshStageNav.oldColumns c (Fintype.card A.Base) d :=
    shrink_input_columns s D rem A K c
  dsimp only
  intro np nr nk machine
  exact shrink_admission T s D rem hD small A field high cur input c space
    (by rw [cols];exact old) sep fit raw stream oldcap outcap tiles alphabet room cap score machine


end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
