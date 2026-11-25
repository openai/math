import OAI.Hierarchy.TraceShrinkRoom
import OAI.ThreeFlat.Diagonal.PhysicalShrinkAdmission

namespace OAI
/-! # Native shrinking writer at the trace word width

The table is chosen by scanning the actual graph and widths. The caller supplies
the packed incoming record words. The admission theorem returns the selected
successor graph and the descriptor arrays written by the same invocation.
-/

namespace Hierarchy.TraceShrinkRetained

open ThreeFlat Diagonal Diagonal.PhysicalStage
open Computability.VPVNP.BurstRAM PrivateRAM RAM Computability.VPVNP.Compression CompressorPacking
open Native Native.ShrinkStage Native.ShrinkStage.Resident Native.Placement
open NavigationDirectory NavigationPass PhysicalShrink ShrinkStageNav
open scoped Classical Fin.NatCast BigOperators
noncomputable section

open private thick_read_bound from OAI.ThreeFlat.Diagonal.PhysicalShrinkAdmission

variable {F : Type} [Field F] (T : ShrinkMotif.Table F) (s D rem : ℕ) (hD : 0<D)
variable (small : ((2^(2*(2^s)+1)*(2^s)*(2^s):ℕ):ℝ)/D≤1/1024)
variable (A : State (2^s) (shrinkCharge s+rem))

set_option quotPrecheck false
local notation "M" => shrinkBinary T s D rem hD small A
local notation "Q" => shrinkBinaryFamily T s D rem hD small A
local notation "N" => Fintype.card (shrinkRecordState s rem A).Base
local notation "d" => (2^s : ℕ)
local notation "k" => (2*d+1 : ℕ)
local notation "S" => shrinkStage s D
local notation "t" => CompressorPacking.tagBits d
local notation "x" => dims S N t rem
local notation "top" => shrinkMotifWidthFactor T k d*(1+A.maxWidth)

/-- The old-chart scan and table-choice scan produce the admission bank for the
mounted count words, with the selected tile, per-motif demands and exact clocks. -/
theorem prepared {K W q : ℕ} (r : TraceRetainedRoom.Room q W)
    (cur : Word W) (input : Memory W) (c : Cursor)
    (space : CursorSpace cur input c K x)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal _) (incoming S N (pointers K c x))
      (fun i=>(input i).val) A.width)
    (fit : (Q).Fits K W) (raw : HistogramRegister.Words (Q).motifs K W)
    (stream : ∀ i j,input (c.dense+K*i.val+j.val)=raw i j)
    (fixed : fixedWords T s D ≤ q) (arena : (Stage.shrink x).heapWords≤q)
    (wire : A.maxWidth+1≤q^4) :
    ShrinkPrefix T s D rem hD small A cur input c fit raw := by
  obtain ⟨oldCap,_,tiles,room,_,_⟩ := scalar_room T s D rem hD small A r fixed arena wire
  let P := shrinkRecordPacking s rem A
  have oldBound (a : P.Motif) : thickWidth P (shrinkRecordWidth s rem A) (P.bundle a)<2^W := by
    exact thick_read_bound P (shrinkRecordWidth s rem A) (prior_width_le s rem A)
      room (P.bundle a)
  exact shrink_prefix T s D rem hD small A cur input c fit raw space old stream
    oldCap oldBound tiles (by
      apply shrink_choice_room (T:=T) (s:=s) (D:=D) (rem:=rem) (A:=A)
      all_goals assumption)

/-- From the mounted old image and untrusted record to the *selected* physical
graph, width file, descriptor rows and retained input archive at the supplied word width.
Each rejecting record terminates through the real histogram guard. -/
theorem admission_of_room {K W q : ℕ} (r : TraceRetainedRoom.Room q W) (word : 0<W) (field : FieldCode F W)
    (cur : Word W) (input : Memory W) (c : Cursor)
    (space : CursorSpace cur input c K x)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal _) (incoming S N (pointers K c x))
      (fun i=>(input i).val) A.width)
    (sep : c.header+64≤c.graph ∧ c.header+64≤c.width)
    (fit : (Q).Fits K W) (raw : HistogramRegister.Words (Q).motifs K W)
    (stream : ∀ i j,input (c.dense+K*i.val+j.val)=raw i j)
    (fixed : fixedWords T s D ≤ q) (arena : (Stage.shrink x).heapWords≤q)
    (wire : A.maxWidth+1≤q^4) (alphabet : shrinkSymbolBound T≤K) :
    let body := NavigationPass.shrink cur K s D T
    let bits := List.ofFn (HistogramRegister.bitTable raw)
    TickStageSpec.Admission field body.block body.publicData (fun m=>m=input)
      (fun _=>(((Q).record fit).read bits).isSome)
      (fun _ out=>∃ branch : Fin (M).rules.count, ((Q).record fit).read bits=some branch ∧
        ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
      (shrinkBudget T s D rem hD small A K cur c) := by
  obtain ⟨pre,post,tiles,demands,widths,score⟩ := scalar_room T s D rem hD small A r fixed arena wire
  exact shrink_admission T s D rem hD small A field word cur input c space old sep
    fit raw stream pre post tiles alphabet demands widths score

/-- From the mounted old image and untrusted record to the *selected* physical
graph, width file, descriptor rows and retained input archive at `64*w` bits.
Each rejecting record terminates through the real histogram guard. -/
theorem admission {K w : ℕ} (hw : 7≤w) (field : FieldCode F (64*w))
    (cur : Word (64*w)) (input : Memory (64*w)) (c : Cursor)
    (space : CursorSpace cur input c K x)
    (old : SlotImage.Stored A.graph A.order (tagOrdinal _) (incoming S N (pointers K c x))
      (fun i=>(input i).val) A.width)
    (sep : c.header+64≤c.graph ∧ c.header+64≤c.width)
    (fit : (Q).Fits K (64*w)) (raw : HistogramRegister.Words (Q).motifs K (64*w))
    (stream : ∀ i j,input (c.dense+K*i.val+j.val)=raw i j)
    (fixed : fixedWords T s D ≤ 2^w) (arena : (Stage.shrink x).heapWords≤2^w)
    (wire : A.maxWidth+1≤(2^w)^4) (alphabet : shrinkSymbolBound T≤K) :
    let body := NavigationPass.shrink cur K s D T
    let bits := List.ofFn (HistogramRegister.bitTable raw)
    TickStageSpec.Admission field body.block body.publicData (fun m=>m=input)
      (fun _=>(((Q).record fit).read bits).isSome)
      (fun _ out=>∃ branch : Fin (M).rules.count, ((Q).record fit).read bits=some branch ∧
        ShrinkOutput (K:=K) T s D rem hD small A cur input c branch out)
      (shrinkBudget T s D rem hD small A K cur c) := by
  exact admission_of_room T s D rem hD small A (TraceRetainedRoom.native hw) (by omega)
    field cur input c space old sep fit raw stream fixed arena wire alphabet

/-- The exact physical stage budget is linear in the number of incoming sites.
The coefficient depends only on the shrink rule and its fixed alphabet. -/
theorem time (K : ℕ) : ∃ C : ℕ, ∀ (W : ℕ) (cur : Word W) (c : Cursor),
    shrinkBudget T s D rem hD small A K cur c ≤ C*(1+Fintype.card A.Base*2^(shrinkCharge s+rem)) := by
  obtain ⟨C,work⟩ := shrink_absolute_time T s D K
  refine ⟨C,fun W cur c=>?_⟩
  rw [shrinkBudget_absolute]
  exact work W cur c rem (Fintype.card A.Base)


end
end Hierarchy.TraceShrinkRetained

end OAI
