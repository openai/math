import OAI.ThreeFlat.Diagonal.TickBucketScanValues
import OAI.ThreeFlat.Diagonal.TickSlotForest

namespace OAI
/-! # Native tick arguments from the assigned forest and the actual bucket rows -/

noncomputable section
namespace ThreeFlat.Diagonal.TickPhaseModel.Buckets

open HistoryContraction TickChronology TickAuxiliary PackedChunkTransfer RotatedChunkGuards
open RAM.TickActiveROM RAM.Contraction RAM.BitLayout RAM RAM.HistoryFactors
open scoped Classical BigOperators
variable {F : Type*} [Field F] [Fintype F] {S : Shape} {P : Plan F S} {E : P.Codes}
  {bits : P.History → ℕ} {A : RAM.TickActiveROM.Layout} {c : Clock} {R : GroupRegister P E bits A.bits}
  {lanes span p H J w : ℕ} {fit : Fits (TickWeightedBank.shape F p H J) w}
  (T : Buckets P bits c A.bits lanes span)

private def proposal {a : ℕ} (capacity n : ℕ) (fits : 1+capacity+2*n≤a) (oa : Aux a)
    (side : Bool) (i : ℕ) : Bool :=
  if hi : i<n then oa ⟨1+capacity+((if side then n else 0)+i),by cases side <;> simp <;> omega⟩ else false

/-- Select and pad the contracted cell stream. Pair bits come directly from
the old auxiliary register, and each interval is a real clipped cursor bucket. -/
def cellInput (v : Plan.Terminal P bits) (t : ℕ) (oa : Aux A.bits)
    (room : 1+A.capacity+2*T.length v (c.group t)≤A.bits)
    (N : BitNetwork F p) (L : Library N) (hh : N.internal≤H) (hj : N.cells+(H-N.internal)≤J)
    (lut : A.lut+8*(L.count+2)≤2^w) : CellInput A c fit where
  count := T.length v (c.group t)
  pairSpace := room
  intervals := T.finiteRows v
  lo := (chunk c t).val*A.bits
  group := c.group t
  before := proposal A.capacity (T.length v (c.group t)) room oa false
  after := proposal A.capacity (T.length v (c.group t)) room oa true
  net := TraceCircuit.addPadding N (H-N.internal) (J-(N.cells+(H-N.internal)))
  lib := L.padded (H-N.internal) (J-(N.cells+(H-N.internal)))
  hidden := (fixed_capacities N hh hj).1
  cells := (fixed_capacities N hh hj).2
  lutSpace := lut

section Registers
variable (v : Plan.Terminal P bits) (t : ℕ) (oa : Aux A.bits)
  (fits : 1+A.capacity+2*T.length v (c.group t)≤A.bits)
  (N : BitNetwork F p) (L : Library N) (hh : N.internal≤H) (hj : N.cells+(H-N.internal)≤J)
  (lut : A.lut+8*(L.count+2)≤2^w)
set_option quotPrecheck false
local notation "z" => T.cellInput (fit:=fit) v t oa fits N L hh hj lut

theorem cellInput_before_read (j : ℕ) (bound : j<(z).count) :
    (z).before j=oa ⟨(z).aux.wiresEnd+j,by
      change 1+A.capacity+j<A.bits
      change j<T.length v (c.group t) at bound
      omega⟩ := by
  change j<T.length v (c.group t) at bound
  simp [cellInput,proposal,bound,CellInput.aux,TickPairHeader.layout]

theorem cellInput_after_read (j : ℕ) (bound : j<(z).count) :
    (z).after j=oa ⟨(z).aux.wiresEnd+(z).count+j,by
      change 1+A.capacity+T.length v (c.group t)+j<A.bits
      change j<T.length v (c.group t) at bound
      omega⟩ := by
  change j<T.length v (c.group t) at bound
  simp [cellInput,proposal,bound,CellInput.aux,TickPairHeader.layout,Nat.add_assoc]
end Registers

variable (v : Plan.Terminal P bits) (t : ℕ) (oa : Aux A.bits)
    (room : ∀ v g, 1+R.capacity+2*T.length v g≤A.bits)
    (weights : ∀ v g, Aux (T.length v g) → Aux (T.length v g) → ℕ → F)
    (reserve : A.capacity=R.capacity)
    (N : BitNetwork F p) (L : Library N) (hh : N.internal≤H) (hj : N.cells+(H-N.internal)≤J)
    (lut : A.lut+8*(L.count+2)≤2^w)

private theorem capacity_room {old new count bits : ℕ} (e : old=new)
    (h : 1+new+2*count≤bits) : 1+old+2*count≤bits := by simpa only [e] using h

set_option quotPrecheck false
local notation "x" => T.cellInput (fit:=fit) v t oa
  (capacity_room reserve (room v (c.group t))) N L hh hj lut

theorem cellInput_guard (oc nc : Aux A.bits) :
    TickChunkCheck.valid true (TickGroupScanBank.layout A.scan (x).lo (x).group) (x).intervals (x).before (x).after
      (chunkView A (x).lo (x).group oc) (chunkView A (x).lo (x).group nc) ↔
      guard (T.code v (c.group t) (chunk c t)) (atIndex (before (T.data room weights) v (c.group t) oa))
        (atIndex (after (T.data room weights) v (c.group t) oa)) oc nc := by
  apply T.physical_guard room weights t x v oa oc nc rfl rfl rfl
  · intro i
    simp only [cellInput,proposal,dite_eq_left i.isLt,Bool.false_eq_true,ite_false,Nat.zero_add]
    unfold before
    apply congrArg oa
    apply Fin.ext
    simp [reserve]
  · intro i
    simp only [cellInput,proposal,dite_eq_left i.isLt,ite_true]
    unfold after
    apply congrArg oa
    apply Fin.ext
    simp [reserve]
    rfl

theorem cellInput_aux : (x).aux=layout (T.data room weights) v (c.group t) :=
  T.auxiliary room weights v (c.group t) x reserve rfl

theorem cellInput_eval (pin : Fin p → Bool) : (x).net.eval pin=N.eval pin :=
  TraceCircuit.addPadding_eval ..


end ThreeFlat.Diagonal.TickPhaseModel.Buckets

end
end OAI
