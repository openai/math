import OAI.ThreeFlat.RAM.TickNavigationRun

namespace OAI
/-! # Actual control words and unchanged raw inputs after group selection -/

namespace ThreeFlat.RAM.TickActiveROM
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickChronology
open scoped Fin.CommRing
variable {w : ℕ}

private def rangeEmb (s : ℕ) (fit : s+4 ≤ 2^w) : Fin 4 ↪ Word w where
  toFun := range w s
  inj' := by
    intro i j eq
    have hi := i.isLt
    have hj := j.isLt
    have v := congrArg Fin.val eq
    change ((s+i.val : ℕ) : Word w).val = ((s+j.val : ℕ) : Word w).val at v
    rw [Fin.val_cast_of_lt (by omega),Fin.val_cast_of_lt (by omega)] at v
    exact Fin.ext (by omega)

theorem bounds_low (B : Layout) (clock : Clock) (out : Memory w) (i : ℕ) (left : i < B.bounds)
    (fit : B.bounds+4 ≤ 2^w) : boundsMemory B clock out i = out i := by
  apply TickControlHeader.store_outside
  intro j
  have hj := j.isLt
  change i ≠ ((B.bounds+j.val : ℕ) : Word w).val
  rw [Fin.val_cast_of_lt (by omega)]
  omega

theorem bounds_high (B : Layout) (clock : Clock) (out : Memory w) (i : ℕ) (right : B.bounds+4 ≤ i)
    (fit : B.bounds+4 ≤ 2^w) : boundsMemory B clock out i = out i := by
  apply TickControlHeader.store_outside
  intro j
  have hj := j.isLt
  change i ≠ ((B.bounds+j.val : ℕ) : Word w).val
  rw [Fin.val_cast_of_lt (by omega)]
  omega

theorem selected_count (B : Layout) (clock : Clock) (group count : ℕ) (out : Memory w)
    (gf : group < 2^w) (gc : clock.groups < 2^w)
    (clockWord : out (B.clockWords : Word w).val = (group : Word w))
    (counter : group < clock.groups → out ((B.groupCounts+group : ℕ) : Word w).val = (count : Word w))
    (invalid : clock.groups ≤ group → count=0) :
    TickPairHeader.selected out B.clockWords B.groupCounts clock.groups = (count : Word w) := by
  rw [TickPairHeader.selected,clockWord]
  have eq : (group : Word w) < (clock.groups : Word w) ↔ group<clock.groups := by
    simp [Fin.lt_def,Fin.val_cast_of_lt gf,Fin.val_cast_of_lt gc]
  simp only [eq]
  by_cases h : group<clock.groups
  · simpa [h,Nat.cast_add] using counter h
  · simp [h,invalid (Nat.le_of_not_gt h)]

theorem bound_values (B : Layout) (clock : Clock) (out : Memory w) (count : ℕ)
    (space : 1+B.capacity+2*count ≤ B.bits) (fit : B.bounds+4 ≤ 2^w)
    (stored : TickPairHeader.selected out B.clockWords B.groupCounts clock.groups = (count : Word w))
    (i : Fin 4) :
    let L := TickPairHeader.layout B.capacity count space
    boundsMemory B clock out (B.bounds+i.val) =
      ![(L.wiresEnd : Word w),(L.pairsEnd : Word w),(B.oldAux+L.wiresEnd : ℕ),(B.oldAux+L.wiresEnd+count : ℕ)] i := by
  let dest := rangeEmb B.bounds fit
  have hi := i.isLt
  have addr : (dest i).val=B.bounds+i.val := Fin.val_cast_of_lt (by omega)
  rw [← addr]
  change TickControlHeader.store dest _ out (dest i).val = _
  rw [TickControlHeader.store_read,stored,TickPairHeader.values_layout B.capacity count B.oldAux space]

theorem auxiliary_header (B : Layout) (clock : Clock) (out : Memory w) (ph : Phase) (count : ℕ)
    (space : 1+B.capacity+2*count ≤ B.bits) (fit : B.bounds+4 ≤ 2^w)
    (split : B.control+4 ≤ B.bounds)
    (phase : out (B.control+2) = (ph.tag : Word w)) (marker : out (B.control+3) = 1)
    (stored : TickPairHeader.selected out B.clockWords B.groupCounts clock.groups = (count : Word w)) :
    ∀ j, boundsMemory B clock out (B.header w j).val =
      TickAuxRequestGen.header (TickPairHeader.layout B.capacity count space) ph true j := by
  intro j
  have bv := bound_values B clock out count space fit stored
  fin_cases j
  · change boundsMemory B clock out ((B.control+2 : ℕ) : Word w).val = (ph.tag : Word w)
    rw [Fin.val_cast_of_lt (by omega),bounds_low B clock out _ (by omega) fit,phase]
  · change boundsMemory B clock out ((B.control+3 : ℕ) : Word w).val = 1
    rw [Fin.val_cast_of_lt (by omega),bounds_low B clock out _ (by omega) fit,marker]
  · change boundsMemory B clock out (B.bounds : Word w).val =
      ((TickPairHeader.layout B.capacity count space).wiresEnd : Word w)
    rw [Fin.val_cast_of_lt (by omega)]
    simpa using bv 0
  · change boundsMemory B clock out ((B.bounds+1 : ℕ) : Word w).val =
      ((TickPairHeader.layout B.capacity count space).pairsEnd : Word w)
    rw [Fin.val_cast_of_lt (by omega)]
    simpa using bv 1


end ThreeFlat.RAM.TickActiveROM

end OAI
