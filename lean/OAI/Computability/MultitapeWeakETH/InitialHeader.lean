import OAI.Computability.MultitapeWeakETH.IncidenceMemory
import OAI.Computability.VPVNP.CompressorCurrentGraph

/-! # Installing the level-zero header of the formula graph -/

namespace OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence

open VPVNP Compression CompressorRecords DescriptorSpace BurstRAM BlockHeaderRun
open scoped Classical Fin.CommRing
noncomputable section

def vertices (g r : ℕ) := 2*(g+(r+2))-2+2

theorem card_base (a g r : ℕ) : Fintype.card (inputState a g r).Base = vertices g r :=
  Fintype.card_fin _

/-- The six scalar cells and three retained startup bounds are immediately
followed, after the fixed scalar reservation, by the two pointer banks. -/
def headerValue (L : Layout) (a g r n j : ℕ) : ℕ :=
  if j < 6 then Scalars.values (.terminal a) (vertices g r) g (Fin.ofNat 6 j)
  else if j = 14 then endAddress L
  else if j = 28 then L.levels
  else if j = 29 then n
  else if j < L.shape.scalarFields then 0
  else if j < L.shape.scalarFields+6 then incidenceStart L 0+(j-L.shape.scalarFields)*rows a g r
  else arrayBase L 0+(j-(L.shape.scalarFields+6))*tableWords L

def levelMemory {w : ℕ} (L : Layout) (a g r n : ℕ) (m : Memory w) : Memory w :=
  install a g r (incidenceStart L 0) fun x =>
    if levelStart L 0 ≤ x ∧ x < incidenceStart L 0 then
      CursorRAM.encode w (headerValue L a g r n (x-levelStart L 0))
    else m x

theorem below {w : ℕ} (L : Layout) (a g r n : ℕ) (m : Memory w)
    {x : ℕ} (h : x < levelStart L 0) : levelMemory L a g r n m x = m x := by
  have upper : x < incidenceStart L 0 := by unfold incidenceStart; omega
  unfold levelMemory
  rw [install_outside _ _ _ _ _ _ (.inl upper),ite_eq_right (by omega)]

private theorem field {w : ℕ} (L : Layout) (a g r n : ℕ) (m : Memory w)
    {j : ℕ} (hj : j < levelHeaderWords L) :
    levelMemory L a g r n m (levelStart L 0+j) = CursorRAM.encode w (headerValue L a g r n j) := by
  have high : levelStart L 0+j < incidenceStart L 0 := Nat.add_lt_add_left hj _
  unfold levelMemory
  rw [install_outside _ _ _ _ _ _ (.inl high),ite_eq_left ⟨Nat.le_add_right ..,high⟩,Nat.add_sub_cancel_left]

private theorem scalar {w : ℕ} (L : Layout) (a g r n : ℕ) (m : Memory w)
    (fields : 30 ≤ L.shape.scalarFields) (j : Fin 6) :
    levelMemory L a g r n m (levelStart L 0+j.val) =
      CursorRAM.encode w (Scalars.values (.terminal a) (vertices g r) g j) := by
  have hj := j.isLt
  rw [field _ _ _ _ _ _ (by unfold levelHeaderWords; omega),headerValue,ite_eq_left hj,
    show Fin.ofNat 6 j.val = j from Fin.ext (Nat.mod_eq_of_lt hj)]

private theorem wordAddr {w : ℕ} (L : Layout) (j : ℕ) (h : levelStart L 0+j < 2^w) :
    (header w L 0+(j : Word w)).val = levelStart L 0+j := by
  unfold header
  rw [← Nat.cast_add,Fin.val_natCast,Nat.mod_eq_of_lt h]

theorem role {w : ℕ} (L : Layout) (a g r n : ℕ) (m : Memory w)
    (fields : 30 ≤ L.shape.scalarFields) :
    levelMemory L a g r n m (levelStart L 0+27) = 0 := by
  rw [field _ _ _ _ _ _ (by unfold levelHeaderWords; omega)]
  simp [headerValue,show 27 < L.shape.scalarFields by omega]

/-- The same memory that supplies the array contents also supplies every
scalar and pointer read by a native shrinking or refresh pass. -/
theorem current {w : ℕ} (L : Layout) (a g r n : ℕ) (m : Memory w)
    (fields : 30 ≤ L.shape.scalarFields) (levels : 0 < L.levels)
    (fit : endAddress L < 2^w) (lengthFit : n < 2^w) (levelsFit : L.levels < 2^w)
    (scalarFit : Scalars.Fits (.terminal a) (vertices g r) g w)
    (pos : vertices g r * 2^g = L.positions) (slots : rows a g r ≤ slotCapacity L) :
    CurrentGraph.Current L 0 (inputState a g r) n (levelMemory L a g r n m) := by
  let head := levelStart L 0
  let mem := levelMemory L a g r n m
  have room := packed_incidence_room L fit ⟨0,levels⟩ slots
  have headRoom : head+levelHeaderWords L < 2^w := (Nat.le_add_right ..).trans_lt room
  have scalarAt := scalar L a g r n m fields
  have read (j : Fin 6) : mem (header w L 0+(j.val : Word w)).val =
      CursorRAM.encode w (Scalars.values (.terminal a) (vertices g r) g j) := by
    have hj := j.isLt
    rw [wordAddr L _ (by change head+j.val < _; refine lt_trans ?_ headRoom; unfold levelHeaderWords; omega)]
    exact scalarAt j
  refine ⟨?_,?_,?_,?_⟩
  · rw [card_base]
    intro j
    change (mem (header w L 0+(j.val : Word w)).val).val = _
    rw [read,Fin.val_ofNat,Nat.mod_eq_of_lt (scalarFit j)]
  · rw [slot_count]
    constructor
    · intro c
      have hc := c.isLt
      rw [incidenceHead,Nat.add_assoc,field _ _ _ _ _ _ (by unfold levelHeaderWords; omega)]
      simp only [headerValue,ite_eq_right (by omega : ¬L.shape.scalarFields+c.val < 6),
        ite_eq_right (by omega : L.shape.scalarFields+c.val ≠ 14),
        ite_eq_right (by omega : L.shape.scalarFields+c.val ≠ 28),
        ite_eq_right (by omega : L.shape.scalarFields+c.val ≠ 29),
        ite_eq_right (by omega : ¬L.shape.scalarFields+c.val < L.shape.scalarFields),
        ite_eq_left (by omega : L.shape.scalarFields+c.val < L.shape.scalarFields+6),Nat.add_sub_cancel_left]
      rfl
    · intro c
      have hc := c.isLt
      change levelMemory L a g r n m (levelStart L 0+L.shape.scalarFields+6+c.val) = _
      rw [show levelStart L 0+L.shape.scalarFields+6+c.val = levelStart L 0+(L.shape.scalarFields+6+c.val) by omega,
        field _ _ _ _ _ _ (by unfold levelHeaderWords; omega)]
      simp only [headerValue,ite_eq_right (by omega : ¬L.shape.scalarFields+6+c.val < 6),
        ite_eq_right (by omega : L.shape.scalarFields+6+c.val ≠ 14),
        ite_eq_right (by omega : L.shape.scalarFields+6+c.val ≠ 28),
        ite_eq_right (by omega : L.shape.scalarFields+6+c.val ≠ 29),
        ite_eq_right (by omega : ¬L.shape.scalarFields+6+c.val < L.shape.scalarFields),
        ite_eq_right (by omega : ¬L.shape.scalarFields+6+c.val < L.shape.scalarFields+6),Nat.add_sub_cancel_left]
      rfl
  · exact represents L 0 _ room.le
  · constructor
    · refine ⟨vertices g r,2^a,2^g,⟨?_,?_,?_⟩,pos⟩
      · have h := read 0
        change mem (header w L 0+0).val = (vertices g r : Word w) at h
        simpa only [add_zero] using h
      · exact read 1
      · exact read 2
    · rw [field _ _ _ _ _ _ (by unfold levelHeaderWords; omega)]
      simp [headerValue,Nat.mod_eq_of_lt fit]
    · rw [field _ _ _ _ _ _ (by unfold levelHeaderWords; omega)]
      simp [headerValue,Nat.mod_eq_of_lt levelsFit]
    · rw [field _ _ _ _ _ _ (by unfold levelHeaderWords; omega)]
      simp [headerValue,Nat.mod_eq_of_lt lengthFit]

end
end OAI.Computability.MultitapeWeakETH.CNFNetwork.InitialIncidence
