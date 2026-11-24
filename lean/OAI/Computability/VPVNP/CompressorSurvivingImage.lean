import OAI.Computability.VPVNP.CompressorSurvivingCells

/-!
# Closed form for the descriptor of a surviving wire

A source field of width `b` meets every target subdivision in the entire
target. Its live reference list is the initial segment of length `min b q`.
Each live target has exactly one reference, its own index.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep

open BurstRAM SliceRAM SliceSchedule ShrinkSliceArrays Compression

variable {w : ℕ}

/-- Direct numerical readout of a surviving row with one old field. -/
structure SurvivingWords (r : Row w) (b : ℕ) (mem : Memory w) : Prop where
  total : (mem r.total.val).val = b
  widths : ∀ j : Fin r.count.val, (mem (r.dst.val+j.val)).val = splitWidth b r.count.val j
  oldStart : (mem (r.bank.val+3+r.count.val)).val = 0
  newStarts : ∀ j : Fin r.count.val, (mem (r.bank.val+4+r.count.val+j.val)).val =
    j.val*(b/r.count.val) + min j.val (b%r.count.val)
  frames : ∀ j : Fin r.count.val,
    let a := frameHead r.bank.val 1 r.count.val + 3*j.val
    (mem a).val = j.val*(b/r.count.val) + min j.val (b%r.count.val) ∧
      (mem (a+1)).val = 0 ∧ (mem (a+2)).val = splitWidth b r.count.val j
  oldCount : (mem (r.bank.val+2)).val = min b r.count.val
  newCounts : ∀ j : Fin r.count.val, (mem (r.bank.val+3+j.val)).val =
    if j.val < min b r.count.val then 1 else 0
  oldRefs : ∀ j : Fin r.count.val,
    (mem (frameHead r.bank.val 1 r.count.val+3*r.count.val+j.val)).val = j.val
  newRefs : ∀ j : Fin r.count.val,
    (mem (frameHead r.bank.val 1 r.count.val+4*r.count.val+j.val)).val = j.val

private theorem start_eq (b q j : ℕ) (hj : j ≤ q) :
    ((List.ofFn (splitWidth b q)).take j).sum = j*(b/q)+min j (b%q) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hlt : j < q := hj
    have hi : j < (List.ofFn (splitWidth b q)).length := by simpa
    rw [List.sum_take_succ _ _ hi,ih hlt.le,List.getElem_ofFn,Nat.succ_mul]
    simp only [splitWidth]
    split <;> omega

private theorem live_iff (b q : ℕ) (j : Fin q) :
    splitWidth b q j ≠ 0 ↔ j.val < min b q := by
  by_cases hb : b < q
  · simp [splitWidth,Nat.div_eq_of_lt hb,Nat.mod_eq_of_lt hb,Nat.min_eq_left hb.le]
  · have hpos : 0 < b/q := Nat.div_pos_iff.mpr ⟨Nat.zero_lt_of_lt j.isLt,by omega⟩
    simp [splitWidth,Nat.min_eq_right (by omega : q ≤ b),j.isLt]
    split <;> omega

private def frameLength (b q : ℕ) (k : ℕ) :=
  (sliceAt [b] (List.ofFn (splitWidth b q)) k).length

private theorem frame_live {b q j : ℕ} (hj : j < q) :
    frameLength b q j ≠ 0 ↔ j < min b q := by
  rw [frameLength,surviving_sliceAt b q (Nat.zero_lt_of_lt hj) ⟨j,hj⟩]
  exact live_iff b q ⟨j,hj⟩

private theorem sourcePrefix (b q t : ℕ) (ht : t ≤ q) :
    adjPrefix w (frameLength b q) (· / q) 0 t =
      (List.range (min b t)).map (Fin.ofNat (2^w)) := by
  induction t with
  | zero => simp [adjPrefix]
  | succ t ih =>
    have hlt : t < q := ht
    have live : frameLength b q t ≠ 0 ∧ t / q = 0 ↔ t < b := by
      rw [frame_live hlt,Nat.div_eq_of_lt hlt]; omega
    rw [adjPrefix_succ,ih hlt.le,if_congr live rfl rfl]
    by_cases hl : t < b
    · rw [Nat.min_eq_right hl.le,Nat.min_eq_right hl,List.range_succ,List.map_append]
      simp [hl]
    · have hb : b ≤ t := by omega
      simp [hl,Nat.min_eq_left hb,Nat.min_eq_left (Nat.le_succ_of_le hb)]

private theorem targetPrefix (b q v t : ℕ) (ht : t ≤ q) :
    adjPrefix w (frameLength b q) (· % q) v t =
      if v < min b t then [Fin.ofNat (2^w) v] else [] := by
  induction t with
  | zero => simp [adjPrefix]
  | succ t ih =>
    have hlt : t < q := ht
    rw [adjPrefix_succ,ih hlt.le,Nat.mod_eq_of_lt hlt]
    by_cases hv : t = v
    · subst v
      have next : ¬ t < min b t := by omega
      simp only [next,ite_false,List.nil_append,frame_live hlt,and_true]
      apply if_congr _ rfl rfl
      omega
    · simp only [hv,and_false,ite_false,List.append_nil]
      apply if_congr _ rfl rfl
      omega

/-- The closed-form numerical fields are a complete stored interval schedule,
including the incidence ordering required by the endpoint readers. -/
theorem SurvivingWords.image {r : Row w} {b : ℕ} {mem : Memory w} (h : SurvivingWords r b mem)
    (positive : 0 < r.count.val) (fits : stop r.bank.val 1 r.count.val < 2^w) : Image r b mem := by
  let q := r.count.val
  let B := r.bank.val
  let a := frameHead B 1 q
  let ws := List.ofFn (splitWidth b q)
  have nq : ws.length = q := List.length_ofFn
  have bound : a+5*q < 2^w := by simpa only [stop,one_mul,a,B,q] using fits
  have ha : a = B+4+2*q := by simp [a,frameHead]
  have sub (j : ℕ) (hj : j < q) := surviving_sliceAt b q positive ⟨j,hj⟩
  refine ⟨h.total,h.widths,mem,mem,?_,fun _ _ _ => rfl⟩
  change Stored r.bank [b] ws mem mem
  constructor
  · intro i hi
    simp only [List.length_singleton] at hi ⊢
    have hz : i = 0 := by omega
    subst i
    simpa [nq] using h.oldStart
  · intro j hj
    rw [nq] at hj
    simpa [nq,start_eq b q j hj.le,ws] using h.newStarts ⟨j,hj⟩
  · intro j hj
    simp only [List.length_singleton,nq,one_mul] at hj ⊢
    rw [sub j hj]
    exact (h.frames ⟨j,hj⟩).2.2
  · intro j hj _
    simp only [List.length_singleton,nq,one_mul] at hj ⊢
    rw [sub j hj,start_eq b q j hj.le]
    exact ⟨(h.frames ⟨j,hj⟩).1,(h.frames ⟨j,hj⟩).2.1⟩
  · simp only [List.length_singleton,nq,one_mul]
    let bank := oldBank (adjacencyData r.bank 1 q)
    change bank.Represents mem (frameLength b q) (· / q) q
    intro v hv
    have size : bank.size.val = 1 := Nat.mod_eq_of_lt (by omega : 1 < 2^w)
    have hz : v.val = 0 := by have := Fin.lt_def.mp hv; omega
    have count : (bank.count v).val = B+2 := by
      change ((B+2) % 2^w + v.val) % 2^w = _
      rw [hz,Nat.add_zero,Nat.mod_mod,Nat.mod_eq_of_lt (by omega)]
    have row : (bank.row v).val = a+3*q := by
      have hr : bank.refHead.val = a+3*q := by
        change (a+3*(1*q)) % 2^w = _
        rw [one_mul,Nat.mod_eq_of_lt (by omega)]
      simp [AdjBank.row,Fin.val_add,Fin.val_mul,hz,hr,Nat.mod_eq_of_lt (by omega : a+3*q < 2^w)]
    rw [hz,sourcePrefix b q q le_rfl]
    constructor
    · rw [count,List.length_map,List.length_range]
      exact h.oldCount
    · intro i
      have hi : i.val < min b q := by simpa only [List.length_map,List.length_range] using i.isLt
      rw [row,List.getElem_map,List.getElem_range]
      apply Fin.ext
      exact (h.oldRefs ⟨i.val,by omega⟩).trans (Nat.mod_eq_of_lt (by omega)).symm
  · simp only [List.length_singleton,nq,one_mul]
    let bank := newBank (adjacencyData r.bank 1 q)
    change bank.Represents mem (frameLength b q) (· % q) q
    intro v hv
    have size : bank.size.val = q := Nat.mod_eq_of_lt (by omega : q < 2^w)
    have cap : bank.cap.val = 1 := Nat.mod_eq_of_lt (by omega : 1 < 2^w)
    have hlt : v.val < q := size ▸ Fin.lt_def.mp hv
    have count : (bank.count v).val = B+3+v.val := by
      change ((B+2+1) % 2^w + v.val) % 2^w = _
      rw [Nat.mod_add_mod,Nat.mod_eq_of_lt (by omega)]
    have row : (bank.row v).val = a+4*q+v.val := by
      have hr : bank.refHead.val = a+4*q := by
        change (a+4*(1*q)) % 2^w = _
        rw [one_mul,Nat.mod_eq_of_lt (by omega)]
      rw [AdjBank.row,Fin.val_add,Fin.val_mul,cap,hr,Nat.mul_one,Nat.add_mod_mod,Nat.mod_eq_of_lt (by omega)]
    rw [targetPrefix b q v.val q le_rfl]
    have hc := h.newCounts ⟨v.val,hlt⟩
    by_cases hlive : v.val < min b q
    · rw [ite_eq_left hlive] at hc ⊢
      constructor
      · rw [count]; exact hc
      · intro i
        have hz : i.val = 0 := by have hi : i.val < 1 := i.isLt; omega
        simp only [row,hz,Nat.add_zero,List.getElem_cons_zero]
        apply Fin.ext
        exact (h.newRefs ⟨v.val,hlt⟩).trans (Nat.mod_eq_of_lt v.isLt).symm
    · rw [ite_eq_right hlive] at hc ⊢
      exact ⟨count ▸ hc,fun i => Fin.elim0 i⟩
  · exact fun _ _ => rfl

namespace SurvivingCells

/-- Reading the thirteen worker cells at every target yields the physical
interval table. One target suffices to read the source's shared cells. -/
theorem words_of_fields {r : Row w} {b : ℕ} {mem : Memory w}
    (h : ∀ j : Fin r.count.val, ∀ f, (mem (address r j.val f)).val = value b r.count.val j.val f)
    (hq : 0 < r.count.val) : SurvivingWords r b mem := by
  let first : Fin r.count.val := ⟨0,hq⟩
  have piece (j : Fin r.count.val) : b/r.count.val + (if j.val < b%r.count.val then 1 else 0) =
      splitWidth b r.count.val j := by
    unfold splitWidth
    split <;> simp [*]
  constructor
  · exact h first 0
  · intro j
    exact (h j 1).trans (piece j)
  · exact h first 6
  · intro j
    exact h j 7
  · intro j
    exact ⟨h j 8,h j 9,(h j 10).trans (piece j)⟩
  · exact h first 4
  · intro j
    exact h j 5
  · intro j
    exact h j 11
  · intro j
    exact h j 12

end SurvivingCells

end CompressorRecords.ShrinkSliceSweep

end VPVNP
end Computability
end OAI
