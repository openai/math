import OAI.ThreeFlat.Diagonal.TraceSourceRectangle
import OAI.ThreeFlat.Diagonal.LaneCursorRows

namespace OAI
/-! # Bounded hidden reservations and contiguous external pins of each lane -/

namespace ThreeFlat.Diagonal.TraceSourceOwner

open LaneCursor

/-- Numerical high part of a row, under the actual bit-vector lane equivalence. -/
theorem lane_eq_iff {k low : ℕ} (v : Row k low) (lane : Lane k) :
    (splitRow _ _ v).1=lane ↔ v.val/2^low=(finFunctionFinEquiv lane).val := by
  change finFunctionFinEquiv.symm ((finProdFinEquiv.symm v : Fin (2^k) × Fin (2^low)).1) = lane ↔ _
  rw [Equiv.symm_apply_eq,Fin.ext_iff]
  rfl

/-- Hidden index inside a rectangular reservation for one entire lane. -/
def laneHiddenSlot (s : Shape) (low h : ℕ) : ℕ :=
  ((locate s h).1%2^low)*s.stride+(locate s h).2

def decodeLane (s : Shape) (low lane j : ℕ) : Option ℕ :=
  decode s (lane*2^low+j/s.stride) (j%s.stride)

theorem decodeLane_some (s : Shape) (fit : s.header+s.ticks ≤ 2*s.rows) (low lane : ℕ)
    {h : ℕ} (hi : h<s.count) (hl : (locate s h).1/2^low=lane) :
    decodeLane s low lane (laneHiddenSlot s low h) = some h := by
  have hj := (locate_spec s fit hi).2.1
  rw [decodeLane,laneHiddenSlot,pack_div hj,pack_mod hj,← hl,Nat.mul_comm _ (2^low),Nat.div_add_mod]
  exact (decode_some_iff s fit ..).2 ⟨hi,by simp⟩

/-- Inside a lane's finite reservation, the partial lookup succeeds exactly
on the image of the physically owned hidden coordinates. -/
theorem decodeLane_some_iff (s : Shape) (fit : s.header+s.ticks ≤ 2*s.rows)
    (low lane j h : ℕ) (bound : j<2^low*s.stride) :
    decodeLane s low lane j = some h ↔
      h<s.count ∧ (locate s h).1/2^low=lane ∧ laneHiddenSlot s low h=j := by
  constructor
  · intro hit
    obtain ⟨hi,pos⟩ := (decode_some_iff s fit ..).1 hit
    have st : 0<s.stride := by by_contra! absurd; simp [show s.stride=0 by omega] at bound
    have lowBound : j/s.stride < 2^low := (Nat.div_lt_iff_lt_mul st).2 bound
    refine ⟨hi,?_,?_⟩
    · rw [pos]; exact pack_div lowBound
    · simp only [laneHiddenSlot,pos,pack_mod lowBound]
      rw [Nat.mul_comm (j / s.stride),Nat.div_add_mod]
  · rintro ⟨hi,hl,pos⟩
    rw [←pos]
    exact decodeLane_some s fit low lane hi hl

theorem laneHiddenSlot_lt (s : Shape) (fit : s.header+s.ticks ≤ 2*s.rows)
    (low : ℕ) {h : ℕ} (hi : h<s.count) : laneHiddenSlot s low h < 2^low*s.stride :=
  pack_lt ((locate_spec s fit hi).2.1) (Nat.mod_lt _ (Nat.two_pow_pos _))

def hiddenFiber (s : Shape) (fit : s.header+s.ticks ≤ 2*s.rows) (low lane : ℕ) :
    {h : Fin s.count // (locate s h.val).1/2^low=lane} ↪ Fin (2^low*s.stride) where
  toFun h := ⟨laneHiddenSlot s low h.val.val,laneHiddenSlot_lt s fit _ h.val.isLt⟩
  inj' := by
    intro a b eq
    apply Subtype.ext
    apply Fin.ext
    exact Option.some.inj (((decodeLane_some s fit low lane a.val.isLt a.property).symm.trans
      (congrArg (decodeLane s low lane) (congrArg Fin.val eq))).trans
      (decodeLane_some s fit low lane b.val.isLt b.property))

def pinSpan (w low : ℕ) := (w*2)*2^low
def pinCount (S w low lane : ℕ) := min (pinSpan w low) (S*w-lane*pinSpan w low)

/-- Unlike hidden rows, external pins of each lane form a contiguous interval.
Their local ordinal is the bit address minus the lane's first bit. -/
def pinFiber (S w low lane : ℕ) :
    Fin (pinCount S w low lane) ≃ {j : Fin (S*w) // j.val/pinSpan w low=lane} where
  toFun i := by
    have h₁ := i.isLt.trans_le (min_le_left _ _)
    have h₂ := i.isLt.trans_le (min_le_right _ _)
    exact ⟨⟨lane*pinSpan w low+i.val,by omega⟩,pack_div h₁⟩
  invFun j := by
    have hw : 0<w := by by_contra! h; have := j.val.isLt; simp [show w=0 by omega] at this
    have hp : 0<pinSpan w low := Nat.mul_pos (Nat.mul_pos hw (by decide)) (Nat.two_pow_pos _)
    have he := Nat.div_add_mod j.val.val (pinSpan w low)
    rw [j.property,Nat.mul_comm (pinSpan w low) lane] at he
    exact ⟨j.val.val % pinSpan w low, lt_min (Nat.mod_lt _ hp) (by have := j.val.isLt; omega)⟩
  left_inv i := Fin.ext (pack_mod (i.isLt.trans_le (min_le_left _ _)))
  right_inv j := by
    apply Subtype.ext; apply Fin.ext
    change lane*pinSpan w low + j.val.val%pinSpan w low = j.val.val
    have hm := Nat.div_add_mod j.val.val (pinSpan w low)
    rw [j.property,Nat.mul_comm] at hm
    exact hm

@[simp] theorem pinFiber_apply_val (S w low lane : ℕ) (i : Fin (pinCount S w low lane)) :
    ((pinFiber S w low lane i).val).val = lane*pinSpan w low+i.val := rfl

@[simp] theorem pinFiber_symm_val (S w low lane : ℕ) (j : {j : Fin (S*w) // j.val/pinSpan w low=lane}) :
    ((pinFiber S w low lane).symm j).val = j.val.val%pinSpan w low := rfl

end ThreeFlat.Diagonal.TraceSourceOwner

end OAI
