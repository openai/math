import OAI.ThreeFlat.Diagonal.TraceSourceRectangle

namespace OAI
/-! # A single row-scale width for every reverse-lookup candidate -/

namespace ThreeFlat.Diagonal.TraceSourceOwner

/-- Even a padding slot has a bounded reverse candidate. The estimate contains
one factor of the row count and the polynomial width of a row. -/
theorem unplace_lt_capacity (s : Shape) {v j : ℕ} (hv : v<s.rows) (hj : j<s.stride) :
    unplace s v j < s.count+s.rows*s.stride+1 := by
  unfold Shape.stride at hj
  by_cases h₁ : j<2*s.cpu
  · rw [unplace,appendAt_left _ _ h₁]
    have k : 0<s.cpu := by by_contra! h; simp [show s.cpu=0 by omega] at h₁
    have low : j/s.cpu < 2 := (Nat.div_lt_iff_lt_mul k).2 h₁
    have high : 2*v+j/s.cpu-s.header < 2*s.rows := by omega
    have z := pack_lt (Nat.mod_lt j k) high
    have le : 2*s.rows*s.cpu ≤ s.rows*s.stride := by
      rw [show 2*s.rows*s.cpu=s.rows*(2*s.cpu) by ring]
      apply Nat.mul_le_mul_left
      unfold Shape.stride
      omega
    omega
  let a := j-2*s.cpu
  have eq : j=2*s.cpu+a := by dsimp [a]; omega
  rw [unplace,eq,appendAt_right]
  by_cases h₂ : a<s.layers*s.track
  · rw [appendAt_left _ _ h₂]
    have k : 0<s.track := by by_contra! h; simp [show s.track=0 by omega] at h₂
    have idx := pack_lt (pack_lt (Nat.mod_lt a k) hv) ((Nat.div_lt_iff_lt_mul k).2 h₂)
    unfold Shape.count
    omega
  let b := a-s.layers*s.track
  have eq₂ : a=s.layers*s.track+b := by dsimp [b]; omega
  rw [eq₂,appendAt_right]
  by_cases h₃ : b<s.edge
  · rw [appendAt_left _ _ h₃]
    have idx := pack_lt h₃ hv
    have le : s.rows*s.edge ≤ s.rows*s.stride := by
      apply Nat.mul_le_mul_left
      unfold Shape.stride
      omega
    unfold Shape.count
    omega
  let c := b-s.edge
  have eq₃ : b=s.edge+c := by dsimp [c]; omega
  rw [eq₃,appendAt_right]
  by_cases h₄ : c<s.copy
  · rw [appendAt_left _ _ h₄]
    have idx := pack_lt h₄ hv
    unfold Shape.count
    omega
  let e := c-s.copy
  have eq₄ : c=s.copy+e := by dsimp [e]; omega
  rw [eq₄,appendAt_right]
  have he : e<s.gates := by omega
  have idx := pack_lt he hv
  unfold Shape.count
  omega

end ThreeFlat.Diagonal.TraceSourceOwner

end OAI
