import OAI.Hierarchy.TraceDistributionScale

namespace OAI
/-! # Register and descriptor sizes for repeated trace compression -/

namespace Hierarchy.TraceAdmission
open TraceDistribution Filter
open scoped Topology

/-- The product of the number of stages, the initial position count and the word length
fits in the descriptor budget. All coefficients are fixed before the word length grows. -/
theorem record_room {u s : ℕ → ℕ} (scale : Scale u s) (A : ℕ) :
    ∀ᶠ w : ℕ in atTop,
      A * (s w + 1) * (1 + (u w + 1 - w/2) * 2^(u w + 1 - w/2)) * (64*w + 1)
        ≤ 2^(3*w/5) := by
  have cap := (tendsto_order.mp scale.cap).2 2 (by norm_num)
  filter_upwards [cap, lane_room scale 1, factor_room scale (A * (4*4*2*65)) 3 1,
    eventually_ge_atTop 1] with w large blocks room positive
  have pos : (0:ℝ) < w := by exact_mod_cast (show 0<w by omega)
  have bound : u w ≤ 2*w := by
    exact_mod_cast ((div_lt_iff₀ pos).mp large).le
  let k := u w + 1 - w/2
  let e := max (w/2) (u w-w/2)
  have sk : s w ≤ k := by simpa [k] using blocks
  have kmax : k ≤ e+1 := by dsimp [k,e]; omega
  have bk : k + 1 ≤ 4*(w+1) := by dsimp [k]; omega
  have ex : 2^k ≤ 2*2^e := by
    simpa [pow_succ, Nat.mul_comm] using Nat.pow_le_pow_right (by decide : 0<2) kmax
  have vol : 1 + k*2^k ≤ (k+1)*2^k := by
    rw [Nat.add_mul, Nat.one_mul]
    have := Nat.two_pow_pos k
    omega
  change A * (s w + 1) * (1+k*2^k) * (64*w+1) ≤ _
  calc
    _ ≤ A * (4*(w+1)) * ((4*(w+1))*(2*2^e)) * (65*(w+1)) := by
      apply Nat.mul_le_mul _ (by omega)
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      exact vol.trans (Nat.mul_le_mul bk ex)
    _ = (A*(4*4*2*65))*(w+1)^3*1^(s w)*2^e := by ring
    _ ≤ _ := room

/-- The full multiplicity budget fits at the same scale as the adaptive stage records. -/
theorem multiplicity_small {u s : ℕ → ℕ} (scale : Scale u s) (R A d C : ℕ) :
    ∀ᶠ w : ℕ in atTop, R * ((2^(w/2) * (A*(w+1)^d) + 1) * C^(s w)) ≤ 2^(3*w/5) := by
  filter_upwards [factor_room scale (R*(A+1)) d C, eventually_ge_atTop 1] with w room hw
  let e := max (w/2) (u w-w/2)
  have expand : 2^(w/2) ≤ 2^e := Nat.pow_le_pow_right (by decide) (le_max_left ..)
  have positive : 1 ≤ (w+1)^d*2^e := Nat.mul_pos (Nat.pow_pos (by omega)) (Nat.two_pow_pos _)
  have packed : 2^(w/2)*(A*(w+1)^d)+1 ≤ (A+1)*(w+1)^d*2^e := by
    calc
      _ ≤ 2^e*(A*(w+1)^d)+(w+1)^d*2^e :=
        Nat.add_le_add (Nat.mul_le_mul_right _ expand) positive
      _ = _ := by ring
  calc
    _ ≤ R * (((A+1)*(w+1)^d*2^e)*C^(s w)) := by gcongr
    _ = (R*(A+1))*(w+1)^d*C^(s w)*2^e := by ring
    _ ≤ 2^(3*w/5) := room

/-- All stage multiplicities derived from the maximum old width fit in a native
`64*w`-bit word, including the largest byte array at positive characteristic. -/
theorem multiplicity_room {u s : ℕ → ℕ} (scale : Scale u s) (R A d C : ℕ) :
    ∀ᶠ w : ℕ in atTop, R * ((2^(w/2) * (A*(w+1)^d) + 1) * C^(s w)) < 2^(64*w) := by
  filter_upwards [multiplicity_small scale R A d C, eventually_ge_atTop 1] with w bound hw
  exact bound.trans_lt (Nat.pow_lt_pow_right (by decide) (by omega))

/-- The native parent, linked-list, and resource passes touch only an initial
lane times a stage, or a column of a per-factor row. With at most one direction
per bit position, their joint loop body has room at the three-fifths scale. -/
theorem descriptor_room {u s : ℕ→ℕ} (scale : Scale u s) (A : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ roots lanes dirs stages : ℕ,
      let axes := u w+1-w/2
      roots≤axes*2^axes → lanes≤2^axes → dirs≤w → stages≤A*(s w+1) →
      A*(1+(stages+1)*lanes+(lanes+1+roots)*(dirs+2)) ≤ 2^(3*w/5) := by
  filter_upwards [record_room scale ((A+1)*(A+4)*4)] with w room
  intro roots lanes dirs stages axes hr hl hd hs
  let v := axes*2^axes
  have vol : 2^axes ≤ 1+v := by
    by_cases z : axes=0
    · simp [v,z]
    · exact (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero z)).trans (by dsimp [v];omega)
  have lv : lanes≤1+v := hl.trans vol
  have rv : roots≤v := hr
  have ltStage : stages+1 ≤(A+1)*(s w+1) := by
    rw [Nat.add_mul,Nat.one_mul];omega
  have total : lanes+1+roots≤2*(1+v) := by omega
  have dirsBound : dirs+2≤2*(64*w+1) := by omega
  calc
    _ ≤ A*(1+(A+1)*(s w+1)*(1+v)+(2*(1+v))*(2*(64*w+1))) := by gcongr
    _ ≤ ((A+1)*(A+4)*4)*(s w+1)*(1+v)*(64*w+1) := by
      ring_nf
      omega
    _ ≤ _ := room

end Hierarchy.TraceAdmission

end OAI
