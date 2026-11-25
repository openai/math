import OAI.Computability.NearSquareRoot.PhysicalWalshRecursion
import OAI.Computability.NearSquareRoot.SelectedWalsh

/-! # Integer clocks and arena sizes for the recursive Walsh program

A body calls each child with an integral clock and stack allowance. Rounding the
local real upper bound down preserves every integral instruction count, so the
analytic recurrence applies without a new rounding charge at each child.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

/-- Total integral allowance for a tree of ratio-`W` calls. Using one call
per level with the local arena size gives the peak along a live stack path. -/
noncomputable def charge (W calls : ℕ) (localCost : ℕ → ℝ → ℝ) : ℕ → ℝ → ℕ
  | 0, V => ⌊localCost 0 V⌋₊
  | j+1, V => ⌊localCost (j+1) V⌋₊ + calls * charge W calls localCost j (V/W)

theorem charge_mono (W calls : ℕ) (c : ℕ → ℝ → ℝ)
    (mono : ∀ j, Monotone (c j)) (j : ℕ) : Monotone (charge W calls c j) := by
  induction j with
  | zero => exact fun _ _ h => Nat.floor_mono (mono 0 h)
  | succ j ih =>
    exact fun _ _ h => Nat.add_le_add (Nat.floor_mono (mono (j+1) h))
      (Nat.mul_le_mul_left _ (ih (div_le_div_of_nonneg_right h (Nat.cast_nonneg _))))

/-- Time taken by a single level of the selected Walsh recurrence. -/
noncomputable def localTime (A : ℕ) (ρ c L P : ℝ) (j : ℕ) (V : ℝ) : ℝ :=
  c * L * V * (1 + ((2 : ℝ) * (A : ℝ)^j)^ρ) + P

/-- Resident slots and fixed setup at a single level. -/
def localSpace (c P : ℝ) (_ : ℕ) (V : ℝ) : ℝ := c * V + P

theorem localTime_mono {A : ℕ} {ρ c L P : ℝ} (hc : 0 ≤ c) (hL : 0 ≤ L) (j : ℕ) :
    Monotone (localTime A ρ c L P j) := by
  intro V V' h
  unfold localTime
  exact add_le_add (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left h (mul_nonneg hc hL)) (by positivity)) le_rfl

theorem localSpace_mono {c P : ℝ} (hc : 0 ≤ c) (j : ℕ) :
    Monotone (localSpace c P j) := fun _ _ h => add_le_add (mul_le_mul_of_nonneg_left h hc) le_rfl

/-- The integer clock used by the physical program meets the real recurrence
in the analytic cost theorem. -/
theorem charge_time_recurrence {A W calls : ℕ} {ρ c L P : ℝ}
    (hc : 0 ≤ c) (hL : 0 ≤ L) (hP : 0 ≤ P) :
    WalshPieceRecurrence A W calls ρ c L P
      (fun j V => (charge W calls (localTime A ρ c L P) j V : ℝ)) where
  base V hV := by
    simpa only [charge, localTime, pow_zero, mul_one] using
      (Nat.floor_le (show 0 ≤ localTime A ρ c L P 0 V by unfold localTime; positivity))
  step j V hV := by
    simp only [charge, Nat.cast_add, Nat.cast_mul]
    exact add_le_add (Nat.floor_le (show 0 ≤ localTime A ρ c L P (j+1) V by
      unfold localTime; positivity)) le_rfl

theorem charge_space_base {W : ℕ} {c P V : ℝ} (hc : 0 ≤ c) (hP : 0 ≤ P) (hV : 0 ≤ V) :
    (charge W 1 (localSpace c P) 0 V : ℝ) ≤ c*V+P := by
  change (⌊c*V+P⌋₊ : ℝ) ≤ c*V+P
  exact Nat.floor_le (by positivity)

theorem charge_space_step {W : ℕ} {c P V : ℝ} (hc : 0 ≤ c) (hP : 0 ≤ P) (hV : 0 ≤ V)
    (j : ℕ) : (charge W 1 (localSpace c P) (j+1) V : ℝ) ≤
      c*V+P + (charge W 1 (localSpace c P) j (V/W) : ℝ) := by
  simp only [charge, one_mul, Nat.cast_add, localSpace]
  exact add_le_add (Nat.floor_le (show 0 ≤ c*V+P by positivity)) le_rfl

variable {X U K : Type*} {d : RecSpec X U} {W calls C : ℕ}

/-- The outer width and setup parameters are constant during a recursive
piece. Each child has one fewer level and at most a `1/W` share of the volume. -/
structure ChargeLayout (d : RecSpec X U) (W : ℕ) (K : Type*) where
  key : U → K
  volume : U → ℝ
  nonnegative : ∀ u, 0 ≤ volume u
  childKey : ∀ {u v}, d.child u v → key v = key u
  childLevel : ∀ {u v}, d.child u v → d.level v + 1 = d.level u
  childVolume : ∀ {u v}, d.child u v → volume v ≤ volume u / W

/-- A parent's charge indexed by its actual fixed-point word width and layout. -/
noncomputable def ChargeLayout.budget (l : ChargeLayout d W K) (b : ℕ)
    (c : K → ℕ → ℝ → ℝ) (u : U) : ℕ := charge W b (c (l.key u)) (d.level u) (l.volume u)

/-- Discharge the natural recurrences required by the command's
`RecSpec.tie` using integral budgets at every physical child entry. -/
noncomputable def ChargeLayout.recurrence (l : ChargeLayout d W K)
    (t s : K → ℕ → ℝ → ℝ)
    (tmono : ∀ k j, Monotone (t k j)) (smono : ∀ k j, Monotone (s k j))
    (ht : ∀ u, ((C * (d.scan u + 1) : ℕ) : ℝ) ≤ t (l.key u) (d.level u) (l.volume u))
    (hs : ∀ u, ((C * (d.arena u + 1) : ℕ) : ℝ) ≤ s (l.key u) (d.level u) (l.volume u)) :
    d.Recurrence calls C (l.budget calls t) (l.budget 1 s) where
  childTime u := charge W calls (t (l.key u)) (d.level u - 1) (l.volume u/W)
  childSpace u := charge W 1 (s (l.key u)) (d.level u - 1) (l.volume u/W)
  boundsTime {u v} h := by
    have hlev := l.childLevel h
    simp only [ChargeLayout.budget, l.childKey h, ← hlev, Nat.add_sub_cancel]
    exact charge_mono _ _ _ (tmono _) _ (l.childVolume h)
  boundsSpace {u v} h := by
    have hlev := l.childLevel h
    simp only [ChargeLayout.budget, l.childKey h, ← hlev, Nat.add_sub_cancel]
    exact charge_mono _ _ _ (smono _) _ (l.childVolume h)
  baseTime u h := by simpa only [ChargeLayout.budget, h, charge] using Nat.le_floor (ht u)
  baseSpace u h := by simpa only [ChargeLayout.budget, h, charge] using Nat.le_floor (hs u)
  stepTime u h := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
    simpa only [ChargeLayout.budget, hj, charge, Nat.succ_sub_one] using
      Nat.add_le_add_right (Nat.le_floor (ht u)) (calls *
        charge W calls (t (l.key u)) (d.level u-1) (l.volume u/W))
  stepSpace u h := by
    obtain ⟨j, hj⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt h)
    simpa only [ChargeLayout.budget, hj, charge, Nat.succ_sub_one, one_mul] using
      Nat.add_le_add_right (Nat.le_floor (hs u)) (charge W 1 (s (l.key u)) (d.level u-1) (l.volume u/W))

/-- The same charged natural budgets satisfy the closed-form time estimate
uniformly over overhead and setup. -/
theorem charge_time_bound {A W calls : ℕ} {ρ c : ℝ} (ha : 1 ≤ A) (hw : 0 < W)
    (hρ : 0 ≤ ρ) (hc : 0 ≤ c) (saving : (calls : ℝ)/W < (A : ℝ)^ρ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L P : ℝ, 0 ≤ L → 0 ≤ P → ∀ j V, 0 ≤ V →
      (charge W calls (localTime A ρ c L P) j V : ℝ) ≤
        B*L*V*((2:ℝ)*(A:ℝ)^j)^ρ + P*(calls+1:ℝ)^j := by
  obtain ⟨B,hB,bound⟩ := walsh_piece_time_bound ha hw hρ hc saving
  exact ⟨B,hB,fun L P hL hP => bound L P hL hP _ (charge_time_recurrence hc hL hP)⟩

theorem charge_space_bound {W : ℕ} {c P : ℝ} (hw : 2 ≤ W) (hc : 0 ≤ c) (hP : 0 ≤ P)
    (j : ℕ) (V : ℝ) (hV : 0 ≤ V) :
    (charge W 1 (localSpace c P) j V : ℝ) ≤ 2*c*V + (j+1:ℝ)*P :=
  walsh_piece_space_bound hw hc (fun j V => (charge W 1 (localSpace c P) j V : ℝ))
    (fun _ => charge_space_base hc hP) (fun j _ h => charge_space_step hc hP h j) j V hV

/-- The compiler constant multiplies the full resource certificate once,
without changing the branching factor in the time recurrence. -/
def RecSpec.Recurrence.scale {T S : U → ℕ} (h : d.Recurrence calls C T S) (D : ℕ) :
    d.Recurrence calls (D*C) (fun u => D*T u) (fun u => D*S u) where
  childTime u := D*h.childTime u
  childSpace u := D*h.childSpace u
  boundsTime {u v} hv := Nat.mul_le_mul_left _ (h.boundsTime hv)
  boundsSpace {u v} hv := Nat.mul_le_mul_left _ (h.boundsSpace hv)
  baseTime u hu := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left D (h.baseTime u hu)
  baseSpace u hu := by simpa [Nat.mul_assoc] using Nat.mul_le_mul_left D (h.baseSpace u hu)
  stepTime u hu := by
    simpa [Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using
      Nat.mul_le_mul_left D (h.stepTime u hu)
  stepSpace u hu := by simpa [Nat.mul_add, Nat.mul_assoc] using Nat.mul_le_mul_left D (h.stepSpace u hu)

open IntegerMultiplication Code Space

/-- The same charge functions tested against the analytic recurrence are the
budgets of the compiled recursive task. Scan and arena assumptions refer to
the unscaled local budgets of individual layout instances. -/
theorem ChargeLayout.bounded (l : ChargeLayout d W K)
    (one : BoundedTask (fun x : d.Base => d.scan (d.world x.val))
      (fun x => d.arena (d.world x.val)) (fun x => d.payload x.val) (fun x => d.reply x.val))
    (step : OpenRun d.meter calls (fun x : d.Step => d.world x.val)
      (fun x => d.payload x.val) (fun x => d.reply x.val))
    (t s : K → ℕ → ℝ → ℝ)
    (tmono : ∀ k j, Monotone (t k j)) (smono : ∀ k j, Monotone (s k j))
    (ht : ∀ u, (d.scan u : ℝ) + 1 ≤ t (l.key u) (d.level u) (l.volume u))
    (hs : ∀ u, (d.arena u : ℝ) + 1 ≤ s (l.key u) (d.level u) (l.volume u)) :
    BoundedTask (l.budget calls t ∘ d.world) (l.budget 1 s ∘ d.world) d.query d.reply := by
  obtain ⟨cmd,D,h⟩ := d.tie one step
  let cert := l.recurrence (C := 1) (calls := calls) t s tmono smono
    (by simpa only [one_mul, Nat.cast_add, Nat.cast_one] using ht)
    (by simpa only [one_mul, Nat.cast_add, Nat.cast_one] using hs)
  have hrec := cert.scale D
  simp only [Nat.mul_one] at hrec
  refine ⟨cmd,D,fun x env p b hp => ?_⟩
  exact (h _ _ hrec x env p b hp).mono (Nat.mul_le_mul_left _ (Nat.le_succ _))
    (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.le_succ _)) _) (Nat.mul_le_mul_left _ (Nat.le_succ _))

end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
