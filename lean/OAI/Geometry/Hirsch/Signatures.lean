import OAI.Geometry.Hirsch.Modules

noncomputable section

namespace OAI.Geometry.Hirsch.Forest

structure Signature where
  Choice : Type
  [finite : Fintype Choice]
  [inhabited : Nonempty Choice]
  height : ℕ

attribute [instance] Signature.finite Signature.inhabited

namespace Signature

variable (V h : ℕ) [NeZero V]

def tower : ℕ → Signature
  | 0 => { Choice := Unit, height := 0 }
  | k+1 => { Choice := Upgrade V (tower k).Choice, height := h + 2*(tower k).height }

theorem depth (k : ℕ) : (tower V h k).height + h = 2^k * h := by
  induction k with
  | zero => simp [tower]
  | succ k ih =>
    rw [pow_succ', mul_assoc, ← ih]
    change h + 2 * (tower V h k).height + h = _
    omega

theorem degree (k : ℕ) : Fintype.card (tower V h k).Choice + 1 ≤ (2*V)^(3*k+1) := by
  have hv := NeZero.pos V
  induction k with
  | zero =>
    change Fintype.card Unit + 1 ≤ (2*V)^1
    rw [Fintype.card_unique, pow_one]
    omega
  | succ k ih =>
    change Fintype.card (Upgrade V (tower V h k).Choice) + 1 ≤ _
    rw [show 3*(k+1)+1 = 3+(3*k+1) by omega, pow_add]
    have hh : 4*V ≤ (2*V)^3 := by
      calc
        _ ≤ (2*V)^2 := by nlinarith
        _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
    apply le_trans _ (Nat.mul_le_mul hh ih)
    simp only [Upgrade,Position,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
    nlinarith

def growth (k : ℕ) := (3*k+2)*2^k

theorem bounds {k d : ℕ} (hk : k ≤ d) :
    2 * (tower V h k).height ≤ growth d * h ∧
    (3*k+1) * (tower V h k).height ≤ growth d * h := by
  have hh : (tower V h k).height ≤ 2^d*h := by
    calc
      _ ≤ 2^k*h := by rw [← depth V h k]; omega
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by decide) hk)
  unfold growth
  rw [mul_assoc]
  exact ⟨Nat.mul_le_mul (by omega) hh, Nat.mul_le_mul (by omega) hh⟩

def banks (k : ℕ) := bank (tower V h k).Choice (tower V h k).height

theorem trace_bound {k d : ℕ} (hk : k ≤ d) (limit : ℕ) :
    let span := growth d * h + (6*V+2)
    (banks V h k).Tracer limit ((limit+1)*(2*V)^span) span := by
  obtain ⟨prog,ha,hl,hc,hs⟩ := tracer (tower V h k).Choice (tower V h k).height limit
  obtain ⟨h₁,h₂⟩ := bounds V h hk
  refine ⟨prog,ha,hl,hc.trans (Nat.mul_le_mul_left _ ?_),fun idx => (hs idx).trans (by omega)⟩
  calc
    _ ≤ ((2*V)^(3*k+1))^(tower V h k).height := Nat.pow_le_pow_left (degree V h k) _
    _ ≤ _ := by rw [← pow_mul]; exact Nat.pow_le_pow_right (by have := NeZero.pos V; omega) (by omega)

end Signature

theorem scheduler_of_modules (input : ModuleTheorem) : SchedulerTheorem := by
  intro d rate
  obtain ⟨L,V,overhead,hL,hV,hr,ho,hs⟩ := input (Signature.growth d * rate)
  let : NeZero V := ⟨hV.ne'⟩
  refine ⟨L,V,Signature.growth d,6*V+2,overhead,hL,hV,hr,fun h hh => ?_⟩
  refine ⟨Signature.banks V h,fun k hk limit => Signature.trace_bound V h hk limit,fun k hk => ?_⟩
  let sig := Signature.tower V h k
  have hb := (Signature.bounds V h (Nat.succ_le_of_lt hk)).1
  change 2*(h+2*sig.height) ≤ _ at hb
  exact (schedules ho (hs h sig.height hh sig.Choice)).mono (by omega)

end OAI.Geometry.Hirsch.Forest
