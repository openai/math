import OAI.Geometry.Hirsch.Iteration

noncomputable section

open Filter

namespace OAI.Geometry.Hirsch

def exponent (depth stage : ℕ) := 4 * (4 * (depth + 1)) ^ stage

theorem exponent_pos (depth stage : ℕ) : 0 < exponent depth stage := by
  unfold exponent
  positivity

theorem exponent_mono (depth : ℕ) : Monotone (exponent depth) := by
  intro first last hh
  unfold exponent
  gcongr

def volume (root depth stage : ℕ) := root ^ exponent depth stage

theorem volume_mono {root : ℕ} (hr : 0 < root) (depth : ℕ) : Monotone (volume root depth) :=
  fun _ _ hh => Nat.pow_le_pow_right hr (exponent_mono depth hh)

theorem volume_succ (root depth stage : ℕ) :
    volume root depth (stage + 1) = volume root depth stage ^ (4 * (depth + 1)) := by
  unfold volume exponent
  rw [pow_succ, ← mul_assoc, pow_mul]

structure Supply (degree scale depth root : ℕ) where
  bank : ℕ → Bank
  span : ℕ → ℕ
  monotone : Monotone span
  tracer : ∀ idx ≤ degree, (bank idx).Tracer root (volume root depth 0) (span 0)
  drive : ∀ stage idx, stage + idx < degree → ∀ rows ≥ scale,
    let size := volume root depth stage
    let windows := volume root depth degree
    (bank idx).Drives (bank (idx + 1)) scale root (size ^ 2) windows size rows (span stage)
      (size ^ 4) (windows ^ 32 * rows) (span (stage + 1))

def rowBudget (windows mult scale stage : ℕ) := windows ^ (33 * (stage + 1)) * (mult * scale)

theorem Supply.iterate {degree scale depth root mult : ℕ} (supply : Supply degree scale depth root)
    (hr : 4 ≤ root) (hs : 2 ≤ scale) (hm : 1 ≤ mult)
    (hd : scale ^ degree ≤ volume root depth degree ^ depth) :
    ∀ stage idx, stage + idx ≤ degree →
      (supply.bank idx).Hard root scale (volume root depth stage)
        (rowBudget (volume root depth degree) mult scale stage) (supply.span stage)
        (mult * scale ^ stage) := by
  let size := volume root depth
  let windows := size degree
  let rows := rowBudget windows mult scale
  have mono : Monotone size := volume_mono (by omega) depth
  have hsize : ∀ stage, 4 ≤ size stage := fun stage =>
    hr.trans (Nat.le_self_pow (exponent_pos depth stage).ne' root)
  have hw : 4 ≤ windows := hsize degree
  have hbase : size 0 * (2 * (scale * mult) + 1) ≤ rows 0 := by
    have hl : 2 * (scale * mult) + 1 ≤ windows * (mult * scale) := by
      have hh := Nat.mul_le_mul_right (mult * scale) hw
      have hp : 0 < mult * scale := by positivity
      rw [mul_comm scale mult]
      omega
    calc
      _ ≤ windows * (windows * (mult * scale)) := Nat.mul_le_mul (mono (Nat.zero_le _)) hl
      _ = windows ^ 2 * (mult * scale) := by ring
      _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 33))
  have hrows : Monotone rows := by
    intro first last hle
    unfold rows rowBudget
    gcongr
  have hmin : ∀ stage, scale ≤ rows stage := by
    intro stage
    exact (Nat.le_mul_of_pos_left scale hm).trans (Nat.le_mul_of_pos_left _ (by positivity))
  have ht : ∀ idx ≤ degree, (supply.bank idx).Hard root scale (size 0) (rows 0) (supply.span 0) mult := by
    intro idx hi ep
    obtain ⟨pkg, hf, hh⟩ := (supply.tracer idx hi).terminal ep mult
    exact ⟨pkg, hf.mono le_rfl hbase le_rfl, hh⟩
  intro stage
  induction stage with
  | zero => simpa [size, windows, rows] using ht
  | succ stage ih =>
    intro idx hi
    let vol := size stage
    let tree := (2 * vol ^ 2 + 1) ^ depth
    have hv : 4 ≤ vol := hsize stage
    have htree : tree * vol ^ 4 ≤ size (stage + 1) := by
      change _ ≤ volume root depth (stage + 1)
      rw [volume_succ, mul_add, mul_one, pow_add, pow_mul]
      apply Nat.mul_le_mul_right
      apply Nat.pow_le_pow_left
      have hp : 4 ≤ vol ^ 2 := hv.trans (Nat.le_self_pow (by decide) _)
      change 2 * vol ^ 2 + 1 ≤ vol ^ 4
      nlinarith
    have htw : tree ≤ windows := (Nat.le_mul_of_pos_right tree (by positivity)).trans
      (htree.trans (mono (by omega)))
    have hrow : tree * (windows ^ 32 * rows stage) ≤ rows (stage + 1) := calc
      _ ≤ windows * (windows ^ 32 * rows stage) := Nat.mul_le_mul_right _ htw
      _ = _ := by
        unfold rows rowBudget
        rw [show 33 * (stage + 1 + 1) = 33 + 33 * (stage + 1) by omega, pow_add]
        rw [show windows ^ 33 = windows * windows ^ 32 from pow_succ' _ _]
        simp only [mul_assoc]
    have hter := (ht idx (by omega)).mono
      ((mono (Nat.zero_le stage)).trans (Nat.le_self_pow (by decide : 4 ≠ 0) vol))
      ((hrows (Nat.zero_le stage)).trans (Nat.le_mul_of_pos_left _ (by positivity : 0 < windows ^ 32)))
      (supply.monotone (Nat.zero_le (stage + 1)))
    have hcost : scale * (mult * scale ^ stage) = mult * scale ^ (stage + 1) := by
      rw [pow_succ', mul_left_comm]
    have hl : 2 ≤ scale * (mult * scale ^ stage) :=
      hs.trans (Nat.le_mul_of_pos_right _ (by positivity))
    have hu : scale * (mult * scale ^ stage) ≤ mult * windows ^ depth := by
      rw [hcost]
      exact Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by omega) (by omega)).trans hd)
    have hh := Bank.amplify (by positivity : 0 < vol ^ 2) hw hl hu hter
      (ih idx (by omega)) (ih (idx + 1) (by omega)) (supply.drive stage idx (by omega) _ (hmin stage))
    rw [hcost] at hh
    exact hh.mono htree hrow le_rfl

end OAI.Geometry.Hirsch
