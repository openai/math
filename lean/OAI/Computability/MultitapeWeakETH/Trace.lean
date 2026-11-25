import OAI.Computability.MultitapeWeakETH.Machine
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-! # The head-motion and pigeonhole parts of the coarse trace lemma -/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication

theorem head_step {A Q I : Type} (rule : TM.Rule A Q I) {x y : TM.Config A Q I}
    (h : TM.advance rule x = some y) (i : I) :
    |(y.tape i).pos - (x.tape i).pos| ≤ 1 := by
  cases he : rule x.pc (fun j => (x.tape j).view 0) with
  | none => simp [TM.advance, he] at h
  | some result =>
    obtain ⟨q, ops⟩ := result
    simp only [TM.advance, he, Option.map_some, Option.some.injEq] at h
    subst y
    change |(x.tape i).pos + (ops i).2.shift - (x.tape i).pos| ≤ 1
    rw [add_sub_cancel_left]
    cases (ops i).2 <;> decide

theorem head_displacement (pos : ℕ → ℤ) (step : ∀ t, |pos (t+1) - pos t| ≤ 1)
    (start steps : ℕ) : |pos (start+steps) - pos start| ≤ steps := by
  induction steps with
  | zero => simp
  | succ steps ih =>
    have h := abs_add_le (pos (start+steps+1) - pos (start+steps)) (pos (start+steps) - pos start)
    rw [sub_add_sub_cancel] at h
    have one := step (start + steps)
    rw [← Nat.add_assoc]
    push_cast
    omega

/-- During one epoch every visited cell lies in the starting block or one
of its two neighbors, including when the absolute head position is negative. -/
theorem epoch_blocks {b : ℕ} (hb : 0 < b) (pos : ℕ → ℤ)
    (step : ∀ t, |pos (t+1) - pos t| ≤ 1) (start t : ℕ) (ht : t ≤ b) :
    |pos (start+t)/(b:ℤ) - pos start/(b:ℤ)| ≤ 1 := by
  have h := (abs_le.mp (head_displacement pos step start t))
  have p : (0:ℤ) < b := by exact_mod_cast hb
  have le : (t:ℤ) ≤ b := by exact_mod_cast ht
  have up := Int.ediv_le_ediv p (show pos (start+t) ≤ pos start+b by omega)
  have down := Int.ediv_le_ediv p (show pos start ≤ pos (start+t)+b by omega)
  rw [Int.add_ediv_of_dvd_right (dvd_refl _), Int.ediv_self p.ne'] at up down
  exact abs_le.mpr ⟨by omega,by omega⟩

abbrev TraceCode (heads epochs : ℕ) := Fin epochs → Fin heads → Fin 3

/-- Encode the signed block change at each epoch boundary with one trit per head. -/
def recordBlocks {heads : ℕ} (epochs b : ℕ) (hb : 0 < b)
    (pos : Fin heads → ℕ → ℤ) (step : ∀ i t, |pos i (t+1) - pos i t| ≤ 1) :
    TraceCode heads epochs := fun j i =>
  let start := j.val*b
  let d := pos i (start+b)/(b:ℤ) - pos i start/(b:ℤ)
  have hd := abs_le.mp (epoch_blocks hb (pos i) (step i) start b le_rfl)
  ⟨(d+1).toNat, by dsimp [d,start] at *; omega⟩

theorem recordBlocks_decode {heads epochs b : ℕ} (hb : 0 < b)
    (pos : Fin heads → ℕ → ℤ) (step : ∀ i t, |pos i (t+1) - pos i t| ≤ 1)
    (j : Fin epochs) (i : Fin heads) :
    ((recordBlocks epochs b hb pos step j i).val : ℤ) - 1 =
      pos i ((j.val+1)*b)/(b:ℤ) - pos i (j.val*b)/(b:ℤ) := by
  have hd := abs_le.mp (epoch_blocks hb (pos i) (step i) (j.val*b) b le_rfl)
  simp only [recordBlocks, Nat.succ_mul]
  omega

theorem trace_count (heads epochs : ℕ) :
    Fintype.card (TraceCode heads epochs) = 3^(heads*epochs) := by
  simp [TraceCode,pow_mul]

/-- A single recorded trace retains the asserted fraction of all selected inputs. -/
theorem most_frequent_trace {I : Type*} {heads epochs : ℕ} (inputs : Finset I)
    (record : I → TraceCode heads epochs) :
    ∃ code, inputs.card ≤ 3^(heads*epochs) * (inputs.filter (fun i => record i = code)).card := by
  classical
  let count (code : TraceCode heads epochs) := (inputs.filter fun i => record i = code).card
  obtain ⟨best,_,maximal⟩ := Finset.exists_max_image Finset.univ count Finset.univ_nonempty
  refine ⟨best,?_⟩
  calc
    inputs.card = ∑ code, count code := Finset.card_eq_sum_card_fiberwise (fun _ _ => Finset.mem_univ _)
    _ ≤ ∑ _ : TraceCode heads epochs, count best :=
      Finset.sum_le_sum fun i _ => maximal i (Finset.mem_univ _)
    _ = _ := by simp [pow_mul,count,TraceCode]

end OAI.Computability.MultitapeWeakETH
