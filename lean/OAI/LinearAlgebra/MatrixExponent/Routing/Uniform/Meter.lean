import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Tables

/-!
# Metered execution of the numeric queries

Steps are word-operation charges. Peak records the largest data
word, including partial powers, partial sums, and loop counters.
The two resource counters are instrumentation and are unnecessary
when producing the result.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
variable {M : ℕ}

structure Step where
  val : ℕ
  steps : ℕ
  peak : ℕ

private def powers (q : ℕ) : ℕ → Step
  | 0 => ⟨1, 8, max q 1⟩
  | n + 1 =>
    let z := powers q n
    let v := z.val * q
    ⟨v, z.steps + 8, max (n + 1) (max v z.peak)⟩

private theorem powers_val (q n : ℕ) : (powers q n).val = q ^ n := by
  induction n <;> simp [powers, pow_succ, *]

private theorem powers_steps (q n : ℕ) : (powers q n).steps = 8 * (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [powers, ih]; omega

private theorem grow {s t : ℕ} (hst : s ≤ t) (h : ℕ) :
    2 ^ (s * (h + 3)) ≤ 2 ^ (t * (h + 3)) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hst)

private theorem small (h k : ℕ) (hk : 1 ≤ k) : h + 2 < 2 ^ (k * (h + 3)) := by
  have := grow hk h
  rw [one_mul] at this
  have := Nat.lt_two_pow_self (n := h + 3)
  omega

private theorem powers_peak (q h n : ℕ) (hn : n ≤ h + 2) :
    (powers q n).peak < 2 ^ ((q + 1) * (h + 3)) := by
  have hs := small h (q + 1) (by omega)
  induction n with
  | zero =>
    have := power_lt q h 1 (by omega)
    simp only [powers, max_lt_iff, pow_one] at *
    omega
  | succ n ih =>
    simp only [powers, max_lt_iff, powers_val, ← pow_succ]
    exact ⟨hn.trans_lt hs, power_lt q h (n + 1) hn, ih (by omega)⟩

private def calcOp (h x y : ℕ) : Arith M → Step
  | .power q => powers q (min (h + 2) x)
  | .table (n := n) f =>
    let v := (Arith.table f).eval h x y
    ⟨v, 8, max n v⟩
  | ar =>
    let v := ar.eval h x y
    ⟨v, 8, v⟩

private theorem calcOp_val (a : Arith M) (h x y : ℕ) :
    (calcOp h x y a).val = a.eval h x y := by
  cases a <;> first | rfl | exact powers_val _ _

private theorem calcOp_steps (a : Arith M) (h x y : ℕ) :
    (calcOp h x y a).steps ≤ 16 * (h + 3) := by
  cases a <;> simp only [calcOp, powers_steps] <;> omega

private theorem calcOp_peak (a : Arith M) (h x y k : ℕ) (hw : a.width ≤ k)
    (hv : a.eval h x y < 2 ^ (k * (h + 3))) : (calcOp h x y a).peak < 2 ^ (k * (h + 3)) := by
  cases a <;> try {exact hv}
  case power q => exact (powers_peak q h _ (min_le_left ..)).trans_le (grow hw h)
  case table n f =>
    have : n ≤ k := by simp only [Arith.width] at hw; omega
    have hn : n < 2 ^ (k * (h + 3)) := Nat.lt_two_pow_self.trans_le
      (Nat.pow_le_pow_right (by decide) (by nlinarith))
    exact max_lt hn hv

private def accumulate (f : ℕ → Step) : ℕ → Step
  | 0 => ⟨0, 8, 0⟩
  | n + 1 =>
    let t := accumulate f n
    let z := f n
    let v := t.val + z.val
    ⟨v, t.steps + z.steps + 8, max (n + 1) (max v (max t.peak z.peak))⟩

private theorem accumulate_val (f : ℕ → Step) (n : ℕ) :
    (accumulate f n).val = ∑ j ∈ Finset.range n, (f j).val := by
  induction n <;> simp [accumulate, Finset.sum_range_succ, *]

private theorem accumulate_steps (f : ℕ → Step) (n c : ℕ) (hc : ∀ j, (f j).steps ≤ c) :
    (accumulate f n).steps ≤ 8 * (n + 1) + n * c := by
  induction n with
  | zero => simp [accumulate]
  | succ n ih =>
    have := hc n
    simp only [accumulate, Nat.succ_mul]
    omega

private theorem accumulate_peak (f : ℕ → Step) (n B : ℕ) (hn : n < B)
    (hv : (accumulate f n).val < B) (hf : ∀ j < n, (f j).peak < B) :
    (accumulate f n).peak < B := by
  induction n with
  | zero => exact hn
  | succ n ih =>
    have ht : (accumulate f n).val < B := (Nat.le_add_right _ _).trans_lt hv
    have hp := ih (by omega) ht (fun j hj => hf j (by omega))
    exact max_lt hn (max_lt hv (max_lt hp (hf n (by omega))))

def run : Index M → ℕ → ℕ → ℕ → ℕ → Step
  | .arg r, h, b, x, i =>
    let v := r.eval h b x i
    ⟨v, 1, max (h + 2) (max x (max b (max i v)))⟩
  | .op f u v, h, b, x, i =>
    let a := u.run h b x i
    let d := v.run h b x i
    let z := calcOp h a.val d.val f
    ⟨z.val, z.steps + a.steps + d.steps, max z.peak (max a.peak d.peak)⟩
  | .sum n u, h, b, x, i =>
    let a := n.run h b x i
    let z := accumulate (u.run h b x) (min (h + 2) a.val)
    ⟨z.val, a.steps + z.steps, max a.peak z.peak⟩

theorem run_val (e : Index M) (h b x i : ℕ) : (e.run h b x i).val = e.eval h b x i := by
  induction e generalizing i <;> simp only [run, eval, calcOp_val, accumulate_val, *]

theorem run_steps (e : Index M) (h b x i : ℕ) : (e.run h b x i).steps ≤ e.cost h := by
  induction e generalizing i with
  | arg r => exact le_rfl
  | op f u v hu hv => exact Nat.add_le_add (Nat.add_le_add (calcOp_steps _ _ _ _) (hu i)) (hv i)
  | sum n u hn hu =>
    let m := min (h + 2) (n.run h b x i).val
    have hm : m ≤ h + 2 := min_le_left ..
    have ht := accumulate_steps (u.run h b x) m _ hu
    have := Nat.mul_le_mul_right (u.cost h) hm
    have := hn i
    change (n.run h b x i).steps + (accumulate (u.run h b x) m).steps ≤
      16 * (h + 3) + n.cost h + (h + 2) * u.cost h
    omega

theorem run_peak (e : Index M) (h b x i : ℕ) (hb : b ≤ h + 2) (hx : x < 2 ^ (h + 2)) (hi : i ≤ h + 2) :
    (e.run h b x i).peak < 2 ^ (e.width * (h + 3)) := by
  induction e generalizing i with
  | arg r =>
    let e := arg (M := M) r
    have hs := small h e.width e.width_pos
    have hv := e.eval_lt h b x i hb hx hi
    have hw : 2 ^ (h + 2) ≤ 2 ^ (e.width * (h + 3)) := Nat.pow_le_pow_right (by decide)
      (by have := e.width_pos; nlinarith)
    exact max_lt hs (max_lt (hx.trans_le hw) (max_lt (hb.trans_lt hs) (max_lt (hi.trans_lt hs) hv)))
  | op f u v hu hv =>
    let e := op f u v
    have eu : u.width ≤ e.width := by simp only [e, width]; omega
    have ev : v.width ≤ e.width := by simp only [e, width]; omega
    have ef : f.width ≤ e.width := by simp only [e, width]; omega
    refine max_lt (calcOp_peak f h _ _ _ ef ?_)
      (max_lt ((hu i hi).trans_le (grow eu h)) ((hv i hi).trans_le (grow ev h)))
    rw [run_val, run_val]
    exact e.eval_lt h b x i hb hx hi
  | sum n u hn hu =>
    let e := sum n u
    have en : n.width ≤ e.width := by simp only [e, width]; omega
    have eu : u.width ≤ e.width := by simp only [e, width]; omega
    let m := min (h + 2) (n.run h b x i).val
    have hm : m ≤ h + 2 := min_le_left ..
    have hv : (e.run h b x i).val < 2 ^ (e.width * (h + 3)) := by rw [run_val]; exact e.eval_lt _ _ _ _ hb hx hi
    exact max_lt ((hn i hi).trans_le (grow en h))
      (accumulate_peak (u.run h b x) m _ (hm.trans_lt (small _ _ e.width_pos)) hv
        (fun j hj => (hu j (hj.le.trans hm)).trans_le (grow eu h)))

end OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.Index
