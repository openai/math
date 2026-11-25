import OAI.LinearAlgebra.MatrixExponent.Network.Dense
import OAI.LinearAlgebra.MatrixExponent.Lookup.Single
import OAI.LinearAlgebra.MatrixExponent.Diagram.Substitute

/-!
# Substituting batched lookups into a wide network

A vertex of arity `t` uses batches of `2^t` copies. Repeating these to reach
a common batch size `2^u` costs at most a constant times `(1 + u)^(p - 1)`
per incident bit per copy, with one extra unit per vertex.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Lookup

variable {K : Type} [Field K] {a b : Wire}

private def paired (k : Val a → Val b → K) (x : Val (.pair a b)) (_ : Val .unit) : K :=
  k x.1 x.2

private theorem power_paired (k : Val a → Val b → K) (d : ℕ)
    (x : Val (.pair (copies a d) (copies b d))) :
    power (paired k) d (zipCopies a b d x) (unitCopies d) = power k d x.1 x.2 := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [power, paired, zipCopies, unitCopies, ih]

private theorem split_batch {k : Val a → Val b → K} {t v : ℕ}
    (h : Net K (tree t (.pair a b)) .unit
      (fun x _ => ((flatten t x).map (fun z => k z.1 z.2)).prod) v) :
    Net K (copies a (2 ^ t)) (copies b (2 ^ t)) (power k (2 ^ t)) (v + 2 ^ t * wd b) := by
  let d := 2 ^ t
  have g : Net K (copies (.pair a b) d) (copies .unit d) (power (paired k) d) v :=
    h.rewire (.treeCopies (.pair a b) t) (.unitCopies d)
      (fun x _ => power_tree (paired k) t x (unitCopies d))
  have j := (g.pre (.zipCopies a b d)).post (.unitCopies d)
  simp only [power_paired] at j
  simpa only [wd_copies] using j.curry

private theorem vertex_cost {C p : ℝ} (hC : 1 ≤ C) (hp : 1 ≤ p) {t u v b : ℕ}
    (ht : t ≤ u) (hb : b ≤ t) (hv : (v : ℝ) ≤ C * (2 : ℝ) ^ t * (1 + (t : ℝ)) ^ p) :
    ((2 ^ (u - t) * (v + 2 ^ t * b) : ℕ) : ℝ) ≤
      (C + 1) * (2 : ℝ) ^ u * (1 + (u : ℝ)) ^ (p - 1) * (1 + (t : ℝ)) := by
  have hbase : 1 ≤ 1 + (t : ℝ) := by simp
  have hb' : (b : ℝ) ≤ (1 + (t : ℝ)) ^ p := calc
    (b : ℝ) ≤ (t : ℝ) := by exact_mod_cast hb
    _ ≤ 1 + (t : ℝ) := by linarith
    _ ≤ _ := by simpa using Real.rpow_le_rpow_of_exponent_le hbase hp
  have hpow : (2 : ℝ) ^ (u - t) * 2 ^ t = 2 ^ u := by rw [← pow_add, Nat.sub_add_cancel ht]
  have hsplit : (1 + (t : ℝ)) ^ p = (1 + (t : ℝ)) ^ (p - 1) * (1 + (t : ℝ)) := by
    rw [Real.rpow_sub (by positivity), Real.rpow_one, div_mul_cancel₀ _ (by positivity)]
  push_cast
  calc
    _ ≤ 2 ^ (u - t) * (C * 2 ^ t * (1 + (t : ℝ)) ^ p + 2 ^ t * (1 + (t : ℝ)) ^ p) := by gcongr
    _ = (C + 1) * (2 : ℝ) ^ u * (1 + (t : ℝ)) ^ (p - 1) * (1 + (t : ℝ)) := by rw [← hpow, hsplit]; ring
    _ ≤ _ := by gcongr

/-- A uniform sorting bound suffices for arbitrary labels and all extensions. -/
theorem lookup_network {F : Type} [Field F] {p : ℝ} (hp : 1 ≤ p) (hs : Sorting F p) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ (K : Type) (_ : Field K) (_ : Algebra F K)
      (u : ℕ) (L : Set (Table K)) (a b : Wire) (k : Val a → Val b → K) (s : ℕ),
      Wide K u L a b k s →
      ∃ v : ℕ, Net K (copies a (2 ^ u)) (copies b (2 ^ u)) (power k (2 ^ u)) v ∧
        (v : ℝ) ≤ C * (2 : ℝ) ^ u * s * (1 + (u : ℝ)) ^ (p - 1) := by
  obtain ⟨C, hC, batch⟩ := lookup_net hp hs
  refine ⟨C + 1, by linarith, ?_⟩
  intro K fk ak u L a b k s h
  rw [mul_right_comm ((C + 1) * (2 : ℝ) ^ u)]
  apply h.substitute
  intro A B f hab
  let t := wd A + wd B
  obtain ⟨v, hv, hb⟩ := batch K fk ak (.pair A B) (fun z => f z.1 z.2)
  let d := 2 ^ (u - t)
  refine ⟨d * (v + 2 ^ t * wd B), ?_, vertex_cost hC hp hab (Nat.le_add_left _ _) hb⟩
  have hpow : 2 ^ t * d = 2 ^ u := by dsimp [d, t]; rw [← pow_add, Nat.add_sub_of_le hab]
  rw [← hpow]
  exact ((split_batch (k := f) hv).power d).rewire
    (.joinCopies A (2 ^ t) d) (.joinCopies B (2 ^ t) d) (power_join f (2 ^ t) d)

end OAI.LinearAlgebra.MatrixExponent.Lookup
