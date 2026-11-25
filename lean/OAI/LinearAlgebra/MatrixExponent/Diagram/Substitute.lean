import OAI.LinearAlgebra.MatrixExponent.Diagram.Wide


/-!
# Substitution in powered networks

Each replacement handles the same number of copies. Summing over the
internal bits of a bundle then factors as independent sums in each copy.
-/

namespace OAI.LinearAlgebra.MatrixExponent
variable {F : Type} [Field F] {a b c : Wire}

theorem power_comp (k : Val a → Val b → F) (l : Val b → Val c → F) (d : ℕ)
    (x : Val (copies a d)) (z : Val (copies c d)) :
    power (fun s t => ∑ y : Val b, k s y * l y t) d x z =
      ∑ y : Val (copies b d), power k d x y * power l d y z := by
  induction d with
  | zero => simp [power]
  | succ d ih =>
    rw [power, ih, Finset.sum_mul_sum, Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro y _
    apply Finset.sum_congr rfl
    intro v _
    exact mul_mul_mul_comm _ _ _ _

theorem power_trace (k : Val (.pair a c) → Val (.pair b c) → F) (d : ℕ)
    (x : Val (copies a d)) (y : Val (copies b d)) :
    power (fun (s : Val a) (t : Val b) => ∑ z : Val c, k (s, z) (t, z)) d x y =
      ∑ z : Val (copies c d), power k d (zipCopies a c d (x, z)) (zipCopies b c d (y, z)) := by
  induction d with
  | zero => simp [power]
  | succ d ih =>
    rw [power, ih, Finset.sum_mul_sum, Fintype.sum_prod_type]
    rfl

private theorem power_pre (k : Val b → Val c → F) (f : Val a → Val b) (d : ℕ)
    (x : Val (copies a d)) (y : Val (copies c d)) :
    power (fun s t => k (f s) t) d x y = power k d (mapCopies f d x) y := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [power, mapCopies, ih]

private theorem power_post (k : Val a → Val b → F) (f : Val c → Val b) (d : ℕ)
    (x : Val (copies a d)) (y : Val (copies c d)) :
    power (fun s t => k s (f t)) d x y = power k d x (mapCopies f d y) := by
  induction d with
  | zero => rfl
  | succ d ih => simp only [power, mapCopies, ih]

theorem Wide.substitute {u d m : ℕ} {C : ℝ} {L : Set (Table F)} {k : Val a → Val b → F}
    (h : Wide F u L a b k m)
    (ht : ∀ A B : Wire, ∀ k : Val A → Val B → F, wd A + wd B ≤ u →
      ∃ v, Net F (copies A d) (copies B d) (power k d) v ∧
        (v : ℝ) ≤ C * (1 + (wd A + wd B : ℕ))) :
    ∃ v, Net F (copies a d) (copies b d) (power k d) v ∧ (v : ℝ) ≤ C * m := by
  induction h with
  | empty => exact ⟨_, Net.empty.power d, by simp⟩
  | table a b k ha _ => simpa only [Nat.cast_add, Nat.cast_one] using ht a b k ha
  | @par a b c e k l m n _ _ ih ig =>
    obtain ⟨v, hv, ev⟩ := ih
    obtain ⟨w, hw, ew⟩ := ig
    refine ⟨v + w, (hv.par hw).rewire (.zipCopies a c d) (.zipCopies b e d) (power_zip k l d), ?_⟩
    simpa only [Nat.cast_add, mul_add] using add_le_add ev ew
  | @comp a b c k l m n _ _ ih ig =>
    obtain ⟨v, hv, ev⟩ := ih
    obtain ⟨w, hw, ew⟩ := ig
    refine ⟨v + w, ?_, ?_⟩
    · simpa only [← power_comp] using hv.comp hw
    · simpa only [Nat.cast_add, mul_add] using add_le_add ev ew
  | @trace a b c k m _ ih =>
    obtain ⟨v, hv, ev⟩ := ih
    refine ⟨v, ?_, ev⟩
    simpa only [← power_trace] using ((hv.pre (.zipCopies a c d)).post (.zipCopies b c d)).trace
  | pre _ hf ih =>
    obtain ⟨v, hv, ev⟩ := ih
    exact ⟨v, by simpa only [← power_pre] using hv.pre (hf.mapCopies d), ev⟩
  | post _ hf ih =>
    obtain ⟨v, hv, ev⟩ := ih
    exact ⟨v, by simpa only [← power_post] using hv.post (hf.mapCopies d), ev⟩

end OAI.LinearAlgebra.MatrixExponent
