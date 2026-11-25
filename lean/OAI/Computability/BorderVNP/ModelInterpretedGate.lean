import OAI.Computability.VPVNP.CircuitComposition

/-! # Retaining shared operands in arbitrary target rings -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Interpreted

open VPVNP

variable {R σ A : Type*} [Ring A] {n m : ℕ} (s : R → A) (x : σ → A)

/-- A value in the target ring is available as an input, scalar, or gate output. -/
def HasWire (p : Program R σ n) (f : A) : Prop :=
  ∃ r : Ref R σ n, r.read s x (p.run s x) = f

/-- Every operand of the first program can be reused in the second. -/
def Preserves (p : Program R σ n) (q : Program R σ m) : Prop :=
  ∀ f, HasWire s x p f → HasWire s x q f

/-- Scalars are free circuit inputs. -/
theorem hasWire_const (p : Program R σ n) (a : R) : HasWire s x p (s a) :=
  ⟨.const a, rfl⟩

/-- Variables are free circuit inputs. -/
theorem hasWire_var (p : Program R σ n) (a : σ) : HasWire s x p (x a) :=
  ⟨.var a, rfl⟩

/-- Appending a binary operation retains all old operands and produces its result. -/
theorem append_binary (p : Program R σ n) (op : BinOp) {a b : A}
    (ha : HasWire s x p a) (hb : HasWire s x p b) :
    ∃ q : Program R σ (n+1), Preserves s x p q ∧ HasWire s x q (op.apply a b) := by
  obtain ⟨u, rfl⟩ := ha
  obtain ⟨v, rfl⟩ := hb
  refine ⟨p.snoc op u v, ?_, .gate (Fin.last _), ?_⟩
  · rintro _ ⟨r, rfl⟩
    refine ⟨r.reindex Fin.castSucc, ?_⟩
    cases r <;> simp [Ref.reindex, Ref.read, Program.run]
  · simp [Ref.read, Program.run]

/-- Produce a finite sequence of operands at bounded cost per operand. Every operand is
available for all subsequent steps. -/
theorem extend_fin (p : Program R σ n) (k t : ℕ) (f : ℕ → A)
    (step : ∀ {m} (q : Program R σ m), Preserves s x p q → ∀ i < k,
      ∃ l ≤ m+t, ∃ r : Program R σ l, Preserves s x q r ∧ HasWire s x r (f i)) :
    ∃ l ≤ n+k*t, ∃ r : Program R σ l, Preserves s x p r ∧ ∀ i < k, HasWire s x r (f i) := by
  induction k with
  | zero => exact ⟨n, by simp, p, fun _ h => h, by simp⟩
  | succ k ih =>
    obtain ⟨l, hl, q, hpq, hq⟩ := ih (fun r h i hi => step r h i (by omega))
    obtain ⟨l', hl', r, hqr, hr⟩ := step q hpq k (by omega)
    refine ⟨l', ?_, r, fun g h => hqr g (hpq g h), ?_⟩
    · rw [Nat.succ_mul]
      omega
    · intro i hi
      rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | rfl
      · exact hqr _ (hq i h)
      · exact hr

/-- Accumulating a sum of products costs two gates per term and retains the input wires. -/
theorem append_sum_products {ι : Type*} (p : Program R σ n) (T : Finset ι)
    (hz : HasWire s x p 0) (a b : ι → A) (ha : ∀ i ∈ T, HasWire s x p (a i))
    (hb : ∀ i ∈ T, HasWire s x p (b i)) :
    ∃ l ≤ n + 2 * T.card, ∃ q : Program R σ l, Preserves s x p q ∧
      HasWire s x q (∑ i ∈ T, a i * b i) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    exact ⟨n, by simp, p, fun _ h => h, by simpa using hz⟩
  | @insert i T hi ih =>
    obtain ⟨l, hl, q, hpq, hsum⟩ := ih
      (fun j hj => ha j (Finset.mem_insert_of_mem hj))
      (fun j hj => hb j (Finset.mem_insert_of_mem hj))
    obtain ⟨r, hqr, hmul⟩ := append_binary s x q .mul
      (hpq _ (ha i (Finset.mem_insert_self ..))) (hpq _ (hb i (Finset.mem_insert_self ..)))
    obtain ⟨r', hrr', hplus⟩ := append_binary s x r .add hmul (hqr _ hsum)
    refine ⟨l + 1 + 1, ?_, r', fun f hf => hrr' f (hqr f (hpq f hf)), ?_⟩
    · rw [Finset.card_insert_of_notMem hi]
      omega
    · rw [Finset.sum_insert hi]
      exact hplus

end Interpreted

end BorderVNP
end Computability
end OAI
