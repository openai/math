import Mathlib.Data.Finset.Sort
import Mathlib.Logic.Equiv.Set
import Mathlib.Tactic

namespace OAI
/-! # Unique aligned destinations for a sorted digit block

Within a run destinations advance by one. At a digit change they advance to
the first slot of the next pack. Dummy sources fill the complement in strictly
increasing order. All of these rules concern adjacent rows or a single word.
-/

namespace Hierarchy.Tagged.Align

open scoped Classical
noncomputable section

/-- The next destination after a real source row. -/
def advance (p x : ℕ) (changed : Bool) := if changed then (x/p+1)*p else x+1

private theorem advance_bounds {p x : ℕ} (hp : 0 < p) (ch : Bool) :
    x < advance p x ch ∧ advance p x ch ≤ x+p := by
  have div := Nat.div_add_mod x p
  rw [Nat.mul_comm] at div
  have rem := Nat.mod_lt x hp
  cases ch <;> simp [advance, Nat.add_mul] <;> omega

def dest {n d : ℕ} (p : ℕ) (key : Fin (n+1) → Fin d) : Fin (n+1) → ℕ :=
  Fin.induction 0 (fun i x => advance p x (decide (key i.castSucc ≠ key i.succ)))

theorem dest_zero {n d : ℕ} (p : ℕ) (key : Fin (n+1) → Fin d) : dest p key 0 = 0 := rfl

theorem dest_step {n d : ℕ} (p : ℕ) (key : Fin (n+1) → Fin d) (i : Fin n) :
    dest p key i.succ = advance p (dest p key i.castSucc) (decide (key i.castSucc ≠ key i.succ)) := by
  simp [dest]

theorem dest_strict {n d p : ℕ} (hp : 0 < p) (key : Fin (n+1) → Fin d) : StrictMono (dest p key) := by
  apply Fin.strictMono_iff_lt_succ.mpr
  intro i
  rw [dest_step]
  exact (advance_bounds hp _).1

theorem dest_bound {n d p : ℕ} (hp : 0 < p) (key : Fin (n+1) → Fin d) (sorted : Monotone key)
    (i : Fin (n+1)) : dest p key i ≤ i.val + (key i).val*p := by
  induction i using Fin.induction with
  | zero => simp [dest_zero]
  | succ i ih =>
    rw [dest_step, Fin.val_succ]
    by_cases same : key i.castSucc = key i.succ
    · simp [advance, same] at *
      omega
    · have a := (advance_bounds (x := dest p key i.castSucc) hp (decide (key i.castSucc ≠ key i.succ))).2
      have inc : (key i.castSucc).val+1 ≤ (key i.succ).val :=
        (sorted i.castSucc_le_succ).lt_of_ne same
      have scale := Nat.mul_le_mul_right p inc
      simp only [Fin.val_castSucc, Nat.add_mul, Nat.one_mul] at *
      omega

theorem dest_lt_slots {n d p : ℕ} (hp : 0 < p) (key : Fin (n+1) → Fin d) (sorted : Monotone key)
    (i : Fin (n+1)) : dest p key i < (n+1)+d*p := by
  exact lt_of_le_of_lt (dest_bound hp key sorted i)
    (Nat.add_lt_add_of_lt_of_le i.isLt (Nat.mul_le_mul_right p (key i).isLt.le))

/-- The local transition and the first address characterize all real destinations. -/
theorem dest_unique {n d : ℕ} (p : ℕ) (key : Fin (n+1) → Fin d) (guess : Fin (n+1) → ℕ)
    (first : guess 0 = 0) (step : ∀ i : Fin n,
    guess i.succ = advance p (guess i.castSucc) (decide (key i.castSucc ≠ key i.succ))) :
    guess = dest p key := by
  funext i
  induction i using Fin.induction with
  | zero => exact first
  | succ i ih => rw [step, ih, dest_step]

/-- A pack may contain several real records, all of one digit. -/
theorem homogeneous {n d p : ℕ} (hp : 0 < p) (key : Fin (n+1) → Fin d) (sorted : Monotone key)
    (i j : Fin (n+1)) (pack : dest p key i/p = dest p key j/p) : key i = key j := by
  have strict (j : Fin (n+1)) : ∀ i, i ≤ j → key i < key j → dest p key i/p < dest p key j/p := by
    induction j using Fin.induction with
    | zero =>
      intro i h lt
      have zero := Fin.le_zero_iff.mp h
      exact (lt.ne (congrArg key zero)).elim
    | succ j ih =>
      intro i le lt
      have ne : i ≠ j.succ := by rintro rfl; exact lt_irrefl _ lt
      have ij : i ≤ j.castSucc := by have := lt_of_le_of_ne le ne; exact Fin.le_castSucc_iff.mpr this
      by_cases changeKey : key j.castSucc = key j.succ
      · have before := ih i ij (lt.trans_le changeKey.ge)
        exact before.trans_le (Nat.div_le_div_right ((dest_strict hp key).monotone j.castSucc_le_succ))
      · have before := Nat.div_le_div_right (c := p) ((dest_strict hp key).monotone ij)
        rw [dest_step]
        simp [advance, changeKey, Nat.mul_div_cancel _ hp] at *
        omega
  rcases le_total i j with le | le
  · exact (sorted le).eq_of_not_lt fun lt => (strict j i le lt).ne pack
  · exact ((sorted le).eq_of_not_lt fun lt => (strict i j le lt).ne pack.symm).symm

/-- Every lane before a real record in the same pack is real and carries
its digit. Thus the first physical lane supplies each nonempty pack's sort key. -/
theorem pack_prefix {n d p : ℕ} (hp : 0 < p) (key : Fin (n+1) → Fin d) (i : Fin (n+1)) :
    ∀ b, dest p key i/p*p ≤ b → b ≤ dest p key i → ∃ l, dest p key l = b ∧ key l = key i := by
  induction i using Fin.induction with
  | zero =>
    intro b _ hb
    exact ⟨0,(Nat.eq_zero_of_le_zero hb).symm,rfl⟩
  | succ i ih =>
    intro b lower upper
    by_cases same : key i.castSucc = key i.succ
    · have step : dest p key i.succ = dest p key i.castSucc+1 := by simp [dest_step, advance,same]
      by_cases last : b = dest p key i.succ
      · exact ⟨i.succ,last.symm,rfl⟩
      · have before : b ≤ dest p key i.castSucc := by omega
        by_cases wrap : p ∣ dest p key i.castSucc+1
        · rw [step, Nat.div_mul_cancel wrap] at lower
          omega
        · rw [step, Nat.succ_div_of_not_dvd wrap] at lower
          obtain ⟨l, placed, k⟩ := ih b lower before
          exact ⟨l,placed,k.trans same⟩
    · have aligned : dest p key i.succ/p*p = dest p key i.succ := by
        rw [dest_step]
        simp [advance,same,Nat.mul_div_cancel _ hp]
      rw [aligned] at lower
      exact ⟨i.succ,Nat.le_antisymm lower upper,rfl⟩

/-- The real slots and the remaining dummy slots form a single tagged permutation. -/
def complete {r m : ℕ} (e : Fin r ↪ Fin m) : Fin r ⊕ Fin (m-r) ≃ Fin m := by
  let used := Finset.univ.map e
  have usedCard : used.card = r := by simp [used]
  let re : Fin r ≃ used := Equiv.ofBijective (fun i => ⟨e i, by simp [used]⟩) (by
    constructor
    · intro i j h; exact e.injective (congrArg Subtype.val h)
    · rintro ⟨v, membership⟩
      obtain ⟨i, _, hi⟩ := Finset.mem_map.mp membership
      exact ⟨i, Subtype.ext hi⟩)
  have freeCard : usedᶜ.card = m-r := by simp [Finset.card_compl, usedCard]
  let free := (usedᶜ.orderIsoOfFin freeCard).toEquiv
  let identify : (↑usedᶜ : Type) ≃ {v : Fin m // v ∉ used} :=
    Equiv.subtypeEquivRight fun _ => Finset.mem_compl
  exact (Equiv.sumCongr re (free.trans identify)).trans (Equiv.sumCompl (· ∈ used))

@[simp] theorem complete_real {r m : ℕ} (e : Fin r ↪ Fin m) (i : Fin r) :
    complete e (.inl i) = e i := rfl

theorem complete_dummy {r m : ℕ} (e : Fin r ↪ Fin m) : StrictMono (fun i => complete e (.inr i)) := by
  have freeCard : (Finset.univ.map e)ᶜ.card = m-r := by simp [Finset.card_compl]
  exact fun _ _ h => (Finset.orderIsoOfFin ((Finset.univ.map e)ᶜ) freeCard).strictMono h

private theorem residual_range {r m : ℕ} (e : Fin r ↪ Fin m)
    (f : Fin r ⊕ Fin (m-r) ≃ Fin m) (real : ∀ i, f (.inl i) = e i) :
    Set.range (fun j => f (.inr j)) = (Set.range e)ᶜ := by
  ext v
  constructor
  · rintro ⟨j,rfl⟩ ⟨i,same⟩
    have clash := f.injective ((real i).trans same)
    contradiction
  · intro outside
    obtain ⟨i | j, pre⟩ := f.surjective v
    · exact (outside ⟨i,(real i).symm.trans pre⟩).elim
    · exact ⟨j, pre⟩

/-- The whole alignment permutation is forced by the real destinations and
order of the dummy tags. -/
theorem complete_unique {r m : ℕ} (e : Fin r ↪ Fin m) (f : Fin r ⊕ Fin (m-r) ≃ Fin m)
    (real : ∀ i, f (.inl i) = e i) (ordered : StrictMono (fun j => f (.inr j))) : f = complete e := by
  have same := (ordered.range_inj_of_wellFoundedLT (complete_dummy e)).mp
    ((residual_range e f real).trans (residual_range e _ (complete_real e)).symm)
  apply Equiv.ext
  rintro (i | j)
  · exact (real i).trans (complete_real e i).symm
  · exact congrFun same j


end
end Hierarchy.Tagged.Align

end OAI
