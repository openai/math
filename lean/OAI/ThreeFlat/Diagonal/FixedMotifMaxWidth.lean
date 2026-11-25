import OAI.ThreeFlat.Diagonal.MotifIntegerChoice
import OAI.ThreeFlat.Diagonal.MotifHistogram
import OAI.ThreeFlat.Diagonal.FixedMotifTile

namespace OAI
/-! # Uniform coordinate width for a fixed finite motif table -/

namespace ThreeFlat.Diagonal.FixedMotifMaxWidth

open LinearAlgebra.SpectralBooks MotifIntegerChoice MotifOuterTerms
open scoped BigOperators Classical

theorem score_le_sentinel {T E : Type*} [Fintype E] [DecidableEq E]
    (b : E → ℕ) (d : T → E → ℕ) (i : T) : score b d i ≤ 1+∑ e, b e := by
  change score b d i ≤ sentinel b
  apply Finset.sup_le
  intro e _
  by_cases zero : d i e = 0
  · simp only [need,zero,ite_true]
    split <;> omega
  · have eb : b e ≤ ∑ a, b a :=
      Finset.single_le_sum (f:=b) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)
    have lt : b e < sentinel b := by unfold sentinel; omega
    exact ((need_le_iff lt).mpr (Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero zero))).trans lt.le

theorem histWidth_le {H S : Type*} [Fintype H] {r : ℕ} (v : H → S → ℕ)
    (z : Histogram H r) (e : S) (M : ℕ) (bound : ∀ h, v h e ≤ M) :
    histWidth v z e ≤ r*M := by
  calc
    histWidth v z e ≤ ∑ h, (z.1 h).val*M :=
      Finset.sum_le_sum fun h _ => Nat.mul_le_mul_left _ (bound h)
    _ = r*M := by rw [← Finset.sum_mul,z.property]

/-- The constant depends only on the table and the input coefficient. The
bound holds for any selected row, including a row whose demand has a zero. -/
theorem bound {T E S : Type*} [Fintype T] [Fintype E] [DecidableEq E] [Fintype S]
    (H : T → Type*) [∀ i, Fintype (H i)] (base : T → E → ℕ) (v : ∀ i, H i → S → ℕ)
    (bits : T → ℕ) (K : ℕ) : ∃ C : ℕ, ∀ (U : ℕ) (b : E → ℕ), (∀ e, b e ≤ K*U) →
    ∀ (i : T) (z : Histogram (H i) (score b base i)) (e : S),
      histWidth (v i) z e+score b base i*bits i ≤ C*(1+U) := by
  let M : T → ℕ := fun i => ∑ h : H i, ∑ e : S, v i h e
  let A := ∑ i : T, (M i + bits i)
  refine ⟨(1+Fintype.card E*K)*A,?_⟩
  intro U b hb i z e
  have total : (∑ a, b a) ≤ Fintype.card E*K*U := by
    calc
      (∑ a, b a) ≤ ∑ _a : E, K*U := Finset.sum_le_sum (fun a _ => hb a)
      _ = _ := by simp [Nat.mul_assoc]
  have rle : score b base i ≤ (1+Fintype.card E*K)*(1+U) := by
    have h := score_le_sentinel b base i
    rw [Nat.mul_add,Nat.mul_one,Nat.add_mul,Nat.one_mul]
    omega
  have each (h : H i) : v i h e ≤ M i :=
    (Finset.single_le_sum (f:=v i h) (fun _ _ => Nat.zero_le _) (Finset.mem_univ e)).trans
      (Finset.single_le_sum (f:=fun a : H i => ∑ s : S, v i a s)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ h))
  have row : M i+bits i ≤ A :=
    Finset.single_le_sum (f:=fun j => M j+bits j) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  calc
    histWidth (v i) z e+score b base i*bits i ≤ score b base i*(M i+bits i) := by
      rw [Nat.mul_add]
      exact Nat.add_le_add_right (histWidth_le _ z e _ each) _
    _ ≤ ((1+Fintype.card E*K)*(1+U))*A := Nat.mul_le_mul rle row
    _ = _ := by ac_rfl

theorem tile_bound {T J E S : Type} [Fintype T] [Fintype J] [Fintype E] [DecidableEq E] [Fintype S]
    {D : PortGraph J E} {P : PortGraph J S} {F : Type*} [CommSemiring F]
    (base : T → E → ℕ) (block : ∀ i, FixedMotifTile D P (base i) F) (K : ℕ) :
    ∃ C : ℕ, ∀ (U : ℕ) (b : E → ℕ), (∀ e, b e ≤ K*U) →
    ∀ (i : T) (z : Histogram (block i).Alphabet (score b base i)) (e : S),
      histWidth (block i).output z e + score b base i*(block i).bits ≤ C*(1+U) :=
  bound (fun i => (block i).Alphabet) base (fun i => (block i).output) (fun i => (block i).bits) K


end ThreeFlat.Diagonal.FixedMotifMaxWidth

end OAI
