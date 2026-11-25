import OAI.Computability.BorderVNP.PackedDeckCandidateMoments
import OAI.Computability.BorderVNP.PackedDeckCandidateCompare

/-! # Computing the entire score of each finite candidate before any digit is chosen -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckCandidate

open PackedDeckScore ParseBatchSort VPVNP.VerifierNetwork

variable {B G : Type*} [Fintype B] [Fintype G] {m w : ℕ}

/-- Scalar formula applied to the four computed moments in one bin. -/
def scalar (D n : ℕ) : Bool → Word.Formula (Fin 4)
  | false => .add (.mul (.num (D*n)) (.var 3)) (.mul (.mul (.num (2*D)) (.var 1)) (.var 2))
  | true => .mul (.mul (.num (2*n)) (.var 0)) (.var 2)

/-- Per-bin positive or negative score before reducing to the working width. -/
def charge (D : ℕ) (x : Input B G m w → Bool) (i : Fin m) (neg : Bool) (t : B) : ℕ :=
  (scalar D (Fintype.card G) neg).eval (moment x i t)

private theorem scalar_nodes (D n : ℕ) (neg : Bool) : (scalar D n neg).nodes ≤ 9 := by
  cases neg <;> simp [scalar, Word.Formula.nodes]

/-- Gates per bin and channel, including all moment computations. -/
def scalarCost (G : Type*) [Fintype G] (w C e M z : ℕ) :=
  momentCost G w C e + 9*(M*(w+1)^z+w*(16*w+22)+1)

/-- All scalar charge circuits use the same constants, independent of the group and candidate list. -/
theorem scalarFrames :
    ∃ C e M z : ℕ, ∀ (B : Type*) (G : Type*) [Fintype B] [Fintype G] (m w D : ℕ)
      (i : Fin m) (neg : Bool) (t : B),
      ∃ f : Frame (Input B G m w) (Fin w), f.size ≤ scalarCost G w C e M z ∧
        ∀ x, value (f.eval x) = charge D x i neg t % 2^w := by
  obtain ⟨C,e,hfields⟩ := exists_moments
  obtain ⟨M,z,hmul⟩ := StackFrame.multiplicationFrames
  refine ⟨C,e,M,z,?_⟩
  intro B G instB instG m w D i neg t
  obtain ⟨fields,hf,he⟩ := hfields B G m w i t
  obtain ⟨mul,hs,hm⟩ := hmul w
  let p := scalar D (Fintype.card G) neg
  refine ⟨(p.compile mul).subst fields, ?_, ?_⟩
  · rw [Frame.subst_size]
    apply Nat.add_le_add hf
    apply (p.compile_size mul).trans
    apply Nat.mul_le_mul (scalar_nodes ..)
    omega
  · intro x
    have hw : ((p.compile mul).subst fields).eval x = (p.compile mul).eval (fields.eval x) :=
      funext fun j => Frame.subst_eval _ _ _ _
    rw [hw, p.compile_value _ hm]
    have hfield : (fun l => value (fun j => fields.eval x (l,j))) = fun l => moment x i t l % 2^w :=
      funext (he x)
    rw [hfield, p.eval_mod]
    rfl

/-- Cost of aggregating one signed score channel over all relative bins. -/
def channelCost (B G : Type*) [Fintype B] [Fintype G] (w C e M z : ℕ) :=
  1 + Fintype.card B*scalarCost G w C e M z + queryCost (batchBits B Unit) 0 (sumBits B w)

/-- The accumulated wide channels give the two exact integer numerators. -/
theorem scoreFrames :
    ∃ C e M z : ℕ, ∀ (B : Type*) (G : Type*) [Fintype B] [Fintype G] (m w D : ℕ),
      ∃ f : Frame (Input B G m w) (ScorePin m (sumBits B w)),
        f.size ≤ 1 + m*2*channelCost B G w C e M z ∧
        ∀ x, (∀ i neg t, charge D x i neg t < 2^w) →
          ∀ i neg, channel (f.eval x) i neg =
            if neg then negative (meanNumerator x) (inputCounts x (some i))
            else positive D (inputCounts x none) (inputCounts x (some i)) := by
  obtain ⟨C,e,M,z,h⟩ := scalarFrames
  refine ⟨C,e,M,z,?_⟩
  intro B G instB instG m w D
  choose sf hsize he using h B G m w D
  have per (ij : Fin m × Bool) := Crossing.exists_parallelFrames (out := fun _ : B => Fin w) (sf ij.1 ij.2)
  choose terms ht hb using per
  let out (ij : Fin m × Bool) :=
    (sumFrame B w).subst ((terms ij).select (fun tj : B × Fin w => ⟨tj.1,tj.2⟩))
  obtain ⟨all,ha,hval⟩ := Crossing.exists_parallelFrames (out := fun _ : Fin m × Bool => Fin (sumBits B w)) out
  let names (p : ScorePin m (sumBits B w)) : Σ _ : Fin m × Bool, Fin (sumBits B w) := ⟨(p.1,p.2.1),p.2.2⟩
  refine ⟨all.select names, ?_, ?_⟩
  · have hc (ij : Fin m × Bool) : (out ij).size ≤ channelCost B G w C e M z := by
      have hh := Finset.sum_le_sum (s := Finset.univ) (fun t _ => hsize ij.1 ij.2 t)
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id] at hh
      simp only [out, Frame.subst_size, Frame.select_size, channelCost]
      exact Nat.add_le_add ((ht ij).trans (Nat.add_le_add_left hh 1)) (sumFrame_size ..)
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun ij _ => hc ij)
    simpa only [Frame.select_size, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_id] using ha.trans (Nat.add_le_add_left hh 1)
  · intro x fits i neg
    let y := ((terms (i,neg)).select (fun tj : B × Fin w => ⟨tj.1,tj.2⟩)).eval x
    have hs : channel ((all.select names).eval x) i neg = value ((sumFrame B w).eval y) := by
      apply congrArg value
      funext j
      simp only [Frame.select_eval, names, hval, out, Frame.subst_eval, y]
    have hy (t : B) : value (fun j => y (t,j)) = charge D x i neg t := by
      have hh := he i neg t x
      rw [Nat.mod_eq_of_lt (fits i neg t)] at hh
      simpa only [y, Frame.select_eval, hb] using hh
    rw [hs, sumFrame_value]
    simp only [hy]
    cases neg <;> rfl

/-- A full deterministic finite-candidate comparison chooses the first minimum of the exact
unconditioned rational increment, including the candidate-dependent squared norm. -/
theorem exists_choice :
    ∃ C e M z : ℕ, ∀ (B : Type*) (G : Type*) [Fintype B] [Fintype G] [Group G]
      (m w D : ℕ) (_ : 0 < D),
      ∃ f : Frame (Input B G m w) (Fin m),
        f.size ≤ 1 + m*2*channelCost B G w C e M z +
          m*m*(sumBits B w+1)*(16*(sumBits B w+1)+22) + m*((15*(sumBits B w+1)+3)*m+1) ∧
        ∀ x (base mean : B → ℚ), (∀ t, (D:ℚ)*(base t+mean t) = meanNumerator x t) →
          (∀ i neg t, charge D x i neg t < 2^w) →
          ∀ i, f.eval x i = true ↔ (List.finRange m).argmin
            (fun l => uniformScore (inputCounts x none) (inputCounts x (some l)) base mean) = some i := by
  obtain ⟨C,e,M,z,h⟩ := scoreFrames
  refine ⟨C,e,M,z,?_⟩
  intro B G instB instG groupG m w D hd
  obtain ⟨f,hf,he⟩ := h B G m w D
  refine ⟨(compare m (sumBits B w)).subst f, ?_, ?_⟩
  · rw [Frame.subst_size]
    simpa only [Nat.add_assoc] using Nat.add_le_add hf (compare_size m (sumBits B w))
  · intro x base mean ht fits i
    rw [Frame.subst_eval]
    apply compare_eval
    intro j l
    simp only [he x fits, ite_false, ite_true, Bool.false_eq_true]
    exact (score_le_iff D hd (meanNumerator x) (inputCounts x none) (inputCounts x (some j))
      (inputCounts x (some l)) base mean ht).symm

end PackedDeckCandidate

end BorderVNP
end Computability
end OAI
