import OAI.Computability.BorderVNP.PackedDeckCandidateWord
import OAI.Computability.BorderVNP.PackedDeckCandidateMath
import Mathlib.Data.Fin.VecNotation

/-! # Shared moment computations for the initial finite list of candidates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckCandidate

open PackedDeckScore ParseBatchSort VPVNP.VerifierNetwork

variable {B G : Type*} [Fintype B] [Fintype G] {m w : ℕ}

/-- The prior array, one raw tile array per candidate, and the cleared binwise rational means. -/
abbrev Input (B G : Type*) (m w : ℕ) :=
  (Option (Fin m) × B × G × Fin w) ⊕ (B × Fin w)

/-- Read a count in the prior array or in one finite candidate's array. -/
def inputCounts (x : Input B G m w → Bool) (p : Option (Fin m)) (t : B) (g : G) : ℕ :=
  value fun j => x (.inl (p,t,g,j))

/-- Cleared numerator of the previously centered mean plus the current mean. -/
def meanNumerator (x : Input B G m w → Bool) (t : B) : ℕ := value fun j => x (.inr (t,j))

/-- The four scalar inputs to the per-bin score formula. -/
def moment (x : Input B G m w → Bool) (i : Fin m) (t : B) : Fin 4 → ℕ :=
  ![meanNumerator x t, ∑ g, inputCounts x none t g, ∑ g, inputCounts x (some i) t g,
    ∑ g, inputCounts x (some i) t g * inputCounts x (some i) t g]

/-- Explicit gates for the three wide aggregations in one bin. -/
def momentCost (G : Type*) [Fintype G] (w C e : ℕ) : ℕ :=
  2 + 2*queryCost (batchBits G Unit) 0 (sumBits G w) + Fintype.card G*(C*(w+1)^e) +
    queryCost (batchBits G Unit) 0 (sumBits G (2*w))

/-- One compiled frame returns all four moments, reduced to the installed working width. -/
theorem exists_moments :
    ∃ C e : ℕ, ∀ (B : Type*) (G : Type*) [Fintype B] [Fintype G] (m w : ℕ) (i : Fin m) (t : B),
      ∃ f : Frame (Input B G m w) (Fin 4 × Fin w), f.size ≤ momentCost G w C e ∧
        ∀ x l, value (fun j => f.eval x (l,j)) = moment x i t l % 2^w := by
  obtain ⟨C,e,hdot⟩ := dotFrames
  refine ⟨C,e,?_⟩
  intro B G instB instG m w i t
  obtain ⟨dot,hd,he⟩ := hdot G w
  have hw : w ≤ sumBits G w := by simp [sumBits]
  have hw₂ : w ≤ sumBits G (2*w) := by dsimp [sumBits]; omega
  let single (p : Option (Fin m)) : Frame (Input B G m w) (Fin w) :=
    (Word.trim hw (sumFrame G w)).subst
      (Frame.initial (fun gj => .inl (p,t,gj.1,gj.2)))
  let src (a : G × (Fin w ⊕ Fin w)) : Input B G m w := .inl (some i,t,a.1, a.2.elim id id)
  let square := (Word.trim hw₂ dot).subst (Frame.initial src)
  let direct : Frame (Input B G m w) (Fin w) := Frame.initial (fun j => .inr (t,j))
  let fs : Fin 4 → Frame (Input B G m w) (Fin w) := ![direct,single none,single (some i),square]
  obtain ⟨all,hs,hv⟩ := Crossing.exists_parallelFrames (out := fun _ : Fin 4 => Fin w) fs
  refine ⟨all.select (fun lj => ⟨lj.1,lj.2⟩), ?_, ?_⟩
  · simp only [Frame.select_size]
    apply hs.trans
    rw [Fin.sum_univ_four]
    change 1 + (direct.size + (single none).size + (single (some i)).size + square.size) ≤ _
    simp only [direct, single, square, Word.trim, Frame.subst_size, Frame.initial_size,
      Frame.select_size, zero_add, momentCost]
    have h := sumFrame_size G w
    omega
  · intro x l
    have sumval (p : Option (Fin m)) : value ((single p).eval x) = (∑ g, inputCounts x p t g) % 2^w := by
      let z := fun gj : G × Fin w => x (.inl (p,t,gj.1,gj.2))
      have hzin : (Frame.initial (fun gj : G × Fin w => Sum.inl (p,t,gj.1,gj.2))).eval x = z :=
        funext (Frame.initial_eval _ _)
      have hs' : (single p).eval x = (Word.trim hw (sumFrame G w)).eval z := by
        funext j
        simp only [single, Frame.subst_eval, hzin]
      rw [hs']
      exact (Word.trim_value hw (sumFrame G w) z).trans (congrArg (· % 2^w) (sumFrame_value G w z))
    have sqval : value (square.eval x) = (∑ g, inputCounts x (some i) t g * inputCounts x (some i) t g) % 2^w := by
      have hs' : square.eval x = (Word.trim hw₂ dot).eval
          ((Frame.initial src).eval x) := funext (Frame.subst_eval _ _ _)
      rw [hs', Word.trim_value, he]
      simp [Frame.initial_eval, src, inputCounts]
    simp only [Frame.select_eval, hv]
    fin_cases l
    · simpa [fs, direct, moment, meanNumerator] using (Nat.mod_eq_of_lt (value_lt (fun j => x (.inr (t,j))))).symm
    · exact sumval none
    · exact sumval (some i)
    · exact sqval

end PackedDeckCandidate

end BorderVNP
end Computability
end OAI
