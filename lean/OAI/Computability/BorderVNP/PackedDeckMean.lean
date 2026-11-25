import OAI.Computability.BorderVNP.PackedDeckCandidateMoments
import OAI.Computability.BorderVNP.PackedDeckScoreCost
import OAI.Computability.BorderVNP.PackedDeckMeanMath

/-!
# Computing the cleared bin means for finite motion candidates

The previous numerator is carried in the mean bank. Each update appends one
weighted dot product over candidates and physical tiles. The extra lane for
the previous numerator permits the same circuit to add it without reading
earlier packs again.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedDeckMean

open PackedDeckCandidate PackedDeckScore ParseBatchSort ParseBatchCounts VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin

variable {B G : Type*} [Fintype B] [Fintype G] {m w : ℕ}

/-- Previous bin numerator plus this pack's exact contribution. -/
def nextNumerator (pnum : Fin m → ℕ) (x : Input B G m w → Bool) (b : B) : ℕ :=
  meanNumerator x b + weighted pnum (fun c => inputCounts x (some c)) b

/-- Per-bin cost, with a single lane for each pair of candidate and tile,
and one additional lane for the previous numerator. -/
def meanCost (G : Type*) [Fintype G] (m w C e : ℕ) : ℕ :=
  let I := Option (Fin m × G)
  Fintype.card I * (2*w) +
    (1 + Fintype.card I * (C*(w+1)^e) + queryCost (batchBits I Unit) 0 (sumBits I (2*w)))

/-- Sorting contributes a logarithmic-width polynomial per physical lane.
The estimate also covers the empty candidate list. -/
theorem meanCost_le (G : Type*) [Fintype G] (m w C e : ℕ) :
    let n := m * Fintype.card G + 1
    let b := Nat.clog 2 (n+1)
    meanCost G m w C e ≤ n*(2*w) + (1+n*(C*(w+1)^e)+2400*(n+1)*(b+w+1)^3) := by
  let I := Option (Fin m × G)
  let n := m * Fintype.card G + 1
  let b := Nat.clog 2 (n+1)
  have hn : Fintype.card I = n := by simp [I,n]
  have hb : batchBits I Unit = b := by simp [batchBits,hn,b]
  have hw : sumBits I (2*w) = 2*w+b := by simp [sumBits,hn,b]
  have hp : 2^b ≤ 2*(n+1) := by
    have hs := PackedHistogram.layout_size I Unit (by simp)
    simpa [b, hn] using hs.le
  have h₁ : b + 0 + (2*w+b) + 1 ≤ 2*(b+w+1) := by omega
  have hquery := (queryCost_le b 0 (2*w+b)).trans
    (Nat.mul_le_mul hp (Nat.mul_le_mul_left 150 (Nat.pow_le_pow_left h₁ 3)))
  have he : queryCost b 0 (2*w+b) ≤ 2400*(n+1)*(b+w+1)^3 := by
    exact hquery.trans_eq (by ring)
  change Fintype.card I*(2*w) + (1+Fintype.card I*(C*(w+1)^e)+
    queryCost (batchBits I Unit) 0 (sumBits I (2*w))) ≤ _
  rw [hn,hb,hw]
  exact Nat.add_le_add_left (Nat.add_le_add_left he _) _

/-- Compute all updated bin numerators simultaneously. The word width is
shared with the finite-candidate score and sufficient final range implies
exact output for each bin. -/
theorem numeratorFrames :
    ∃ C e : ℕ, ∀ (B G : Type*) [Fintype B] [Fintype G] (m w : ℕ) (_ : 0 < w)
      (pnum : Fin m → ℕ) (_ : ∀ c, pnum c < 2^w),
      ∃ f : Frame (Input B G m w) (B × Fin w), f.size ≤ 1 + Fintype.card B * meanCost G m w C e ∧
        ∀ (x : Input B G m w → Bool) (b : B),
          value (fun j => f.eval x (b,j)) = nextNumerator pnum x b % 2^w := by
  obtain ⟨C,e,makeDot⟩ := dotFrames
  refine ⟨C,e,?_⟩
  intro B G instB instG m w hw pnum hp
  let I := Option (Fin m × G)
  let weight : I → Fin (2^w)
    | none => ⟨1,one_lt_pow₀ (by decide) (by omega)⟩
    | some p => ⟨pnum p.1,hp p.1⟩
  let raw (b : B) : I → Fin w → Input B G m w
    | none, j => .inr (b,j)
    | some p, j => .inl (some p.1,b,p.2,j)
  let pin (b : B) (z : I × (Fin w ⊕ Fin w)) : Expr (Input B G m w) :=
    z.2.elim (fun j => .const ((numberWords w).symm (weight z.1) j)) (fun j => .input (raw b z.1 j))
  let pins (b : B) := (Frame.initial id).step (pin b)
  obtain ⟨dot,hs,heval⟩ := makeDot I w
  have hwidth : w ≤ sumBits I (2*w) := by dsimp [sumBits]; omega
  let one (b : B) := Word.trim hwidth (dot.subst (pins b))
  have hpin (b : B) : (pins b).size ≤ Fintype.card I*(2*w) := by
    have h := Frame.step_size_le (Frame.initial id) (pin b) 1 (fun p => by rcases p with ⟨i,j|j⟩ <;> rfl)
    simpa [pins,two_mul] using h
  have hsize (b : B) : (one b).size ≤ meanCost G m w C e := by
    simpa only [one,Word.trim,Frame.select_size,Frame.subst_size,meanCost] using Nat.add_le_add (hpin b) hs
  have hval (x : Input B G m w → Bool) (b : B) :
      value ((one b).eval x) = nextNumerator pnum x b % 2^w := by
    rw [show value ((one b).eval x) = value ((dot.subst (pins b)).eval x) % 2^w from Word.trim_value ..]
    have hd : (dot.subst (pins b)).eval x = dot.eval ((pins b).eval x) :=
      funext (Frame.subst_eval dot (pins b) x)
    rw [hd,heval]
    have hleft (i : I) : (fun j => (pins b).eval x (i,Sum.inl j)) = (numberWords w).symm (weight i) := by
      funext j; simp [pins,pin,StatementCircuit.Expr.eval]
    have hright (i : I) : (fun j => (pins b).eval x (i,Sum.inr j)) = x ∘ raw b i := by
      funext j; simp [pins,pin,StatementCircuit.Expr.eval]
    simp_rw [hleft,value_encode,hright]
    congr 1
    rw [Fintype.sum_option,Fintype.sum_prod_type]
    simp only [weight,raw,one_mul,nextNumerator,weighted,Finset.mul_sum,inputCounts,meanNumerator,Function.comp_def]
  obtain ⟨all,ha,hal⟩ := Crossing.exists_parallelFrames (out := fun _ : B => Fin w) one
  let f := all.select fun p : B × Fin w => ⟨p.1,p.2⟩
  refine ⟨f,?_,?_⟩
  · have h := Finset.sum_le_sum (s := Finset.univ) (fun b _ => hsize b)
    simpa [f] using ha.trans (Nat.add_le_add_left h 1)
  · intro x b
    have hrow : (fun j => f.eval x (b,j)) = (one b).eval x := by funext j; simp [f,hal]
    rw [hrow,hval]

/-- Retain the physical count banks and replace the old numerator by the
updated one. The finite-candidate comparison accepts this output directly. -/
theorem updateFrames :
    ∃ C e : ℕ, ∀ (B G : Type*) [Fintype B] [Fintype G] (m w : ℕ) (_ : 0 < w)
      (pnum : Fin m → ℕ) (_ : ∀ c, pnum c < 2^w),
      ∃ f : Frame (Input B G m w) (Input B G m w), f.size ≤ 1 + Fintype.card B * meanCost G m w C e ∧
        (∀ x j, f.eval x (.inl j) = x (.inl j)) ∧
        ∀ x b, nextNumerator pnum x b < 2^w → meanNumerator (f.eval x) b = nextNumerator pnum x b := by
  obtain ⟨C,e,h⟩ := numeratorFrames
  refine ⟨C,e,?_⟩
  intro B G instB instG m w hw pnum hp
  obtain ⟨f,hs,hval⟩ := h B G m w hw pnum hp
  let out := f.withInput.select (Sum.elim (fun j => .inl (.inl j)) Sum.inr)
  refine ⟨out,by simpa [out] using hs,fun _ _ => by simp [out],?_⟩
  intro x b hb
  have he : (fun j => out.eval x (.inr (b,j))) = (fun j => f.eval x (b,j)) := by funext j; simp [out]
  rw [meanNumerator,he,hval,Nat.mod_eq_of_lt hb]

end PackedDeckMean

end BorderVNP
end Computability
end OAI
