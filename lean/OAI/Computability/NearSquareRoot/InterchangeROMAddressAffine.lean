import OAI.Computability.NearSquareRoot.InterchangeSpectralMask
import OAI.Computability.IntegerMultiplication.Carry.Small

/-! # Generating compact binary addresses for the affine router

A field occurs twice in the enclosing array. Its quadratic unary rank
enumeration is therefore paid for once by the array volume. The program
compresses the ranks before copying them to the spectator positions.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace AffineAddress

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry
  IntegerMultiplication.Bits IntegerMultiplication.Strip IntegerMultiplication.Adic
  IntegerMultiplication.Loom IntegerMultiplication.Strip.Dims

theorem rank_number {b f : ℕ} [NeZero b] (x : Block b f) :
    ((line b f).index x).val = number x := by
  let s := line b f
  let F (i : Fin s.count) : Fin s.count :=
    ⟨number (s.index.symm i), by simpa only [s,lineSize] using number_lt (s.index.symm i)⟩
  have inc : StrictMono F := by
    intro i j hij
    exact (SpectralMask.rank_lt _ _).mp (by simpa only [s,Equiv.apply_symm_apply] using hij)
  have e := congrArg Fin.val (congrFun inc.eq_id (s.index x))
  simpa only [F,Equiv.symm_apply_apply,id_eq] using e.symm

variable {I : Type} {w : I → ℝ} {src : I → Tree}

/-- A single rank bank in physical series order, with the same command for
every field and alphabet. -/
theorem binaryRanks {A : I → Type} (s : (i : I) → Series (A i))
    (count : Carries w src (fun i => send (tally (s i).count)))
    (budget : ∀ i, ((((s i).count+1)^2 : ℕ) : ℝ) ≤ w i) :
    Carries w src (fun i => stripe (s i) (fun a => send (born ((s i).index a).val))) := by
  have q := count.sequence (show Sized w _ (fun i => send (Iter.lineup (tally (s i).count))) from
    ⟨count.budget, _, SpectralRuns.enumerate_ranks.on (fun i => tally (s i).count), 2, fun i => by
      simp only [tally_length]
      change _ ≤ 2*w i
      linarith [budget i,count.budget i]⟩)
  let bit (t : Tally) := born t.length
  have z := q.chain (Carries.func q.budget q.out (List.map bit) (easy_chart.mapping))
  convert z using 1
  funext i
  rw [stripe_eq', Iter.lined]
  congr 1
  apply List.ext_getElem (by simp)
  intro n hn hn'
  let t : Fin (s i).count := ⟨n,by simpa only [Series.card] using hn⟩
  rw [(s i).get _ t]
  simp [t,bit]

/-- Replicate a complete stripe across a leading Cartesian factor. Its
per-cell bound may vary with the field width. -/
theorem prepend {P H : I → Type} (p : (i : I) → Series (P i)) (h : (i : I) → Series (H i))
    (v : (i : I) → H i → Tree) (k : I → ℕ) (bound : ∀ i x, (v i x).count ≤ k i)
    (posP : ∀ i, 1 ≤ (p i).count) (posH : ∀ i, 1 ≤ (h i).count)
    (ct : Carries w src (fun i => send (tally (p i).count)))
    (row : Carries w src (fun i => stripe (h i) (v i)))
    (budget : ∀ i, (((p i).count * ((h i).count * (k i + 2)) : ℕ) : ℝ) ≤ w i) :
    Carries w src (fun i => stripe ((p i).cart (h i)) (fun x => v i x.2)) := by
  apply IntegerMultiplication.Strip.flatten p h
  apply spread p _ (ct.twice row)
  refine ⟨2, fun i => ?_⟩
  have sz : (stripe (h i) (v i)).count ≤ (h i).count * (k i+2) := by
    have a := stripe_size (h i) (v i) (k i) (bound i)
    have := posH i
    rw [Nat.mul_add] at a ⊢
    omega
  have sz' : ((p i).count + 1) * (stripe (h i) (v i)).count ≤
      2 * ((p i).count * ((h i).count * (k i+2))) := by
    rw [← Nat.mul_assoc 2]
    exact Nat.mul_le_mul (by have := posP i; omega) sz
  calc
    _ ≤ 2 * (((p i).count * ((h i).count * (k i+2)) : ℕ) : ℝ) := by exact_mod_cast sz'
    _ ≤ _ := by exact mul_le_mul_of_nonneg_left (budget i) (by norm_num)

/-- Replicate the value of each cell across the trailing factor, then flatten
the list in the requested order. -/
theorem appendCopies {H B : I → Type} (h : (i : I) → Series (H i)) (b : (i : I) → Series (B i))
    (v : (i : I) → H i → Tree) (k : I → ℕ) (bound : ∀ i x, (v i x).count ≤ k i)
    (posH : ∀ i, 1 ≤ (h i).count) (posB : ∀ i, 1 ≤ (b i).count)
    (ctH : Carries w src (fun i => send (tally (h i).count)))
    (ctB : Carries w src (fun i => send (tally (b i).count)))
    (row : Carries w src (fun i => stripe (h i) (v i)))
    (budget : ∀ i, (((h i).count * ((b i).count * (k i+2)) : ℕ) : ℝ) ≤ w i) :
    Carries w src (fun i => stripe ((h i).cart (b i)) (fun x => v i x.1)) := by
  let weight (i : I) := (b i).count * (k i + 2)
  have bright i : 1 ≤ weight i := by
    exact Nat.mul_pos (posB i) (by omega)
  have rulerSize i : (send (tally (b i).count)).count ≤ 3*(b i).count := by
    change size (tally _) ≤ _
    rw [size_tally,tally_length]
    have := posB i
    omega
  have bweight i : (b i).count ≤ weight i := Nat.le_mul_of_pos_right _ (by omega)
  have kweight i : k i ≤ weight i := (show k i ≤ k i+2 by omega).trans (Nat.le_mul_of_pos_left _ (posB i))
  have rulers : Carries w src (stackRun h (fun i _ => send (tally (b i).count))) := by
    apply spread h _ (ctH.twice ctB)
    refine ⟨6, fun i => ?_⟩
    have s : ((h i).count+1)*(send (tally (b i).count)).count ≤ 6*((h i).count*weight i) := by
      calc
        _ ≤ (2*(h i).count)*(3*weight i) :=
          Nat.mul_le_mul (by have := posH i; omega) ((rulerSize _).trans (Nat.mul_le_mul_left _ (bweight _)))
        _ = _ := by ring
    calc
      _ ≤ 6*((((h i).count*weight i) : ℕ) : ℝ) := by exact_mod_cast s
      _ ≤ _ := by have := budget i; change _ ≤ 6*w i; dsimp only [weight]; linarith
  let inlet (a : Sigma H) := Tree.fork (send (tally (b a.1).count)) (v a.1 a.2)
  have vb : Volume (fun a : Sigma H => (weight a.1 : ℝ)) inlet := by
    refine ⟨5,fun a => ?_⟩
    have : (inlet a).count ≤ 5*weight a.1 := by
      dsimp only [inlet,Tree.count]
      have z := (rulerSize a.1).trans (Nat.mul_le_mul_left 3 (bweight a.1))
      have u := (bound _ a.2).trans (kweight a.1)
      have := bright a.1
      omega
    change ((inlet a).count : ℝ) ≤ 5*(weight a.1 : ℝ)
    exact_mod_cast this
  have one a : (1 : ℝ) ≤ weight a := by exact_mod_cast bright a
  have each : Carries (fun a : Sigma H => (weight a.1 : ℝ)) inlet
      (fun a => stripe (b a.1) (fun _ => v a.1 a.2)) := by
    apply spread (fun a : Sigma H => b a.1) (fun a => v a.1 a.2)
      (Carries.idles (fun a => one a.1) vb)
    refine ⟨2,fun a => ?_⟩
    have z : ((b a.1).count+1)*(v a.1 a.2).count ≤ 2*weight a.1 := by
      unfold weight
      rw [← Nat.mul_assoc]
      exact Nat.mul_le_mul (by have := posB a.1; omega) ((bound _ _).trans (by omega))
    exact_mod_cast z
  have pairs := coalesce h _ _ rulers row
  apply IntegerMultiplication.Strip.flatten h b
  apply pairs.chain
  exact (liftoff h (fun i a => inlet ⟨i,a⟩) _ (fun i => (weight i : ℝ)) each).times ctH.budget 2
    (fun i => by have hh := budget i; have := ctH.budget i
                 change ((h i).count : ℝ) * (weight i : ℝ) + 1 ≤ 2*w i
                 rw [← Nat.cast_mul]
                 change (((h i).count * weight i : ℕ) : ℝ) ≤ _ at hh
                 linarith)

end AffineAddress

end NearSquareRoot
end Computability
end OAI
