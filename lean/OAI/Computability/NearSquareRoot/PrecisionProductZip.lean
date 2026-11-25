import OAI.Computability.IntegerMultiplication.Code.Dup
import Mathlib.Data.List.OfFn
import Mathlib.Tactic

/-! # Preparing a pair of operand streams for the fixed-point product

A length scan supplies a unary repeat count. The machine copies the single
fractional-width ruler once per address and two linear zip passes align the
resulting records in the original address order.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ProductPass

open IntegerMultiplication.Code

variable {I A B : Type} [Codec A] [Codec B]

omit [Codec A] [Codec B] in
private theorem zip_ofFn {n : ℕ} (a : Fin n → A) (b : Fin n → B) :
    (List.ofFn a).zip (List.ofFn b) = List.ofFn (fun i => (a i, b i)) := by
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    simp [List.getElem_zip]

private theorem zipAt (N : I → ℕ) (a : (i : I) → Fin (N i) → A)
    (b : (i : I) → Fin (N i) → B) :
    Task (fun i => size (List.ofFn (a i), List.ofFn (b i)))
      (fun i => send (List.ofFn (a i), List.ofFn (b i)))
      (fun i => send (List.ofFn fun j => (a i j, b i j))) := by
  let arg i : {s : List A × List B // s.1.length = s.2.length} :=
    ⟨(List.ofFn (a i), List.ofFn (b i)), by simp⟩
  simpa only [arg, zip_ofFn] using (zip_spec.on arg)

/-- Size of an address-ordered stream whose records are uniformly bounded. -/
theorem streamSize {A : Type} [Codec A] {n w : ℕ} (a : Fin n → A)
    (hw : ∀ j, size (a j) ≤ w) : size (List.ofFn a) ≤ (n + 1) * (w + 1) := by
  rw [← costSum_le_length_size]
  have h := costSum_le (t := size) (u := fun _ => w) (s := List.ofFn a) (by
    intro x hx; obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx; exact hw i)
  have heq : costSum (fun _ : A => w) (List.ofFn a) = n*w := by
    simp only [costSum, List.map_ofFn, Function.comp_def, List.ofFn_const, List.sum_replicate, nsmul_eq_mul, Nat.cast_id]
  rw [heq] at h
  simp only [List.length_ofFn]
  nlinarith

/-- Pair two operand arrays with the fractional-width header supplied once
in unary. This prepares exactly the tuple order consumed by the grid command. -/
theorem prepare (N w : I → ℕ) (f : I → Tally)
    (a : (i : I) → Fin (N i) → A) (b : (i : I) → Fin (N i) → B)
    (ha : ∀ i j, size (a i j) ≤ w i) (hb : ∀ i j, size (b i j) ≤ w i)
    (hf : ∀ i, size (f i) ≤ w i) :
    Task (fun i => (N i + 1) * (w i + 1))
      (fun i => send (List.ofFn (a i), f i, List.ofFn (b i)))
      (fun i => send (List.ofFn fun j => (a i j, f i, b i j))) := by
  let xs i := List.ofFn (a i)
  let ys i := List.ofFn (b i)
  let fs i := List.ofFn (fun _ : Fin (N i) => f i)
  let bs i := List.ofFn (fun j => (f i, b i j))
  have setup : Easy (fun v : List A × Tally × List B =>
      (v.1, (ruler v.2.2, v.2.1), v.2.2)) := by fun_prop
  have copies := (((generate (X := Tally)).on (fun i => (ruler (ys i), f i))).left
    (fun i => send (ys i))).right (fun i => send (xs i))
  have hfs i : List.replicate (ruler (ys i)).length (f i) = fs i := by
    simp [ys, fs, List.ofFn_const]
  simp only [hfs] at copies
  have inner := (zipAt N (fun i _ => f i) b).right (fun i => send (xs i))
  have outer := zipAt N a (fun i j => (f i, b i j))
  have total := (((setup.on (fun i => (xs i, f i, ys i))).compose copies).compose inner).compose outer
  apply total.bound 20
  intro i
  let budget := (N i + 1) * (w i + 1)
  have hx : size (xs i) ≤ budget := streamSize _ (ha i)
  have hy : size (ys i) ≤ budget := streamSize _ (hb i)
  have hfsz : size (fs i) ≤ budget := streamSize _ (fun _ => hf i)
  have hbs : size (bs i) ≤ 2 * budget := by
    have t := streamSize (fun j => (f i, b i j)) (w := 2 * w i + 1) (by
      intro j; simp only [size_prod]; have := hf i; have := hb i j; omega)
    convert t using 1
    unfold budget
    ring
  have hw : w i ≤ budget := by unfold budget; nlinarith
  have hdup : ((ruler (ys i)).length + 1) * size (f i) ≤ budget := by
    simp only [ruler_length, ys, List.length_ofFn]
    exact Nat.mul_le_mul_left _ (Nat.le_succ_of_le (hf i))
  have hf' := hf i
  change size (xs i, f i, ys i) +
    ((send (xs i)).count + ((ruler (ys i)).length + 1) * size (f i)) +
    ((send (xs i)).count + size (fs i, ys i)) + size (xs i, bs i) + 1 ≤ 20 * (budget + 1)
  simp only [size_prod]
  change size (xs i) + (size (f i) + size (ys i) + 1) + 1 +
    (size (xs i) + ((ruler (ys i)).length + 1) * size (f i)) +
    (size (xs i) + (size (fs i) + size (ys i) + 1)) + (size (xs i) + size (bs i) + 1) + 1 ≤ _
  omega

end ProductPass

end NearSquareRoot
end Computability
end OAI
