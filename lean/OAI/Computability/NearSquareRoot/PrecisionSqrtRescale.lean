import OAI.Computability.NearSquareRoot.PrecisionProductPass
import OAI.Computability.NearSquareRoot.PrecisionSqrtSetup
import OAI.Computability.NearSquareRoot.BoundedProductRight

/-! # Applying a physically prepared scale to an address-ordered array

The length scan over the input array determines the number of copies of the
scale word. Their order matches the left operand of the pointwise product
command. The original input-width ruler is retained for the readout.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication Code DigitPacking

private theorem markBound {k : ℕ} (x : Record k) : size (Dusk.mark x) ≤ 384 * (k+1) := by
  rw [record_size]
  omega

private theorem paddedSize {N k : ℕ} (u : Fin N → Record k) :
    size (List.ofFn fun j => Dusk.mark (u j)) ≤ 385 * ((N+1)*(k+1)) := by
  have hs := ProductPass.streamSize (fun j => Dusk.mark (u j)) (fun j => markBound (u j))
  calc
    _ ≤ (N+1) * (384*(k+1)+1) := hs
    _ ≤ (N+1) * (385*(k+1)) := by gcongr; omega
    _ = _ := by ring

private theorem scaleCopies {I : Type} (N k : I → ℕ) (a : (i : I) → Record (k i))
    (u : (i : I) → Fin (N i) → Record (k i)) :
    let V i := (N i + 1) * (k i + 1)
    Space.BoundedTask V V
      (fun i => send (Dusk.mark (a i), List.ofFn fun j => Dusk.mark (u i j)))
      (fun i => send (List.ofFn (fun _ : Fin (N i) => Dusk.mark (a i)),
        List.ofFn fun j => Dusk.mark (u i j))) := by
  let xs i := List.ofFn (fun j => Dusk.mark (u i j))
  let one i := Dusk.mark (a i)
  have prep : Easy (fun p : Dusk.Pair × List Dusk.Pair => ((ruler p.2, p.1), p.2)) := by fun_prop
  have replicateRun := ((generate (X := Dusk.Pair)).on (fun i => (ruler (xs i), one i))).left
    (fun i => send (xs i))
  have run := Space.BoundedTask.of_time ((prep.on (fun i => (one i, xs i))).compose replicateRun)
  have volume (i : I) : size (one i, xs i) ≤ 770 * ((N i+1)*(k i+1)) := by
    rw [size_prod]
    have word := markBound (a i)
    change size (one i) ≤ 384 * (k i+1) at word
    have array := paddedSize (u i)
    change size (xs i) ≤ _ at array
    have h : k i+1 ≤ (N i+1)*(k i+1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
    change size (one i) + size (xs i) + 1 ≤ _
    omega
  have copies (i : I) : ((ruler (xs i)).length+1)*size (one i) ≤
      384 * ((N i+1)*(k i+1)) := by
    simp only [ruler_length, xs, List.length_ofFn]
    exact (Nat.mul_le_mul_left _ (markBound (a i))).trans_eq (by ring)
  apply (run.conform (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun i => by
    simp [xs, one, List.ofFn_const])).bound 2000 2000
  · intro i
    have h := volume i
    have g := copies i
    change size (one i, xs i) + ((ruler (xs i)).length+1)*size (one i) + 1 ≤ _
    omega
  · intro i
    have h := volume i
    have g := copies i
    change size (one i, xs i) + (size (one i, xs i) + ((ruler (xs i)).length+1)*size (one i)) + 1 ≤ _
    omega

private theorem arrayBudget {n : ℕ} (hn : 2 ≤ n) :
    (capacity n+1)*(addressBits n+1) ≤ 193*n := by
  obtain ⟨_, upper⟩ := packed_volume hn
  have hk : 0 < addressBits n := by
    have := width_pos hn
    have := width_le_twice_addressBits hn
    omega
  have hN : 0 < capacity n := Nat.two_pow_pos _
  have h1 := Nat.le_mul_of_pos_left (addressBits n) hN
  have h2 := Nat.le_mul_of_pos_right (capacity n) hk
  rw [Nat.add_mul, Nat.mul_add, Nat.mul_one, Nat.one_mul]
  omega

/-- The pass clock is bounded by the input width times the logarithm of its
address width, including rounding to the next power of two. -/
theorem squareRootPass_clock {n : ℕ} (hn : 2 ≤ n) :
    (capacity n + 1) * GridTask.recordCost (addressBits n) ≤
      193 * n * (Nat.clog 2 (addressBits n + 1) + 1) := by
  unfold GridTask.recordCost
  rw [← Nat.mul_assoc]
  exact Nat.mul_le_mul_right _ (arrayBudget hn)

/-- A scale prepared solely from the unary input width can be broadcast and
multiplied on the left while preserving the width and physical rank of every word. -/
theorem scaleArrayFromHeader {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (a : (i : I) → Record (addressBits (n i)))
    (u : (i : I) → Fin (capacity (n i)) → Record (addressBits (n i)))
    (setup : Space.BoundedTask n n (fun i => send (tally (n i))) (fun i => send (Dusk.mark (a i)))) :
    Space.BoundedTask (fun i => (capacity (n i)+1)*GridTask.recordCost (addressBits (n i))) n
      (fun i => send (tally (n i), List.ofFn fun j => Dusk.mark (u i j)))
      (fun i => send (tally (n i), List.ofFn fun j =>
        Dusk.mark (multiply (addressBits (n i)) (a i) (u i j)))) := by
  let k i := addressBits (n i)
  let N i := capacity (n i)
  let xs i := List.ofFn fun j => Dusk.mark (u i j)
  let head i := tally (n i)
  let V i := (N i+1)*(k i+1)
  let T i := (N i+1)*GridTask.recordCost (k i)
  have save : Easy (fun p : Tally × List Dusk.Pair => (p.1, p)) := by fun_prop
  have start := Space.BoundedTask.of_time (save.on (fun i => (head i, xs i)))
  have setupLeft := setup.left (fun i => send (xs i))
  have copies := scaleCopies N k a u
  have multiply := ProductPass.pointwiseSeparate N k (fun i _ => a i) u (fun _ => rfl)
  have inside := ((setupLeft.compose copies).compose multiply).right (fun i => send (head i))
  have run := start.compose inside
  have vol i : V i ≤ 193*n i := arrayBudget (hn i)
  have step i : V i ≤ T i := Nat.mul_le_mul_left _ (GridTask.width_le_recordCost _)
  have width i : n i ≤ T i := by
    have small := (packed_volume (hn i)).1
    have h : capacity (n i)*addressBits (n i) ≤ V i :=
      Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
    exact small.trans (h.trans (step i))
  have inputSize i : size (head i, xs i) ≤ 74400*(n i+1) := by
    have hs := paddedSize (u i)
    change size (xs i) ≤ 385 * V i at hs
    have hv := vol i
    simp only [size_prod, head, size_tally, tally_length]
    omega
  apply run.bound 75000 150000
  · intro i
    have h := inputSize i
    have ht := step i
    have hn' := width i
    change size (head i, xs i) + ((send (head i)).count + (n i + V i + T i)) + 1 ≤ _
    change size (head i, xs i) + (size (head i) + (n i + V i + T i)) + 1 ≤ 75000*(T i+1)
    simp only [head, size_tally, tally_length] at h ⊢
    omega
  · intro i
    have h := inputSize i
    have hv := vol i
    have hs := paddedSize (u i)
    change size (xs i) ≤ 385*V i at hs
    change max (size (head i, xs i) + size (head i, xs i))
      (max (max (n i + size (xs i)) (V i)) (V i) + size (head i)) + 1 ≤ _
    simp only [head, size_tally, tally_length] at h ⊢
    omega

/-- The exact finite record calculated by the square-root setup program. -/
def directoryScale (k : ℕ) : Record k :=
  sqrtRecord (fractionBits k) (componentBits k) (directoryVolume k)

/-- Rebuild the selected coprime box from the input-width ruler, compute its
fixed-point square-root scale and apply that scale to every adjoint record. -/
theorem directorySqrtPass {I : Type} (n : I → ℕ) (hn : ∀ i, 2 ≤ n i)
    (hv : ∀ i, ValidDirectory (addressBits (n i)))
    (u : (i : I) → Fin (capacity (n i)) → Record (addressBits (n i))) :
    Space.BoundedTask (fun i => (capacity (n i)+1)*GridTask.recordCost (addressBits (n i))) n
      (fun i => send (tally (n i), List.ofFn fun j => Dusk.mark (u i j)))
      (fun i => send (tally (n i), List.ofFn fun j =>
        Dusk.mark (multiply (addressBits (n i)) (directoryScale (addressBits (n i))) (u i j)))) :=
  scaleArrayFromHeader n hn (fun i => directoryScale (addressBits (n i))) u (directorySqrtTask n hn hv)

end FixedPoint

end NearSquareRoot
end Computability
end OAI
