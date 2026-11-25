import OAI.Computability.NearSquareRoot.PhysicalWalshBoundary
import OAI.Computability.NearSquareRoot.PhysicalWalshOdd

/-! # End-to-end ordered selected-Walsh traversal

A compact `(k,s)` control word and the original records enter the program.
It emits the grid width, pads spectator rows, executes the even pieces, removes
padding, and conditionally computes the normalized final one-bit butterfly.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.Pieces

open IntegerMultiplication Code Space FixedPoint KernelPass

private def repeatWidth : ℕ → Tally → Tally
  | 0, _ => tally 5
  | n+1, k => k ++ repeatWidth n k

private theorem width_easy (n : ℕ) : Easy (repeatWidth n) := by
  induction n with
  | zero => exact Easy.const (tally 5)
  | succ n ih => exact (Easy.identity.pair ih).compose Easy.append

private theorem width_eq (n k : ℕ) : repeatWidth n (tally k) = tally (n*k+5) := by
  induction n with
  | zero => simp [repeatWidth]
  | succ n ih =>
    change tally k ++ repeatWidth n (tally k) = _
    rw [ih]
    change List.replicate k () ++ List.replicate (n*k+5) () = List.replicate ((n+1)*k+5) ()
    rw [← List.replicate_add,Nat.succ_mul]; congr 1; omega

private def prepareWidth (p : Tally × Tally) := (p,repeatWidth 96 p.1)
private theorem prepare_easy : Easy prepareWidth := Easy.identity.pair (Easy.fst.compose (width_easy 96))

/-- Attach the fixed-point grid width to the controller, scanning the short
counters while the data stream stays parked on the same tape. -/
theorem makeWidth {I : Type} (k s : I → ℕ) (hs : ∀ i,s i ≤ k i)
    (x : (i : I) → ℕ → Record (k i)) :
    BoundedTask (Odd.volume ∘ k) (Odd.volume ∘ k)
      (fun i => send ((tally (k i),tally (s i)),words (2^k i) (x i)))
      (fun i => send (((tally (k i),tally (s i)),tally (componentBits (k i)+1)),words (2^k i) (x i))) := by
  let q i := (tally (k i),tally (s i))
  have task := (BoundedTask.of_time (prepare_easy.on q)).left (fun i => send (words (2^k i) (x i)))
  have eq (i : I) : prepareWidth (q i) = (q i,tally (componentBits (k i)+1)) := by
    simp only [prepareWidth,q,width_eq,componentBits,Nat.add_assoc]
  simp only [eq] at task
  apply task.bound 20 900 <;> intro i
  all_goals
    have kv : k i+1 ≤ Odd.volume (k i) := Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _)
    have hq : size (q i) ≤ 4*(k i)+3 := by simp only [q,size_prod,size_tally,tally_length]; have := hs i; omega
    have hx : size (words (2^k i) (x i)) ≤ 400*Odd.volume (k i)+1 := by
      rw [words_size]; unfold Odd.volume componentBits; ring_nf; omega
  · change size (q i)+1 ≤ 20*(Odd.volume (k i)+1); omega
  · change size (q i)+size (q i)+size (words (2^k i) (x i))+1 ≤ 900*(Odd.volume (k i)+1); omega

/-- The root record stream used by the uniform recursive interpreter, with
canonical zeroes throughout the extra rows. -/
def root (k s : ℕ) (x : ℕ → Record k) : Root := ⟨k,s,componentBits k,zeroAfter (2^k) x⟩

variable {a W : ℕ} (hw : 0<W) (p : Plan (a+1) W W)

/-- Rounded result on the original finite record space. -/
def result (k s : ℕ) (x : ℕ → Record k) : Fin (2^k) → Record k :=
  let b := root k s x
  Odd.finish s (fun j => b.stage hw p (b.pieces (a:=a) hw).length j.val)

variable {I : Type} (k s : I → ℕ) (x : (i : I) → ℕ → Record (k i))

/-- Full boundary program around any certified physical execution of the
rounded even-piece trajectory, including the exactly normalized parity branch. -/
theorem groupedPass (sel : ∀ i,s i ≤ k i)
    (occ : ∀ i,PaddingHeader.extra (a+1) W (k i) (s i) ≤ 2^k i)
    (t r : I → ℕ) :
    let b i := root (k i) (s i) (x i)
    BoundedTask t r (fun i => send (((tally (k i),tally (s i)),tally (componentBits (k i)+1)),
        words ((b i).size (a:=a) (W:=W)) (b i).row))
      (fun i => send ((b i).stream hw p ((b i).pieces (a:=a) hw).length)) →
    BoundedTask (fun i => t i+Odd.time (k i)) (fun i => r i+Odd.volume (k i))
      (fun i => send ((tally (k i),tally (s i)),words (2^k i) (x i)))
      (fun i => send (Odd.words (result hw p (k i) (s i) (x i)))) := by
  intro b sweep
  let y i := (b i).stage hw p ((b i).pieces (a:=a) hw).length
  have centered := boundaries (a+1) W hw k s (fun i => componentBits (k i)) x y sel occ t r sweep
  have whole := ((makeWidth k s sel x).compose centered).compose (Odd.bounded_range k s sel y)
  apply whole.bound 110 110 <;> intro i
  all_goals
    have ratio : 2^k i*(componentBits (k i)+1) ≤ 96*Odd.volume (k i) := by
      unfold Odd.volume componentBits; ring_nf; omega
    have vt : Odd.volume (k i) ≤ Odd.time (k i) := Nat.mul_le_mul_left _ (GridTask.width_le_recordCost _)
  · change Odd.volume (k i)+(2^k i*(componentBits (k i)+1)+t i)+Odd.time (k i)+1 ≤ _
    omega
  · change max (max (Odd.volume (k i)) (2^k i*(componentBits (k i)+1)+r i)) (Odd.volume (k i))+1 ≤ _
    omega

end PhysicalWalsh.Pieces

end NearSquareRoot
end Computability
end OAI
