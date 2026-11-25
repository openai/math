import OAI.Optimization.LinearProgramming.OracleSpec.ArithmeticEncoding
import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding

/-! The public dimension is binary, while the allowed clock is polynomial in its *value*.
The work tape is padded using explicit bit-stack instructions before invoking any program
that promises polynomial work in a word's length. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace OracleSpec
namespace UnaryBootstrap

open ExactQuantumFactoring.BitStackProgram

private def bank (wire unary digits scratch : Word) : Store (Fin 4) := ![wire, unary, digits, scratch]

@[simp] private theorem bank_0 (w u b s : Word) : bank w u b s 0 = w := rfl
@[simp] private theorem bank_1 (w u b s : Word) : bank w u b s 1 = u := rfl
@[simp] private theorem bank_2 (w u b s : Word) : bank w u b s 2 = b := rfl
@[simp] private theorem bank_3 (w u b s : Word) : bank w u b s 3 = s := rfl

@[simp] private theorem set_0 (w u b s x : Word) :
    Function.update (bank w u b s) 0 x = bank x u b s := by
  funext i; fin_cases i <;> simp
@[simp] private theorem set_1 (w u b s x : Word) :
    Function.update (bank w u b s) 1 x = bank w x b s := by
  funext i; fin_cases i <;> simp
@[simp] private theorem set_2 (w u b s x : Word) :
    Function.update (bank w u b s) 2 x = bank w u x s := by
  funext i; fin_cases i <;> simp
@[simp] private theorem set_3 (w u b s x : Word) :
    Function.update (bank w u b s) 3 x = bank w u b x := by
  funext i; fin_cases i <;> simp

private def twoPushes : Program (Fin 4) := .seq (.push 3 true) (.push 3 true)
private def doubleUnary : Program (Fin 4) := .seq (.loop 1 twoPushes twoPushes) (reverseMove 3 1)
private def digit : Bool → Program (Fin 4)
  | false => doubleUnary
  | true => .seq doubleUnary (.push 1 true)
private def readDigits : Program (Fin 4) := .loop 2 (digit false) (digit true)

private theorem twoPushes_runs (w u b : Word) (r : ℕ) :
    Runs twoPushes (bank w u b (List.replicate r true))
      (bank w u b (List.replicate (r+2) true)) 2 := by
  have a := Runs.push (bank w u b (List.replicate r true)) 3 true
  have z := Runs.push (bank w u b (true :: List.replicate r true)) 3 true
  simp only [bank_3, set_3] at a z
  simpa only [twoPushes, List.replicate_succ] using Runs.seq a z

private theorem copyDouble_runs (w b : Word) (n r : ℕ) :
    Runs (.loop 1 twoPushes twoPushes) (bank w (List.replicate n true) b (List.replicate r true))
      (bank w [] b (List.replicate (2*n+r) true)) (3*n+1) := by
  induction n generalizing r with
  | zero =>
    simpa using (Runs.loop_nil (p := twoPushes) (q := twoPushes)
      (k := (1 : Fin 4)) (s := bank w [] b (List.replicate r true)) rfl)
  | succ n ih =>
    have loop := ih (r+2)
    have body := twoPushes_runs w (List.replicate n true) b r
    have step := Runs.loop_true (p := twoPushes) (q := twoPushes) (k := (1 : Fin 4))
      (s := bank w (List.replicate (n+1) true) b (List.replicate r true))
      (xs := List.replicate n true) (a := 2) (b := 3*n+1) (by simp [List.replicate_succ])
      (by simpa only [set_1] using body) loop
    convert step using 1
    congr 2
    omega

private theorem doubleUnary_runs (w b : Word) (n : ℕ) :
    Runs doubleUnary (bank w (List.replicate n true) b []) (bank w (List.replicate (2*n) true) b [])
      (7*n+2) := by
  have read := copyDouble_runs w b n 0
  simp only [Nat.add_zero, List.replicate_zero] at read
  have write := reverseMove_runs (3 : Fin 4) 1 (by decide) (bank w [] b (List.replicate (2*n) true))
  simp only [bank_3, bank_1, set_3, set_1, List.reverse_replicate, List.append_nil, List.length_replicate] at write
  have h := Runs.seq read write
  rw [show 7*n+2 = (2*(2*n)+1)+(3*n+1) by omega]
  exact h

private theorem digit_runs (w b : Word) (n : ℕ) (x : Bool) :
    Runs (digit x) (bank w (List.replicate n true) b []) (bank w (List.replicate (Nat.bit x n) true) b [])
      (7*n+2+x.toNat) := by
  have dbl := doubleUnary_runs w b n
  cases x with
  | false => simpa [digit, Nat.bit_val] using dbl
  | true =>
    have add := Runs.push (bank w (List.replicate (2*n) true) b []) 1 true
    simp only [bank_1, set_1] at add
    have h := Runs.seq dbl add
    simpa [digit, Nat.bit_val, List.replicate_succ, Nat.add_comm 1] using h

private def readValue (xs : Word) (acc : ℕ) := xs.foldl (fun n b => Nat.bit b n) acc

private theorem le_readValue (xs : Word) (acc : ℕ) : acc ≤ readValue xs acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons b bs ih =>
    exact (show acc ≤ Nat.bit b acc by rw [Nat.bit_val]; omega).trans (ih (Nat.bit b acc))

private theorem readDigits_runs (w xs : Word) (acc : ℕ) :
    ∃ n ≤ xs.length*(7*readValue xs acc+4)+1,
      Runs readDigits (bank w (List.replicate acc true) xs [])
        (bank w (List.replicate (readValue xs acc) true) [] []) n := by
  induction xs generalizing acc with
  | nil => exact ⟨1, by simp, Runs.loop_nil rfl⟩
  | cons b bs ih =>
    obtain ⟨n, hn, tail⟩ := ih (Nat.bit b acc)
    have body := digit_runs w bs acc b
    have hb : acc ≤ readValue bs (Nat.bit b acc) := le_readValue (b::bs) acc
    have bit : b.toNat ≤ 1 := by cases b <;> decide
    refine ⟨n+(7*acc+2+b.toNat)+1, ?_, ?_⟩
    · change n+(7*acc+2+b.toNat)+1 ≤ (bs.length+1)*(7*readValue bs (Nat.bit b acc)+4)+1
      rw [Nat.add_mul, Nat.one_mul]; omega
    · cases b with
      | false =>
        apply Runs.loop_false (k := (2 : Fin 4)) (p := digit false) (q := digit true)
          (s := bank w (List.replicate acc true) (false :: bs) [])
          (xs := bs) (a := 7*acc+2+false.toNat) (b := n) rfl
        · simpa only [set_2] using body
        · exact tail
      | true =>
        apply Runs.loop_true (k := (2 : Fin 4)) (p := digit false) (q := digit true)
          (s := bank w (List.replicate acc true) (true :: bs) [])
          (xs := bs) (a := 7*acc+2+true.toNat) (b := n) rfl
        · simpa only [set_2] using body
        · exact tail

/-- Four fixed binary stacks suffice. Decode N without losing the original public input,
read its bits from most to least significant, and frame the unary answer on the input wire. -/
def program : Program (Fin 4) :=
  .seq (unquoteMove 0 1 2 3) (.seq (duplicateReverse 1 2 3)
    (.seq (quoteMove 1 0 3) (.seq readDigits (quoteMove 1 0 3))))

private theorem bank_zero (w : Word) : bank w [] [] [] = singletonStore 0 w := by
  funext i; fin_cases i <;> simp [singletonStore]

/-- Runtime depends on the *value* of n. All tags, writes and stack scans are included. -/
theorem program_runs (n : ℕ) (rest : Word) :
    ∃ steps ≤ 64*(n+1)^2, Runs program (singletonStore 0 (encodeNat n ++ rest))
      (singletonStore 0 (frame (List.replicate n true) ++ (encodeNat n ++ rest))) steps := by
  let w := encodeNat n ++ rest
  have a := unquoteMove_runs (0 : Fin 4) 1 2 3 (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) n.bits rest (bank w [] [] [])
    (by simp [w, encodeNat, quoteBits_eq_frame]) rfl rfl
  simp only [bank_1, List.append_nil, set_0, set_1] at a
  have b := duplicateReverse_runs (1 : Fin 4) 2 3 (by decide) (by decide) (by decide)
    (bank rest n.bits [] []) rfl
  simp only [bank_1, bank_2, set_2, List.append_nil] at b
  have c := quoteMove_runs (1 : Fin 4) 0 3 (by decide) (by decide) (by decide)
    (bank rest n.bits n.bits.reverse []) rfl
  simp only [bank_1, bank_0, set_1, set_0, quoteBits_eq_frame] at c
  have val : readValue n.bits.reverse 0 = n := by
    simpa only [readValue, List.foldl_reverse] using natBits_decode n
  obtain ⟨k,hk,r⟩ := readDigits_runs w n.bits.reverse 0
  rw [val] at hk r
  simp only [List.replicate_zero] at r
  have d := quoteMove_runs (1 : Fin 4) 0 3 (by decide) (by decide) (by decide)
    (bank w (List.replicate n true) [] []) rfl
  simp only [bank_1, bank_0, set_0, set_1, List.length_replicate, quoteBits_eq_frame] at d
  have run := Runs.seq a (Runs.seq b (Runs.seq c (Runs.seq r d)))
  simp only [List.length_reverse] at hk
  have hlen : n.bits.length ≤ n := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr n.lt_two_pow_self
  have hm := Nat.mul_le_mul_right (7*n+4) hlen
  refine ⟨7*n+5+k+(7*n.bits.length+5)+(5*n.bits.length+2)+(7*n.bits.length+6), ?_, ?_⟩
  · nlinarith
  · simpa only [← bank_zero, program] using run

end UnaryBootstrap
end OracleSpec
end LinearProgramming
end Optimization
end OAI
