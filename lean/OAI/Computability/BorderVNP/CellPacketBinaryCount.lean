import OAI.Computability.BorderVNP.CellPacketReadMany

/-! # Reading a binary list length into a private unary counter

The input digits are most significant first. Each digit doubles the current
unary count with one scratch stack, then adds its low bit. The source, output
and the two other lexical counters stay available to the enclosing reader.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Native

open ExactQuantumFactoring.BitStackProgram

private def twice (k : Fin 3) : Program Register :=
  .seq (.push (.counter k) true) (.push (.counter k) true)

private def doubleBack (k : Fin 3) : Program Register :=
  .loop .scratch (twice k) (twice k)

private def digitStep (k : Fin 3) (b : Bool) : Program Register :=
  .seq (reverseMove (.counter k) .scratch)
    (.seq (doubleBack k) (if b then .push (.counter k) true else .skip))

/-- Consume the most-significant-first digit stack and build a unary count in slot `k`. -/
def countCode (k : Fin 3) : Program Register := .loop .digits (digitStep k false) (digitStep k true)

private def work (base : Store Register) (k : Fin 3) (bits : List Bool) (n t : ℕ) : Store Register
  | .digits => bits
  | .scratch => List.replicate t true
  | .counter i => if i = k then List.replicate n true else base (.counter i)
  | r => base r

private theorem write_count (base : Store Register) (k : Fin 3) (bits : List Bool) (n t m : ℕ) :
    Function.update (work base k bits n t) (.counter k) (List.replicate m true) = work base k bits m t := by
  funext r
  cases r <;> simp [Function.update,work]
  rename_i i
  split <;> simp_all

private theorem write_scratch (base : Store Register) (k : Fin 3) (bits : List Bool) (n t m : ℕ) :
    Function.update (work base k bits n t) .scratch (List.replicate m true) = work base k bits n m := by
  funext r; cases r <;> simp [work, Function.update]

private theorem write_digits (base : Store Register) (k : Fin 3) (a b : List Bool) (n t : ℕ) :
    Function.update (work base k a n t) .digits b = work base k b n t := by
  funext r; cases r <;> simp [work, Function.update]

private theorem push_one (base : Store Register) (k : Fin 3) (bits : List Bool) (n t : ℕ) :
    Runs (.push (.counter k) true) (work base k bits n t) (work base k bits (n+1) t) 1 := by
  have a := Runs.push (work base k bits n t) (.counter k) true
  have h : true :: work base k bits n t (.counter k) = List.replicate (n+1) true := by
    simp [work,List.replicate_succ]
  rw [h, write_count] at a
  exact a

private theorem doubleBack_runs (base : Store Register) (k : Fin 3) (bits : List Bool) (n t : ℕ) :
    Runs (doubleBack k) (work base k bits n t) (work base k bits (n+2*t) 0) (3*t+1) := by
  induction t generalizing n with
  | zero =>
    simpa only [doubleBack,Nat.mul_zero,Nat.add_zero,Nat.zero_add] using
      (Runs.loop_nil (k := Register.scratch) (p := twice k) (q := twice k) (s := work base k bits n 0) rfl)
  | succ t ih =>
    have h := (push_one base k bits n t).seq (push_one base k bits (n+1) t)
    have step : Runs (twice k)
        (Function.update (work base k bits n (t+1)) .scratch (List.replicate t true))
        (work base k bits (n+2) t) 2 := by rw [write_scratch]; exact h
    have loop := Runs.loop_true (p := twice k) (q := twice k)
      (show work base k bits n (t+1) .scratch = true :: List.replicate t true by simp [work,List.replicate_succ])
      step (ih (n+2))
    rw [show n+2*(t+1) = n+2+2*t by omega, show 3*(t+1)+1 = (3*t+1)+2+1 by omega]
    exact loop

private theorem digitStep_runs (base : Store Register) (k : Fin 3) (bits : List Bool) (n : ℕ) (b : Bool) :
    Runs (digitStep k b) (work base k bits n 0) (work base k bits (Nat.bit b n) 0) (5*n+3) := by
  have move := reverseMove_runs (Register.counter k) .scratch (by intro h; cases h) (work base k bits n 0)
  have src : work base k bits n 0 (.counter k) = List.replicate n true := by simp [work]
  rw [src, List.reverse_replicate, show work base k bits n 0 .scratch = [] from rfl, List.append_nil,
    show ([] : List Bool) = List.replicate 0 true from rfl, write_count, write_scratch, List.length_replicate] at move
  have back := doubleBack_runs base k bits 0 n
  rw [Nat.zero_add] at back
  cases b with
  | false =>
    have done := move.seq (back.seq (Runs.skip (work base k bits (2*n) 0)))
    rw [show 5*n+3 = (1+(3*n+1))+(2*n+1) by omega]
    exact done
  | true =>
    have done := move.seq (back.seq (push_one base k bits (2*n) 0))
    rw [show 5*n+3 = (1+(3*n+1))+(2*n+1) by omega]
    exact done

private def value (n : ℕ) (bits : List Bool) : ℕ := bits.foldl (fun a b => Nat.bit b a) n

private theorem value_ge (n : ℕ) (bits : List Bool) : n ≤ value n bits := by
  induction bits generalizing n with
  | nil => exact le_rfl
  | cons b bs ih =>
    exact (show n ≤ Nat.bit b n by cases b <;> simp [Nat.bit] <;> omega).trans (ih _)

private theorem count_runs (base : Store Register) (k : Fin 3) (bits : List Bool) (n : ℕ) :
    ∃ c ≤ (5*value n bits+4)*bits.length+1,
      Runs (countCode k) (work base k bits n 0) (work base k [] (value n bits) 0) c := by
  induction bits generalizing n with
  | nil => exact ⟨1,by simp,Runs.loop_nil rfl⟩
  | cons b bs ih =>
    let v := value (Nat.bit b n) bs
    obtain ⟨c,hc,tail⟩ := ih (Nat.bit b n)
    have step := digitStep_runs base k bs n b
    rw [← write_digits base k (b::bs) bs n 0] at step
    have hn := value_ge n (b::bs)
    change n ≤ v at hn
    refine ⟨c+(5*n+3)+1,?_,?_⟩
    · change c+(5*n+3)+1 ≤ (5*v+4)*(bs.length+1)+1
      change c ≤ (5*v+4)*bs.length+1 at hc
      rw [Nat.mul_add,Nat.mul_one]
      omega
    · cases b
      · exact Runs.loop_false rfl step tail
      · exact Runs.loop_true rfl step tail

private theorem value_bits (n : ℕ) : value 0 n.bits.reverse = n ∧ n.bits.length ≤ n := by
  induction n using Nat.binaryRec' with
  | zero => exact ⟨rfl,le_rfl⟩
  | bit b n hn ih =>
    rw [Nat.bits_append_bit n b hn]
    simp only [value,List.reverse_cons,List.foldl_append,List.foldl_cons,List.foldl_nil,List.length_cons]
    constructor
    · exact congrArg (Nat.bit b) ih.1
    · cases b <;> simp [Nat.bit] at hn ⊢ <;> omega

/-- The decoder runs on the actual bank and returns exactly one unary token
per list element, within the clock expected by the nested packet reader. -/
theorem countCode_runs (k : Fin 3) (n : ℕ) (src out : List Bool) (ct : Fin 3 → List Bool) (hc : ct k = []) :
    ∃ c ≤ 20*(n+1)^2, Runs (countCode k) (Function.update (bank src out ct) .digits n.bits.reverse)
      (bank src out (Function.update ct k (List.replicate n true))) c := by
  obtain ⟨a,ha,run⟩ := count_runs (bank src out ct) k n.bits.reverse 0
  obtain ⟨hv,hl⟩ := value_bits n
  rw [hv, List.length_reverse] at ha
  rw [hv] at run
  have initial : Function.update (bank src out ct) .digits n.bits.reverse =
      work (bank src out ct) k n.bits.reverse 0 0 := by
    funext r; cases r <;> simp [work, bank, Function.update]
    rintro rfl
    exact hc
  have final : work (bank src out ct) k [] n 0 = bank src out (Function.update ct k (List.replicate n true)) := by
    funext r; cases r <;> simp [work, bank, Function.update]
  refine ⟨a,?_,initial.symm ▸ final ▸ run⟩
  exact ha.trans ((Nat.add_le_add_right (Nat.mul_le_mul_left (5*n+4) hl) 1).trans (by nlinarith))

/-- The decoder supplies the count header for any of the three nesting levels. -/
def binaryCountRoutine (k : Fin 3) : CountRoutine k := ⟨countCode k,20,countCode_runs k⟩

end CellSparse.Packet.Native

end BorderVNP
end Computability
end OAI
