import OAI.Computability.NearSquareRoot.ScheduleSchoolStep
import OAI.Computability.NearSquareRoot.ScheduleSchoolIO
import Mathlib.Tactic

/-! # Linear-cost segments of the polynomial-time schoolbook candidate -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Schoolbook

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

def operandStream (x y : Word) : List Ltr := x.map Ltr.bit ++ .sep :: y.map Ltr.bit

def boundary (x y : Word) (i : ℕ) : State := next^[i] (start (x,y))

def encoded (s : State) : List Ltr := (send s).spell

theorem boundary_zero (x y : Word) : boundary x y 0 = start (x,y) := rfl

theorem boundary_next (x y : Word) (i : ℕ) :
    boundary x y (i+1) = next (boundary x y i) := Function.iterate_succ_apply' ..

theorem encoded_head (s : State) : (encoded s).head? = some .node := rfl

theorem active_tag (x y : Word) {i : ℕ} (hi : i < y.length) :
    (encoded (boundary x y i))[1]? = some .node := by
  rw [boundary, iterate_start x y i hi.le]
  cases h : y.drop i with
  | nil =>
    have he := congrArg List.length h
    simp at he
    omega
  | cons => rfl

theorem finish_tag (x y : Word) :
    (encoded (boundary x y y.length))[1]? = some (.bit false) := by
  rw [boundary, finished_state]
  rfl

theorem encoded_bound {x y : Word} {i n : ℕ}
    (hx : x.length ≤ n) (hy : y.length ≤ n) (hi : i ≤ y.length) :
    (encoded (boundary x y i)).length ≤ 8*n+5 := by
  simpa [encoded, Code.size, boundary] using size_iterate hx hy hi

private theorem easy_program {X Y : Type} [Codec X] [Codec Y] {f : X → Y} (hf : Easy f) :
    ∃ c : Cmd, ∃ C : ℕ, ∀ x,
      ∃ t ≤ C * (size x + 1), Prog.Run [] c (raw (send x).spell) t
        (raw (send (f x)).spell) := by
  obtain ⟨c,C,hc⟩ := hf
  refine ⟨c,C,fun x => ?_⟩
  obtain ⟨t, ht, run⟩ := hc x [] (fun _ => [])
  exact ⟨t, ht, by simpa only [letters_pile_empty] using run⟩

/-- The same three finite programs serve every input length. All their calls,
including the delimited parser and raw-output conversion, have linear cost. -/
theorem schoolbook_programs :
    ∃ (load step emit : Cmd) (B : ℕ), ∀ x y : Word, ∀ n : ℕ,
      x.length = n → y.length = n →
      (∃ t ≤ B*(n+1), Prog.Run [] load (raw (operandStream x y)) t
        (raw (encoded (boundary x y 0)))) ∧
      (∀ i < y.length, ∃ t ≤ B*(n+1), Prog.Run [] step (raw (encoded (boundary x y i))) t
        (raw (encoded (boundary x y (i+1))))) ∧
      (∃ t ≤ B*(n+1), Prog.Run [] emit (raw (encoded (boundary x y y.length))) t
        (raw ((finish (boundary x y y.length)).map Ltr.bit))) := by
  obtain ⟨a,A,ha⟩ := easy_program easy_start
  obtain ⟨b,D,hb⟩ := easy_program easy_next
  obtain ⟨c,E,hc⟩ := easy_program easy_finish
  let B := 100+8*A+8*D+8*E
  refine ⟨loadCmd.join a, b, c.join unloadCmd, B, fun x y n hx hy => ?_⟩
  have hA : 24 + 8*A ≤ B := by dsimp [B]; omega
  have hD : 8*D ≤ B := by dsimp [B]; omega
  have hE : 32 + 8*E ≤ B := by dsimp [B]; omega
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨t, ht, run⟩ := ha (x,y)
    have hr := Prog.Run.join (load_run x y []) run
    refine ⟨_, ?_, hr⟩
    simp only [size_prod, size_word, hx, hy] at ht
    have h₀ := Nat.mul_le_mul_left A (show 2*n+1+(2*n+1)+1+1 ≤ 8*(n+1) by omega)
    rw [← Nat.mul_assoc, Nat.mul_comm A 8] at h₀
    refine le_trans ?_ (Nat.mul_le_mul_right (n+1) hA)
    rw [Nat.add_mul, hx, hy]
    omega
  · intro i hi
    obtain ⟨t, ht, run⟩ := hb (boundary x y i)
    refine ⟨t, ?_, by simpa only [encoded, boundary_next] using run⟩
    have h₀ := size_iterate hx.le hy.le hi.le
    change size (boundary x y i) ≤ 8*n+5 at h₀
    have h₁ := Nat.mul_le_mul_left D (show size (boundary x y i)+1 ≤ 8*(n+1) by omega)
    rw [← Nat.mul_assoc, Nat.mul_comm D 8] at h₁
    exact (ht.trans h₁).trans (Nat.mul_le_mul_right (n+1) hD)
  · let z := finish (boundary x y y.length)
    obtain ⟨t, ht, run⟩ := hc (boundary x y y.length)
    refine ⟨_, ?_, Prog.Run.join run (unload_run z [])⟩
    have hz : z.length = 2*n := by simpa [z,boundary,hx,hy,two_mul] using (output_exact x y).1
    have h₀ := size_iterate hx.le hy.le (k := y.length) le_rfl
    change size (boundary x y y.length) ≤ 8*n+5 at h₀
    have h₁ := Nat.mul_le_mul_left E (show size (boundary x y y.length)+1 ≤ 8*(n+1) by omega)
    rw [← Nat.mul_assoc, Nat.mul_comm E 8] at h₁
    refine le_trans ?_ (Nat.mul_le_mul_right (n+1) hE)
    rw [Nat.add_mul, hz]
    omega

end Schoolbook

end NearSquareRoot
end Computability
end OAI
