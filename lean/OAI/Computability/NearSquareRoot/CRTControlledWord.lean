import OAI.Computability.IntegerMultiplication.Bits.Small
import OAI.Computability.IntegerMultiplication.Carry.Wide
import OAI.Computability.IntegerMultiplication.Code.Iter

/-! # Binary word operations for routing tables

P192's stack programs compare both the lengths and the binary values of two words.
The length test ensures that distinct zero-padded keys stay distinct. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Benes
open IntegerMultiplication IntegerMultiplication.Code

theorem easyWordHead : Easy (fun l : List Bool => l.headD false) := Code.Iter.leader false

theorem easyWordTail : Easy (fun l : List Bool => l.tail) := by
  have H := Easy.listCase ([] : List Bool) (Easy.snd (X := Bool) (Y := List Bool))
  convert H using 1
  funext l
  cases l <;> rfl

theorem easyWordEq : Easy (fun t : List Bool × List Bool => decide (t.1 = t.2)) := by
  let check (p : Bool × Bool × Bool) := p.1 && !(p.2.1 || p.2.2)
  have c := (Code.Iter.linked (X := Bool) (Y := Bool)).pair
    ((Bits.easy_more Easy.identity).pair (Bits.easy_more Easy.exchange))
  have H := c.compose (Easy.finite check)
  convert H using 1
  funext t
  apply Bool.eq_iff_iff.mpr
  change decide (t.1 = t.2) = true ↔
    ((decide (t.1.length = t.2.length)) && !(Bits.more (t.1,t.2) || Bits.more (t.2,t.1))) = true
  simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_true', Bool.or_eq_false_iff]
  have leftTest := Bits.more_lt t.1 t.2
  have rightTest := Bits.more_lt t.2 t.1
  constructor
  · intro eq
    have hr := (Bits.more_lt t.1 t.1).not.mpr (Nat.lt_irrefl _)
    have hz : Bits.more (t.1,t.1) = false := by simpa using hr
    simpa only [← eq] using And.intro (rfl : t.1.length = t.1.length) (And.intro hz hz)
  · rintro ⟨hlen,hleft,hright⟩
    apply Bits.word_inject _ _ hlen
    rw [hleft] at leftTest
    rw [hright] at rightTest
    simp only [Bool.false_eq_true, false_iff] at leftTest rightTest
    omega

/-- Numbering a width-`d` port needs at most one tally cell per port. -/
def wordNumber (d : ℕ) (x : Fin d → Bool) : Tally := tally (Bits.value (List.ofFn x))

theorem wordNumber_injective (d : ℕ) : Function.Injective (wordNumber d) := by
  intro x y h
  have hv := congrArg List.length h
  simp only [wordNumber, tally_length] at hv
  exact List.ofFn_injective (Bits.word_inject _ _ (by simp) hv)

theorem wordNumber_lt {d : ℕ} (x : Fin d → Bool) : (wordNumber d x).length < 2^d := by
  simpa only [wordNumber, tally_length, List.length_ofFn] using Bits.value_lt (List.ofFn x)

/-- One fixed tape program numbers ports of every width. The cost is linear in the
number of possible ports, including the unary output. -/
theorem wordNumber_task :
    Task (fun z : Σ d, Fin d → Bool => 2^z.1)
      (fun z => send (List.ofFn z.2)) (fun z => send (wordNumber z.1 z.2)) := by
  let words := fun z : Σ d, Fin d → Bool => List.ofFn z.2
  apply (Carry.rice.on words).bound 4
  intro z
  have h := Bits.value_lt (words z)
  have hd : z.1 < 2^z.1 := Nat.lt_two_pow_self
  simp only [words,List.length_ofFn] at h
  simp only [words,Bits.size_word,List.length_ofFn]
  omega

end Benes

end NearSquareRoot
end Computability
end OAI
