import OAI.Computability.IntegerMultiplication.Code.Dup
import OAI.Computability.IntegerMultiplication.Code.Carry
import OAI.Computability.IntegerMultiplication.Bits.Word

/-! # A tape pass for one padded axis

For each valid outer coordinate copy the current inner mask. For each invalid
one emit an equally long block of false flags. The P192 stack task bounds the
work by a constant times the resulting rectangular volume, including all copies.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace BoxMaskStep
open IntegerMultiplication Code Bits

abbrev Input := (Tally × Tally) × List Bool

def budget (p : Input) : ℕ := (p.1.1.length + p.1.2.length + 1) * (p.2.length+1)

def applyAxis (p : Input) : List Bool :=
  (List.replicate p.1.1.length p.2).flatten ++ List.replicate (p.1.2.length * p.2.length) false

private theorem repeat_false (a b : ℕ) :
    (List.replicate a (List.replicate b false)).flatten = List.replicate (a*b) false := by
  induction a with
  | zero => simp
  | succ a ih => rw [List.replicate_succ, List.flatten_cons, ih, List.replicate_append_replicate, Nat.succ_mul, Nat.add_comm]

private theorem sourceVolume : Volume (fun p : Input => (budget p : ℝ)) send := by
  refine ⟨8, fun p => ?_⟩
  change (size p : ℝ) ≤ 8 * (budget p : ℝ)
  exact_mod_cast (show size p ≤ 8 * budget p from by
    rcases p with ⟨⟨a,b⟩,l⟩
    simp only [budget, size_prod, size_tally, size_word]
    nlinarith)

private theorem replicatePart (r : Input → Tally) (w : Input → List Bool)
    (hr : Easy (fun x => (r x, w x))) (hlen : ∀ p, (r p).length ≤ p.1.1.length + p.1.2.length)
    (hword : ∀ p, (w p).length = p.2.length) :
    Carries (fun p : Input => (budget p : ℝ)) send
      (fun p => send (List.replicate (r p).length (w p)).flatten) := by
  have hpos : ∀ p : Input, (1:ℝ) ≤ budget p := by
    intro p
    exact_mod_cast (Nat.succ_le_iff.mpr (Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)) : 1 ≤ budget p)
  have init := Carries.func (y := id) hpos sourceVolume _ hr
  have gen := Code.generate.on (fun p : Input => (r p,w p))
  have step := (Sized.natural gen).adapts hpos 3 (by
    intro p
    change (((r p).length+1) * size (w p) : ℕ) + (1 : ℝ) ≤ _
    exact_mod_cast (show ((r p).length+1)*size (w p)+1 ≤ 3 * budget p from by
      rw [size_word, hword]; unfold budget
      nlinarith [Nat.mul_le_mul_right (2 * p.2.length + 1) (hlen p)]))
  have mid := init.sequence step
  exact mid.chain (Carries.func mid.budget mid.out List.flatten Easy.flatten)

/-- Output-sensitive expansion of an inner validity mask along one axis. -/
theorem task : Computes budget applyAxis := by
  have h₁ := replicatePart (fun p => p.1.1) Prod.snd (by fun_prop) (by intro p; omega) (by simp)
  have h₂ := replicatePart (fun p => p.1.2) (fun p => p.2.map (fun _ => false))
    (by fun_prop) (by intro p; omega) (by simp)
  have h := h₁.twice h₂
  let parts (p : Input) := ((List.replicate p.1.1.length p.2).flatten,
    (List.replicate p.1.2.length (p.2.map fun _ => false)).flatten)
  change Carries _ send (fun p => send (parts p)) at h
  have u := h.chain (Carries.func (y := parts) h.budget h.out (fun p : List Bool × List Bool => p.1 ++ p.2) Easy.append)
  change Code.Task budget send (fun p : Input => send (applyAxis p))
  simpa only [Nat.ceil_natCast, List.map_const', repeat_false, parts, applyAxis] using u.runs.release

end BoxMaskStep

end NearSquareRoot
end Computability
end OAI
