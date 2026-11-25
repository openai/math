import OAI.Computability.BorderVNP.TeamPrivateCall
import OAI.Computability.BorderVNP.TeamPrivateInput

/-!
# The complete private subroutine on raw binary data

The loader, the signed multitape interpreter and the cleanup controls form one
fixed bit-stack program. Its three terminal labels are reusable caller continuations.
The replay theorem starts from raw bits, preserves every private branch choice and
returns with an empty workspace within a linear bound in the input length and time.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamPrivateCompiler

open VPVNP.RAMTape TeamPrivateTape

variable {Q Γ : Type} {m g : ℕ}

/-- The complete private control, with disjoint loader, machine and signed return states. -/
inductive Control (Q : Type) (m g : ℕ) where
  | load (q : TeamPrivateInput.State g)
  | run (q : TeamPrivateFragment.Label Q (m*g))
  | result (sign : Option Bool)

noncomputable instance [Fintype Q] : Fintype (Control Q m g) := derive_fintype% _

private def launch (start : Q) (bits : Fin (m*g) → Bool) : Control Q m g :=
  .run (.inl (.ready start bits))

/-- A concrete fixed finite-control table for any private symbol-tape routine. -/
noncomputable def code (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m)
    (P : TapeTable Q Γ m) (start : Q) : StackCode (TeamPrivateInput.NativePort m g) (Control Q m g)
  | .load q => ((TeamPrivateInput.code (fun b => a.bits (digit b))) q).rename (TeamPrivateInput.ports i)
      (TeamPrivateInput.withHead a digit i Control.load (launch start))
  | .run q => TeamPrivateFragment.rows (trackTable a P) Sum.inr Control.run Control.result q
  | .result sign => .halt sign.isSome

/-- The terminal sign read by the universal signed stack processor. -/
def negative : Control Q m g → Bool
  | .result (some true) => true
  | _ => false

/-- An actual native signed path compiles all the way from a raw input stack to a
signed return label, with its exact list of binary choices consumed. -/
theorem run_input (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m)
    (start : Q) (bs : List Bool) {n choices sign u}
    (run : TeamPrivateFragment.Run (trackTable a P) n start (tracks a (input a.blank digit i bs))
      choices sign u) (suffix : List Bool) :
    StackRuns (TeamPrivateFragment.replay (code a digit i P start))
      (TeamPrivateInput.steps g bs + (n*(2*(m*g)+2)+1 + TeamPrivateCleanup.steps (bank u)))
      (Control.load .start, choices ++ suffix) (TeamPrivateInput.initial bs)
      (Control.result sign, suffix) (fun _ => []) := by
  let C := code a digit i P start
  have hload := TeamPrivateInput.native_runs a digit i bs C Control.load (launch start) (by
    intro q h
    cases q <;> first | rfl | simp [TeamPrivateInput.code] at h)
  let t := tracks a (input a.blank digit i bs)
  have hbody := TeamPrivateFragment.run_linked run Sum.inr Sum.inr_injective Control.run Control.result C
    (fun _ => rfl) (TeamPrivateInput.loaded a digit i bs) suffix
  have hbank : installStacks Sum.inr (TeamPrivateInput.loaded a digit i bs) (bank t) =
      TeamPrivateInput.loaded a digit i bs := installStacks_eq Sum.inr_injective _ _ (fun _ => rfl)
  have hclear : installStacks Sum.inr (TeamPrivateInput.loaded a digit i bs) (fun _ => []) =
      fun _ => [] := by
    funext k
    cases k with
    | inl b => rw [installStacks_outside (hl := fun _ => Sum.inr_ne_inl)]; rfl
    | inr p => rw [installStacks_at Sum.inr_injective]
  rw [hbank, hclear] at hbody
  exact (TeamPrivateFragment.replay_segment hload (choices ++ suffix)).trans hbody

/-- The exact elementary time for a compiled accepting path is linear in the binary
input length and native transition count for fixed tape count and alphabet width. -/
theorem run_input_cost_le (a : Alphabet Γ g) (digit : Bool → Γ) (i : Fin m) (P : TapeTable Q Γ m)
    (start : Q) (bs : List Bool) {n choices sign u}
    (run : TeamPrivateFragment.Run (trackTable a P) n start (tracks a (input a.blank digit i bs))
      choices sign u) :
    TeamPrivateInput.steps g bs + (n*(2*(m*g)+2)+1 + TeamPrivateCleanup.steps (bank u)) ≤
      (2*g+4)*bs.length + n*(3*(m*g)+2) + 2*(m*g) + 5 := by
  have h := TeamPrivateFragment.run_cost_le run
  have hi := input_cells_le a digit i bs
  have hh : bs.tail.length ≤ bs.length := by simp
  calc
    _ ≤ ((g+4)*bs.length+3) + (n*(3*(m*g)+2) + bs.length*g + 2*(m*g)+2) := by
      apply Nat.add_le_add
      · exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hh) 3
      · omega
    _ = _ := by ring

end TeamPrivateCompiler

end BorderVNP
end Computability
end OAI
