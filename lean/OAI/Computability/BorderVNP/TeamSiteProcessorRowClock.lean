import OAI.Computability.BorderVNP.TeamSiteProcessorRowIff

/-! # The measured clock for a native certificate on the physical input row

A native row cannot charge more than its initial block countdown. The parser
cost and the physical geometry therefore bound the replay on every choice
string at this row, including zero-weight private computations.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.Processor.Row

open VPVNP BurstRAM RAMTape TeamSiteEvents TeamTapeHandoff Filter

variable {Q Γ : Type} {p r k a m g n d e w : ℕ}
variable {P : TeamOpcode.Program p r k a} {lib : Fin a → Macro Q Γ m g}
variable (X : Context P lib n d e w)

/-- Native endpoint validation bounds the charged events by this row's actual
initial local countdown, including already halted predecessor frames. -/
theorem Context.charge_le (fuel : ℕ) {es : List (TeamRAM.Event w)} {out : Frame w r}
    (certificate : EndpointRow P X.pub (macros lib fuel) X.block X.limit X.cap X.frame es out) :
    TeamTapeHandoff.cost es ≤ X.block.val := by
  cases frame : X.frame with
  | accepted elapsed =>
    rw [frame] at certificate
    obtain ⟨rfl,_,_⟩ := certificate
    exact Nat.zero_le _
  | live word regs elapsed =>
    rw [frame] at certificate
    obtain ⟨ok,pc,z,fin,_,chunk,_⟩ := certificate
    exact (chunk.clock (X.windowSafe elapsed ok)).1

/-- The total physical budget covers the row cost when its executed prefix is
bounded by the input parser and word/frame loader costs. -/
theorem Context.cost_le_total (dataLength : ℕ) (prefixBound : X.preludeTicks ≤
      Budget.inputCost n w (2^e) dataLength + Budget.prefixCost r k w X.last)
    (body : ℕ) (es : List (TeamRAM.Event w)) :
    X.cost body es ≤ Budget.total r k n d e w dataLength body (X.slots es).length X.last := by
  unfold Context.cost Budget.total
  omega

/-- At every sufficiently large length, one clock covers all measured physical
rows and every endpoint certificate. The threshold depends on the fixed machine
architecture. The words, processor roles, inputs, and histories may all vary. -/
theorem eventually_row_clock (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) :
    ∀ᶠ n : ℕ in atTop, ∀ {d e w : ℕ} (X : Context P lib n d e w) (fuel dataLength : ℕ),
      X.block.val ≤ n → 2+e+d ≤ n → dataLength ≤ n → fuel ≤ n^25+1 →
      X.preludeTicks ≤ Budget.inputCost n w (2^e) dataLength + Budget.prefixCost r k w X.last →
      X.coversClock fuel (n^36) (fun es => X.cost (nativeCost w m g fuel es) es) := by
  filter_upwards [Budget.eventually_chunk_clock r k m g] with n clock
  intro d e w X fuel dataLength block dim data native front es out certificate
  have ticks := (X.charge_le fuel certificate).trans block
  exact (X.cost_le_total dataLength front _ es).trans
    (clock es (X.slots es).length X.last X.hw X.hB dim data native ticks)

end TeamSite.Processor.Row

end BorderVNP
end Computability
end OAI
