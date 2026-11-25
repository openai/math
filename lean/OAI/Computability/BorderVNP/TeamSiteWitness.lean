import OAI.Computability.BorderVNP.TeamContractionReplay
import OAI.Computability.BorderVNP.TeamSiteEvents

/-! # Recovering the unique finite choice prefix from a physical terminal witness

The RAM can be followed on any infinite branch supply. The deterministic replay
of a finite site witness is unaffected by appending unused choices. Two terminal
witnesses which start on prefixes of the same supply therefore have exactly the
same consumed bits, physical time, control and final stacks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSiteWitness

open VPVNP.RAMTape TeamPrivateFragment TeamSiteChoices TeamSiteEvents
open TeamContraction.Replay (terminal_unique)

variable {K Q : Type} [DecidableEq K]

/-- Extending a choice list changes neither the instruction sequence nor any stack,
and the added bits all survive into the returned suffix. -/
theorem append_choices {C : StackCode K Q} {n q choices s t rest out}
    (h : StackRuns (replay C) n (q,choices) s (t,rest) out) (xs : List Bool) :
    StackRuns (replay C) n (q,choices++xs) s (t,rest++xs) out := by
  let labels (z : Q × List Bool) := (z.1, z.2++xs)
  have lifted := h.lift id Function.injective_id labels s (target := replay C) (by
    rintro ⟨q,bs⟩ hc
    rw [replay, replay]
    cases row : C q with
    | choose l r =>
      cases bs with
      | nil => simp [replay,row] at hc
      | cons b tail => simp only [labels,List.cons_append,StackOp.rename]
    | _ => simp [labels,StackOp.rename,Function.comp_def])
  have eq (v : Stacks K) : installStacks id s v = v := funext fun u => installStacks_at Function.injective_id ..
  simpa only [labels,eq] using lifted

private theorem extension (u : Supply) (xs : List Bool) (hp : Prefix u xs) {n : ℕ} (hn : xs.length ≤ n) :
    xs ++ takeBits (drop u xs.length) (n-xs.length) = takeBits u n := by
  rw [← show takeBits u xs.length = xs from hp, prefix_length, ← prefix_add]
  congr 1; omega

/-- Successful or rejecting genuine halts reached on one infinite choice supply consume
the same finite prefix. The outputs, actual elapsed time and entire banks agree. -/
theorem prefix_unique {C : StackCode K Q} (supply : Supply) {x y : List Bool}
    (hx : Prefix supply x) (hy : Prefix supply y) {q s q₁ s₁ q₂ s₂ m n a b}
    (rx : StackRuns (replay C) m (q,x) s (q₁,[]) s₁)
    (ry : StackRuns (replay C) n (q,y) s (q₂,[]) s₂) (h₁ : C q₁ = .halt a) (h₂ : C q₂ = .halt b) :
    x = y ∧ m = n ∧ q₁ = q₂ ∧ s₁ = s₂ := by
  let N := max x.length y.length
  let xx := takeBits (drop supply x.length) (N-x.length)
  let yy := takeBits (drop supply y.length) (N-y.length)
  have one := append_choices rx xx
  have two := append_choices ry yy
  rw [show x++xx = takeBits supply N from extension supply x hx (le_max_left ..)] at one
  rw [show y++yy = takeBits supply N from extension supply y hy (le_max_right ..)] at two
  have halt₁ : replay C (q₁, []++xx) = .halt a := by simp [replay, h₁, StackOp.rename]
  have halt₂ : replay C (q₂, []++yy) = .halt b := by simp [replay, h₂, StackOp.rename]
  obtain ⟨time, labels, bank⟩ := terminal_unique one two halt₁ halt₂
  obtain ⟨controls,suffix⟩ := Prod.mk.inj labels
  have hl := congrArg List.length suffix
  simp only [List.nil_append,xx,yy,prefix_length] at hl
  have len : x.length = y.length := by have h := le_max_left x.length y.length; have h' := le_max_right x.length y.length; dsimp [N] at hl; omega
  exact ⟨hx.symm.trans (len ▸ hy), time, controls, bank⟩

end TeamSiteWitness

end BorderVNP
end Computability
end OAI
