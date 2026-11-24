import OAI.Computability.VPVNP.RAMTapeSuccessorEnds
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import Mathlib.Data.Fintype.Sigma

/-!
# Dispatch on the two end conditions of a site

A fixed finite routine first scans the site's address, preserving its bits.
The two resulting flags select one of four finite continuations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorEnds

open BurstRAM

variable {K : Type}

private abbrev Labels (body : Bool → Bool → FiniteRoutine K) :=
  State ⊕ (Σ flags : Bool × Bool, (body flags.1 flags.2).State)

/-- Scan the address for outgoing and incoming edges, restore it, then enter the continuation
selected by the two flags. -/
def dispatch (src tmp : K) (body : Bool → Bool → FiniteRoutine K) : FiniteRoutine K :=
  FiniteRoutine.ofRoutine ({
    entry := .inl (.read false false)
    code
      | .inl (.done outgoing incoming) =>
        .goto (some (.inr ⟨(outgoing, incoming), (body outgoing incoming).body.entry⟩))
      | .inl q => (code src tmp q).rename id (some ∘ Sum.inl)
      | .inr ⟨f, q⟩ => (body f.1 f.2).body.install (fun q ↦ .inr ⟨f, q⟩) none q
    } : Routine K (Labels body))

theorem dispatch_runs [DecidableEq K] {d : ℕ} (src tmp : K) (hne : src ≠ tmp)
    (body : Bool → Bool → FiniteRoutine K) (s : Stacks K) (v : Word d)
    (hv : s src = BurstRAM.wordBits v) (ht : s tmp = []) {n : ℕ} {out : Stacks K}
    (hb : (body (decide (v.val + 1 < 2 ^ d)) (decide (0 < v.val))).Runs n s out) :
    (dispatch src tmp body).Runs (4 * d + 3 + n) s out := by
  let r := (dispatch src tmp body).body
  let f := (decide (v.val + 1 < 2 ^ d), decide (0 < v.val))
  have he := (word_run src tmp hne s v hv ht).lift id Function.injective_id
    (fun q ↦ some (Sum.inl q)) s (target := r.standalone)
    (by intro q h; cases q <;> first | rfl | contradiction)
  have hframe : installStacks id s s = s := funext fun i ↦ installStacks_at Function.injective_id s s i
  rw [hframe] at he
  have hj : StackStep r.standalone (some (.inl (.done f.1 f.2))) s
      (some (.inr ⟨f, (body f.1 f.2).body.entry⟩)) s := .goto rfl
  have hrun := hb.link r (fun q ↦ .inr ⟨f, q⟩) none (fun _ ↦ rfl)
  rw [show 4 * d + 3 + n = (4 * d + 2) + (n + 1) by omega]
  exact he.trans (.cons hj hrun)

end RAMTape.SuccessorEnds

end VPVNP
end Computability
end OAI
