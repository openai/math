import OAI.Computability.BorderVNP.CellAddressEvaluator
import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.StructuredStackLoop

/-! # Private scratch banks for the sparse generator's returning routines -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellMacro.Generator

open VPVNP.RAMTape

/-- Caller-visible input, enclosing loop environment and reversed output bitstream. -/
inductive IO where
  | row | env | out
  deriving DecidableEq

instance : Fintype IO := derive_fintype% _

/-- Values at the three public call-boundary ports. -/
def io (row env out : List Bool) : Stacks IO
  | .row => row
  | .env => env
  | .out => out

/-- A returning finite routine with private work registers beyond its call-boundary ports. -/
structure Fragment (K : Type) where
  /-- Scratch names local to this routine, fixed independently of the input. -/
  Scratch : Type
  /-- Only finitely many work stacks are allocated. -/
  [finite : Fintype Scratch]
  /-- Work stack names can be compared. -/
  [decEq : DecidableEq Scratch]
  /-- Actual elementary instruction table of the routine. -/
  body : FiniteRoutine (K ⊕ Scratch)

attribute [instance] Fragment.finite Fragment.decEq

namespace Fragment

variable {K L : Type} [DecidableEq K] [DecidableEq L]

/-- At entry and normal return every private scratch stack is empty. -/
abbrev bank (r : Fragment K) (s : Stacks K) : Stacks (K ⊕ r.Scratch) := Sum.elim s (fun _ => [])

/-- Actual deterministic instruction sequence of one call, preserving scratch cleanliness. -/
abbrev Runs (r : Fragment K) (n : ℕ) (s u : Stacks K) := r.body.Runs n (r.bank s) (r.bank u)

/-- Expose an ordinary returning routine on all its existing ports. -/
def plain (f : FiniteRoutine K) : Fragment K where
  Scratch := Empty
  body := f.onPorts Sum.inl

/-- Exposing all ports incurs no instructions. -/
theorem runs_plain {f : FiniteRoutine K} {t : ℕ} {s u : Stacks K} (h : f.Runs t s u) :
    (plain f).Runs t s u := by
  apply f.runs_onPorts_framed Sum.inl_injective h (fun _ => rfl) (fun _ => rfl)
  intro p hp
  cases p with
  | inl k => exact (hp k rfl).elim
  | inr e => exact e.elim

/-- Rename public ports to selected registers of a larger caller. -/
def mount (r : Fragment K) (ports : K → L) : Fragment L where
  Scratch := r.Scratch
  body := r.body.onPorts (Sum.map ports id)

/-- Running a mounted fragment leaves every caller port outside its image unchanged. -/
theorem runs_mount (r : Fragment K) {ports : K → L} (hp : Function.Injective ports)
    {t : ℕ} {s u : Stacks K} {a b : Stacks L} (h : r.Runs t s u)
    (hin : ∀ k, a (ports k) = s k) (hout : ∀ k, b (ports k) = u k)
    (hother : ∀ l, (∀ k, ports k ≠ l) → b l = a l) : (r.mount ports).Runs t a b := by
  apply r.body.runs_onPorts_framed (Sum.map_injective.mpr ⟨hp, Function.injective_id⟩) h
  · intro p; cases p with | inl k => exact hin k | inr j => rfl
  · intro p; cases p with | inl k => exact hout k | inr j => rfl
  · intro p hn
    cases p with
    | inl l => exact hother l (fun k hk => hn (.inl k) (congrArg Sum.inl hk))
    | inr j => rfl

/-- Sequence two fragments with disjoint scratch spaces and common call-boundary ports. -/
def seq (a b : Fragment K) : Fragment K where
  Scratch := a.Scratch ⊕ b.Scratch
  body := (a.body.onPorts (Sum.map id Sum.inl)).followedBy (b.body.onPorts (Sum.map id Sum.inr))

/-- Calls can be linked without moving or copying their common registers. -/
theorem runs_seq (a b : Fragment K) {s u v : Stacks K} {t₁ t₂ : ℕ}
    (ha : a.Runs t₁ s u) (hb : b.Runs t₂ u v) : (seq a b).Runs (t₁+t₂) s v := by
  apply FiniteRoutine.Runs.followedBy (t := (seq a b).bank u)
  · apply a.body.runs_onPorts_framed (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inl_injective⟩) ha
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · intro i hn; cases i with | inl k => exact (hn (.inl k) rfl).elim | inr j => rfl
  · apply b.body.runs_onPorts_framed (Sum.map_injective.mpr ⟨Function.injective_id, Sum.inr_injective⟩) hb
    · intro i; cases i <;> rfl
    · intro i; cases i <;> rfl
    · intro i hn; cases i with | inl k => exact (hn (.inl k) rfl).elim | inr j => rfl

end Fragment

end CellMacro.Generator

end BorderVNP
end Computability
end OAI
