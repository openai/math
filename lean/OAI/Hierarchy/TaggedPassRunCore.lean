import OAI.Hierarchy.TaggedPassFormat
import OAI.Hierarchy.TaggedRadixStages

namespace OAI
/-! # Exact staged records and native stage costs of a radix pass sequence -/
noncomputable section
namespace Hierarchy.Tagged.Radix
open Catalyst CatalystSubstitution RadixStage ThreeFlat Routing
open scoped Classical BigOperators
variable {F : Type*} [Field F] {k h n : ℕ} {format : ℕ → PassFormat}

/-- Data supplied by the exact radix wiring: its consecutive arrays, open
three-gate shells, and scan of the final ordered records. -/
structure StageRun (h n : ℕ) {format : ℕ → PassFormat} (Y : ∀ i,(format i).Calls F k) where
  state : ℕ → Type
  holes : ℕ → Type
  [stateFinite : ∀ i,Fintype (state i)]
  [holesFinite : ∀ i,Fintype (holes i)]
  stage : ∀ i, Network F (state i) (state (i+1)) (holes i)
  sockets : ∀ i, holes i ≃ Sockets (Y i).occurrences
  run : ∀ i, (state i → Bool) → (state (i+1) → Bool)
  reachable : ∀ i, (state i → Bool) → Prop
  computes : ∀ i, i≤n → ComputesOn (stage i)
    (fun a => exactWeight (Y i).occurrences (a ∘ (sockets i).symm)) (reachable i) (run i)
  keep : ∀ i, i≤n → ∀ x,reachable i x → reachable (i+1) (run i x)
  scan : BitNetwork F (Fintype.card (state (n+1)))
  feed : state 0 → Fin (pins h h) ⊕ Bool
  start : ∀ x, reachable 0 (Sum.elim x id ∘ feed)
  finish : ∀ x,TypedWiring.value scan (advance state run n (Sum.elim x id ∘ feed)) = coeff F h h x

attribute [instance] StageRun.stateFinite StageRun.holesFinite

structure StageRun.Room {Y : ∀ i,(format i).Calls F k} (R : StageRun h n Y) (c : ℕ) : Prop where
  pass : ∀ i,i≤n → (R.stage i).cells+(R.stage i).internal+Fintype.card (R.state (i+1)) ≤ c*(2^h*h)
  scan : R.scan.cells+R.scan.internal+pins h h ≤ c*(2^h*h)

end Hierarchy.Tagged.Radix

end
end OAI
