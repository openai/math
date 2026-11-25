import OAI.Hierarchy.DescentHubCoalescence
import OAI.Hierarchy.DescentNetworkReindex

namespace OAI
/-! # Coalescing actual hub sites and restoring the common cable unit -/

namespace Hierarchy.DescentSixParty
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {P : Type} {bits : P→ℕ} {d : ℕ}

/-- Between measured stages, equal hub prefixes coalesce, marked cables split
into their existing width units, and sites and cables receive their physical
tape names. Each operation preserves evaluation and charges its actual widths. -/
inductive Normalize : MarkedWorld F d P bits → Type 1
  | done (W) : Normalize W
  | split (W) (q : ℕ) (m : W.graph.Edge→ℕ) (fit : ∀e∈W.core,W.graph.width e=m e*q)
      (next : Normalize (W.pieces q m fit)) : Normalize W
  | merge (W) (V : Type) [DecidableEq V] (key : W.graph.Site→DescentHostDirectory.Key V)
      (hub : V→Bool) (k g : ℕ) (next : Normalize (W.coalesced key hub k g)) : Normalize W
  | named (W) (site : Equiv.Perm W.graph.Site) (edge : Equiv.Perm W.graph.Edge)
      (next : Normalize (PhysicalRename.world W site edge)) : Normalize W

namespace Normalize
def result {W : MarkedWorld F d P bits} (n : Normalize W) : MarkedWorld F d P bits := by
  induction n with
  | done W => exact W
  | split _ _ _ _ _ ih => exact ih
  | merge _ _ _ _ _ _ _ ih => exact ih
  | named _ _ _ _ ih => exact ih

/-- The renaming is the final step of this same normalization trace. -/
def appendNames {W : MarkedWorld F d P bits} (n : Normalize W) :
    Equiv.Perm n.result.graph.Site → Equiv.Perm n.result.graph.Edge → Normalize W := by
  induction n with
  | done W => exact fun s e => .named W s e (.done _)
  | split W q m fit next ih => exact fun s e => .split W q m fit (ih s e)
  | merge W V key hub k g next ih => exact fun s e => .merge W V key hub k g (ih s e)
  | named W a b next ih => exact fun s e => .named W a b (ih s e)

@[simp] theorem appendNames_result {W : MarkedWorld F d P bits} (n : Normalize W)
    (s : Equiv.Perm n.result.graph.Site) (e : Equiv.Perm n.result.graph.Edge) :
    (n.appendNames s e).result=PhysicalRename.world n.result s e := by
  induction n with
  | done => rfl
  | split _ _ _ _ _ ih => exact ih s e
  | merge _ _ _ _ _ _ _ ih => exact ih s e
  | named _ _ _ _ ih => exact ih s e

theorem value {W : MarkedWorld F d P bits} (n : Normalize W) (x : Ports bits) :
    n.result.value x=W.value x := by
  induction n with
  | done => rfl
  | named W s e next ih => exact ih.trans (congrFun (PhysicalRename.value W s e) x)
  | split W q m fit next ih => exact ih.trans (W.pieces_value q m fit x)
  | merge W V key hub k g next ih => exact ih.trans (W.coalesced_value key hub k g x)

theorem bills {W : MarkedWorld F d P bits} (n : Normalize W) :
    n.result.liveWidth≤W.liveWidth ∧ n.result.tetherWidth≤W.tetherWidth := by
  induction n with
  | done => exact ⟨le_rfl,le_rfl⟩
  | named W s e next ih => exact ⟨ih.1.trans_eq (PhysicalRename.liveWidth W s e),ih.2.trans_eq (PhysicalRename.tetherWidth W s e)⟩
  | split W q m fit next ih =>
    exact ⟨ih.1.trans_eq (W.pieces_core q m fit),ih.2.trans_eq (W.pieces_tether q m fit)⟩
  | merge W V key hub k g next ih =>
    exact ⟨ih.1.trans (W.coalesced_core key hub k g),ih.2.trans (W.coalesced_tether key hub k g)⟩

end Normalize
end
end Hierarchy.DescentSixParty

end OAI
