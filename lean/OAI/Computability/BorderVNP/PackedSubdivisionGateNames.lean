import OAI.Computability.BorderVNP.PackedSubdivisionGateRows
import OAI.Computability.BorderVNP.PackedSubdivisionIncoming
import OAI.Computability.BorderVNP.PackedSubdivisionRelayCounts
import OAI.Computability.BorderVNP.ShortenPublicSubdivisionRows

/-! # Public endpoint selectors of the subdivision writer

Each raw cable slot has a stripe of reserved hop IDs. Occupancy of the
last reserved hop distinguishes a full-length route from a direct cable.
At an original loop the old table reads the source hop. At a new equality
site the predecessor and successor use their destination and source views.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open Crossing Cover Shortening Shortening.PublicCapacity CellAddressCircuit PackedHistoryCircuit.RouteRows
open scoped Classical
open private src_at_old from OAI.Computability.BorderVNP.PackedSubdivisionIncoming
open private from_relay apart from OAI.Computability.BorderVNP.PackedSubdivisionRelayCounts

variable {D np extra : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits} {s : Shape}
    (old : Rows s N) (routes : N.WireRoutes) (fit : ∀ e, routes.interior e ≤ extra)
local notation "G" => N.subdivide routes

private theorem hop_name (e : N.Edge) (k : Fin (routes.interior e+1)) :
    (old.subdivide routes extra fit).edge ⟨e,k⟩ = hop (old.edge e) (k.castLE (Nat.succ_le_succ (fit e))) := Fin.ext rfl

/-- Precisely the first through last actual hops are occupied, including hop zero
of a frozen cable. A hole in the old directory has an entirely empty stripe. -/
theorem hop_live_iff (u : Fin s.edges) (k : Fin (extra+1)) :
    hop u k ∈ Set.range (old.subdivide routes extra fit).edge ↔ ∃ e : N.Edge, old.edge e = u ∧ k.val ≤ routes.interior e := by
  constructor
  · rintro ⟨⟨e,j⟩,h⟩
    have eq := (edgeIndex _ _).injective ((hop_name old routes fit e j).symm.trans h)
    have hj : j.val = k.val := congrArg (fun t => t.2.val) eq
    exact ⟨e,congrArg Prod.fst eq,hj ▸ Nat.le_of_lt_succ j.isLt⟩
  · rintro ⟨e,rfl,hle⟩
    let j : Fin (routes.interior e+1) := ⟨k.val,Nat.lt_succ_of_le hle⟩
    exact ⟨⟨e,j⟩,(hop_name old routes fit e j).trans (congrArg (hop (old.edge e)) (Fin.ext rfl))⟩

/-- The gate for a relay checks its successor cable's occupancy. -/
theorem relay_live_iff (u : Fin s.edges) (j : Fin extra) :
    hop u j.succ ∈ Set.range (old.subdivide routes extra fit).edge ↔ ∃ e : N.Edge, old.edge e = u ∧ j.val < routes.interior e := by
  exact hop_live_iff old routes fit u j.succ

/-- On a real cable, the public final-hop bit measures whether the entire stripe is occupied. -/
theorem last_live_iff (e : N.Edge) :
    hop (old.edge e) (Fin.last extra) ∈ Set.range (old.subdivide routes extra fit).edge ↔ routes.interior e = extra := by
  rw [hop_live_iff]
  constructor
  · rintro ⟨a,he,hle⟩
    obtain rfl := old.edge.injective he
    exact Nat.le_antisymm (fit a) hle
  · intro h
    exact ⟨e,rfl,h.ge⟩

/-- The geodesic subdivision's number of inserted sites is either zero or the
entire public stripe width, including the case of a zero-width stripe. -/
theorem siteRoutes_length {K I : Type*} [Fintype I] {d : ℕ} {L : ℝ} {p : Pack D P bits K}
    (r : SiteRoutes p I d L) (h : ℝ) (e : p.layout.Edge) :
    (r.routes h).interior e = 0 ∨ (r.routes h).interior e = ⌈L/h⌉₊ := by
  by_cases ha : r.active e = true <;> simp [SiteRoutes.routes,ha]

/-- The retained cable row selects the very same end used by the intrinsic
canonical incidence view. This also covers an inactive cable with no interior sites. -/
theorem old_target_eq (v : N.Site) (e : Incident N v) (long : Bool)
    (shape : routes.interior e.val = 0 ∨ routes.interior e.val = extra)
    (present : long = true ↔ hop (old.edge e.val) (Fin.last extra) ∈ Set.range (old.subdivide routes extra fit).edge) :
    oldTarget (np := np) (.inl (old.edge e.val,decide (N.src e.val = v))) long =
      Layer.edgeEnd ((old.subdivide routes extra fit).edge (endpoint N routes v e).val)
        (decide ((G).src (endpoint N routes v e).val = .inl v)) := by
  have length : routes.interior e.val = if long then extra else 0 := by
    have both := present.trans (last_live_iff old routes fit e.val)
    cases long with
    | false => exact shape.resolve_right (fun h => Bool.false_ne_true (both.mpr h))
    | true => exact both.mp rfl
  by_cases hs : N.src e.val = v
  · have hnew : (G).src (endpoint N routes v e).val = .inl v := by simp [endpoint,hs,Network.subdivide]
    rw [decide_eq_true hnew,decide_eq_true hs]
    simp only [hs,oldTarget,ite_true,endpoint,dite_true]
    exact congrArg (fun r => Layer.edgeEnd (n := np) r true) (hop_name old routes fit e.val 0).symm
  · have hnew : (G).src (endpoint N routes v e).val ≠ .inl v := by
      rw [endpoint,dite_eq_right hs]
      intro h
      exact hs ((src_at_old N routes v _ _).mp h).2
    rw [decide_eq_false hnew,decide_eq_false hs]
    simp only [hs,oldTarget,ite_false,Bool.false_eq_true,endpoint,dite_false]
    rw [hop_name]
    apply congrArg (fun r => Layer.edgeEnd r false)
    apply congrArg (hop (old.edge e.val))
    apply Fin.ext
    cases long <;> exact length.symm

/-- Exterior arguments preserve their public names on the old and new sites. -/
theorem old_target_port (portID : P ↪ Fin np) (v : N.Site) (p : Attached N v) (long : Bool) :
    oldTarget (m := s.edges) (extra := extra) (.inr (portID p.val)) long =
      .inr (portID (attached N routes v p).val) := rfl

variable (j : (e : N.Edge) × Fin (routes.interior e))

/-- The relay's first word comes from the destination view of the predecessor hop. -/
theorem relay_left_eq :
    relayLeft (np := np) (old.edge j.1) (j.2.castLE (fit j.1)) =
      Layer.edgeEnd ((old.subdivide routes extra fit).edge (leftHop N routes j).val) (decide ((G).src (leftHop N routes j).val = .inr j)) := by
  have h : (G).src (leftHop N routes j).val ≠ .inr j := by
    intro he
    exact apart N routes j (Subtype.ext (from_relay N routes j _ _ he))
  rw [decide_eq_false h]
  exact congrArg (fun i => Layer.edgeEnd i false) (hop_name old routes fit j.1 j.2.castSucc).symm

/-- The relay's second word comes from the source view of the successor hop. -/
theorem relay_right_eq :
    relayRight (np := np) (old.edge j.1) (j.2.castLE (fit j.1)) =
      Layer.edgeEnd ((old.subdivide routes extra fit).edge (rightHop N routes j).val) (decide ((G).src (rightHop N routes j).val = .inr j)) := by
  have h : (G).src (rightHop N routes j).val = .inr j := by simp [rightHop,Network.subdivide]
  rw [decide_eq_true h]
  exact congrArg (fun i => Layer.edgeEnd i true) (hop_name old routes fit j.1 j.2.succ).symm

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
