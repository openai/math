import OAI.Computability.BorderVNP.ParseFanout
import Mathlib.Logic.Equiv.Sum

/-! # Degree and volume of the equality-chain network

Each argument of a factor contributes one junction and one leaf wire. The
description covers variables with zero uses and counts both ends of a cable.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace ParseBatch.Layout

open scoped Classical

variable {X W T : Type} [Fintype X] [Fintype W] [Fintype T]

/-- Enumerate occurrences of each variable from a factor's explicit argument list. -/
noncomputable def ofArguments (arity : T → ℕ) (arg : (t : T) → Fin (arity t) → X ⊕ W) :
    Layout X W T where
  arity := arity
  fanout u := Fintype.card {j : Σ t, Fin (arity t) // arg j.1 j.2 = u}
  slots := (Equiv.sigmaCongrRight (fun u => (Fintype.equivFin
    {j : Σ t, Fin (arity t) // arg j.1 j.2 = u}).symm)).trans
      (Equiv.sigmaFiberEquiv (fun j : Σ t, Fin (arity t) => arg j.1 j.2))

omit [Fintype X] [Fintype W] in
/-- Each slot in the enumeration refers to the originally supplied variable. -/
theorem ofArguments_wire (arity : T → ℕ) (arg : (t : T) → Fin (arity t) → X ⊕ W)
    (t : T) (i : Fin (arity t)) : ((ofArguments arity arg).slots.symm ⟨t,i⟩).1 = arg t i := rfl

variable (L : Layout X W T)

/-- An external pin or one of the two ends of an internal edge. -/
abbrev Endpoint := X ⊕ (L.Edge × Bool)

/-- Vertex incident to an endpoint; `true` denotes the destination. -/
noncomputable def incident : L.Endpoint → L.Site
  | .inl x => .inr (.inl (.inl x))
  | .inr (e,b) => if b then L.network.dst e else L.network.src e

/-- The candidate endpoints of a site, including the first and last link of each chain. -/
noncomputable def sitePorts : L.Site → Finset L.Endpoint
  | .inl t => Finset.univ.image (fun i : Fin (L.arity t) => .inr (.inr (L.slots.symm ⟨t,i⟩), true))
  | .inr (.inl (.inl x)) => {.inl x, .inr (.inl ⟨.inl x, 0⟩, false)}
  | .inr (.inl (.inr w)) => {.inr (.inl ⟨.inr w, 0⟩, false)}
  | .inr (.inr (.inl ⟨u,i⟩)) => {
      .inr (.inl ⟨u,i.castSucc⟩,true), .inr (.inl ⟨u,i.succ⟩,false), .inr (.inr ⟨u,i⟩,false)}
  | .inr (.inr (.inr u)) => {.inr (.inl ⟨u,Fin.last (L.fanout u)⟩,true)}

private theorem mem_sitePorts (e : L.Endpoint) : e ∈ L.sitePorts (L.incident e) := by
  rcases e with x | ⟨e,b⟩
  · simp [incident, sitePorts]
  rcases e with ⟨u,i⟩ | j
  · cases b
    · induction i using Fin.cases with
      | zero => cases u <;> simp [incident, sitePorts]
      | succ i => simp [incident, sitePorts]
    · induction i using Fin.lastCases with
      | last => simp [incident, sitePorts]
      | cast i => simp [incident, sitePorts]
  · cases b
    · obtain ⟨u,i⟩ := j
      simp [incident, sitePorts]
    · change Sum.inr (Sum.inr j, true) ∈ L.sitePorts (.inl (L.slots j).1)
      apply Finset.mem_image.mpr
      exact ⟨(L.slots j).2, Finset.mem_univ _, by rw [Sigma.eta, L.slots.symm_apply_apply]⟩

/-- Every vertex has degree at most three when every original factor has at most three slots. -/
theorem degree_le_three (harity : ∀ t, L.arity t ≤ 3) (v : L.Site) :
    (Finset.univ.filter (fun e : L.Endpoint => L.incident e = v)).card ≤ 3 := by
  classical
  apply (Finset.card_le_card (t := L.sitePorts v) _).trans
  · rcases v with t | (u | (j | u))
    · exact (Finset.card_image_le.trans (by simpa using harity t))
    · cases u with
      | inl x => exact Finset.card_insert_le .. |>.trans (by simp)
      | inr w => simp [sitePorts]
    · rcases j with ⟨u,i⟩
      apply (Finset.card_insert_le ..).trans
      apply Nat.succ_le_succ
      exact (Finset.card_insert_le ..).trans (by simp)
    · simp [sitePorts]
  · intro e he
    exact (Finset.mem_filter.mp he).2 ▸ L.mem_sitePorts e

/-- The number of vertices plus all internal wires and external ports grows linearly in the
numbers of factors, variables and argument occurrences. -/
theorem volume_eq :
    Fintype.card L.Site + Fintype.card L.Edge + Fintype.card X =
      Fintype.card T + 3 * Fintype.card L.Use + 3 * Fintype.card (X ⊕ W) + Fintype.card X := by
  simp only [Site, Edge, Use, Spine, Fintype.card_sum, Fintype.card_sigma, Fintype.card_fin,
    Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one]
  omega

/-- The number of uses is the sum of the original factor arities. -/
theorem uses_eq : Fintype.card L.Use = ∑ t, L.arity t := by
  simpa only [Fintype.card_sigma, Fintype.card_fin] using Fintype.card_congr L.slots

end ParseBatch.Layout

end BorderVNP
end Computability
end OAI
