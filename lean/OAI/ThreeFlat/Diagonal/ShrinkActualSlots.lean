import OAI.ThreeFlat.Diagonal.ShrinkGraph
import OAI.ThreeFlat.Diagonal.ShrinkLayout

namespace OAI
/-! # The slot of each physical supply word -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression
open scoped Classical BigOperators
noncomputable section

/-- Translate a party of the six-party tensor to its actual packed-site role. -/
def partyRole (layout : Bool) (v : Fin 6) : Role :=
  (![Role.a, Role.b, Role.d] : Fin 3 → Role) (ShrinkMotif.role layout v)

/-- The graph numbering uses exactly the two incidences of each surviving
supply edge under the six-party placement. -/
theorem actual_roles (layout : Bool) (i : Fin 4) :
    supplyRoles layout i =
      (partyRole layout (ShrinkMotif.supplySrc (ShrinkMotif.survivor layout i)),
       partyRole layout (ShrinkMotif.supplyDst (ShrinkMotif.survivor layout i))) := by
  cases layout <;> fin_cases i <;> rfl

variable {c d : ℕ} {V H Tag L : Type*} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)

abbrev PhysicalPiece (count : Fin 4 → ℕ) := Σ e : Fin 4, P.Motif × Fin (count e)

/-- Each parallel piece of an actual motif is a unique rooted cable and translation. -/
def pieceLanes (count : Fin 4 → ℕ) : ShrinkEdge P count × L ≃ PhysicalPiece P count where
  toFun x := ⟨x.1.1, allLanes P (x.1.2.1,x.2), x.1.2.2⟩
  invFun x := (⟨x.1, ((allLanes P).symm x.2.1).1, x.2.2⟩, ((allLanes P).symm x.2.1).2)
  left_inv := by rintro ⟨⟨e,m,i⟩,g⟩; simp
  right_inv := by rintro ⟨e,m,i⟩; simp

variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]

abbrev usedDegree (count : Fin 4 → ℕ) (c d : ℕ) := d*(3*(2^c*d)/4)*(∑ e, count e)

/-- Rooted cable numbering, anchored at the lane of the chosen endpoint. -/
def endpointSlots (layout : Bool) (role : Fin 4 → Role) (count : Fin 4 → ℕ)
    (order : ShrinkEdge P count ↪ ℕ) (hc : 2 ≤ c) :
    ShrinkEdge P count × L ≃ ((V × Tag) × Fin (usedDegree count c d)) × L := by
  letI : LinearOrder (ShrinkEdge P count) := LinearOrder.lift' _ order.injective
  let n := CompressorRegularize.numbering (fun e : ShrinkEdge P count => base (slotSite P layout role (count:=count) e))
    (incident_count P layout role count · hc)
  let lane := fun e : ShrinkEdge P count => (slotSite P layout role (count:=count) e).2.2
  exact {
    toFun := fun x => (n x.1, lane x.1 + x.2)
    invFun := fun y => (n.symm y.1, y.2 - lane (n.symm y.1))
    left_inv := by rintro ⟨e,g⟩; simp only [Equiv.symm_apply_apply,Prod.mk.injEq,true_and]; abel
    right_inv := by rintro ⟨p,g⟩; simp only [Equiv.apply_symm_apply,Prod.mk.injEq,true_and]; abel
  }

/-- Read the vertex and lane of a numbered slot. -/
def numberedSite {k : ℕ} (a : ((V × Tag) × Fin k) × L) : Site V Tag L :=
  (a.1.1.1,a.1.1.2,a.2)

/-- The slot assigned to an actual piece lies at its chosen motif role,
including the entire remaining lane address. -/
theorem endpoint_site (layout : Bool) (role : Fin 4 → Role) (count : Fin 4 → ℕ)
    (order : ShrinkEdge P count ↪ ℕ) (hc : 2 ≤ c) (x : PhysicalPiece P count) :
    numberedSite (endpointSlots P layout role count order hc ((pieceLanes P count).symm x)) =
      siteOf P layout (role x.1) x.2.1 := by
  obtain ⟨⟨⟨e,m,i⟩,g⟩,rfl⟩ := (pieceLanes P count).surjective x
  rw [Equiv.symm_apply_apply]
  change (_,_,_) = siteOf P layout (role e) (moveMotif P g m.val)
  rw [moves_of_role]
  rfl

set_option maxHeartbeats 800000 in
/-- The permutation of the actual graph sends each numbered outgoing occurrence
to the incoming slot of the very same old motif and parallel piece. -/
theorem endpoint_target (layout : Bool) (count : Fin 4 → ℕ) (order : ShrinkEdge P count ↪ ℕ)
    (hc : 2 ≤ c) (hn : ∀ a : Tag, -a = a) (good : TagConditions P.slots (shift P) P.offset)
    (x : PhysicalPiece P count) :
    (shrinkingGraph P layout count order hc hn good).actualTarget
        (endpointSlots P layout (fun t => (supplyRoles layout t).1) count order hc
          ((pieceLanes P count).symm x)) =
      endpointSlots P layout (fun t => (supplyRoles layout t).2) count order hc
        ((pieceLanes P count).symm x) := by
  obtain ⟨⟨e,g⟩,rfl⟩ := (pieceLanes P count).surjective x
  let : LinearOrder (ShrinkEdge P count) := LinearOrder.lift' _ order.injective
  let s := slotSite P layout (fun t => (supplyRoles layout t).1) (count := count)
  let t := slotSite P layout (fun t => (supplyRoles layout t).2) (count := count)
  have he := CompressorRegularize.edge_lift (base ∘ s) (base ∘ t)
    (fun e => (t e).2.2 - (s e).2.2)
    (incident_count P layout _ count · hc) (incident_count P layout _ count · hc)
    (ends_ne P hn good layout count) e ((s e).2.2 + g)
  rw [Equiv.symm_apply_apply]
  change (shrinkingGraph P layout count order hc hn good).actualTarget
    (CompressorRegularize.numbering (base ∘ s) (incident_count P layout _ count · hc) e,(s e).2.2+g) =
      (CompressorRegularize.numbering (base ∘ t) (incident_count P layout _ count · hc) e,(t e).2.2+g)
  rw [show (s e).2.2 + g + ((t e).2.2 - (s e).2.2) = (t e).2.2 + g by abel] at he
  exact he

/-- With the paper's four floor counts the actual rooted incidence degree always
fits in the new degree, so the padding needs no incidence-count hypothesis. -/
theorem graph_degree_fits (c d D : ℕ) (hc : 2 ≤ c) (hd : 0 < d) (hD : 0 < D) :
    usedDegree (SlotEnergy.slotCount ((2^c*d*d : ℕ)/D)) c d ≤ D := by
  apply SlotEnergy.slotCount_capacity (K := 2^c*d) (by positivity) hd hD
  have hk : 2^c = 2^(c-2)*2^2 := by rw [← Nat.pow_add]; congr 1; omega
  rw [hk, show 3*(2^(c-2)*2^2*d) = (3*2^(c-2)*d)*4 by ring,
    Nat.mul_div_cancel _ (by decide : 0 < 4)]
  ring

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
