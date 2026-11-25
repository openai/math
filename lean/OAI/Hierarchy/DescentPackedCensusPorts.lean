import OAI.Hierarchy.DescentPackedHistoryMass
import OAI.Hierarchy.DescentMarkedCensusRows

namespace OAI
/-! # Local quantum ports and true packed census multiplicities -/

namespace Hierarchy.DescentSixParty.PackedCensus
open DescentColonies StarKeys
open scoped Classical BigOperators
noncomputable section

variable {F P V A : Type} [Field F] [Fintype V] [DecidableEq V]
  {d k : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (pos : W.graph.Site→V)
  (ix : W.graph.Site→Block k) (n : W.graph.Edge→ℕ)

abbrev AtEnd (endpt : W.graph.Edge→W.graph.Site) (v : V) (x : Block k) :=
  {e : W.graph.Edge // pos (endpt e)=v ∧ ix (endpt e)=x}

abbrev Ends (endpt : W.graph.Edge→W.graph.Site) (v : V) (x : Block k) :=
  Σ e : AtEnd W pos ix endpt v x, Fin (n e.val)

abbrev Ports (v : V) (x : Block k) :=
  Ends W pos ix n W.graph.src v x ⊕ Ends W pos ix n W.graph.dst v x

abbrev Out (v : V) (x : Block k) :=
  {e : W.graph.Edge // (pos (W.graph.src e)=v ∧ ix (W.graph.src e)=x) ∧ e∈W.core}

def portOfOut (positive : ∀e∈W.core,0<n e) (v : V) (x : Block k) :
    Out W pos ix v x ↪ Ports W pos ix n v x where
  toFun e := .inl ⟨⟨e.1,e.2.1⟩,⟨0,positive e.1 e.2.2⟩⟩
  inj' := by intro i j h; exact Subtype.ext (congrArg (fun t : Ends W pos ix n W.graph.src v x=>t.1.val) (Sum.inl.inj h))

omit [Field F] [Fintype V] in
theorem ends_eq (endpt : W.graph.Edge→W.graph.Site) (v : V) (x : Block k) :
    Fintype.card (Ends W pos ix n endpt v x)=
      ∑e,if pos (endpt e)=v ∧ ix (endpt e)=x then n e else 0 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  rw [←Finset.sum_filter]
  exact (Finset.sum_subtype (Finset.univ.filter fun e=>pos (endpt e)=v ∧ ix (endpt e)=x)
    (by simp) n).symm

omit [Field F] in
theorem out_eq (v : V) (x : Block k) :
    Fintype.card (Out W pos ix v x)=
      blockMass W.graph pos ix (fun u=>(W.core.filter (fun e=>W.graph.src e=u)).card) v x := by
  let edges := (Fintype.equivFin W.graph.Edge).symm
  let idx := Fintype.equivFin V
  rw [←MarkedCensus.outgoing W pos ix idx edges v x]
  unfold DescentCensusRAM.sumAt
  simp only [MarkedCensus.address_eq,Function.comp_apply]
  refine Eq.trans ?_ (edges.sum_comp (fun e=>
    if pos (W.graph.src e)=v ∧ ix (W.graph.src e)=x then MarkedCensus.marked W e else 0)).symm
  rw [Fintype.card_subtype]
  simp only [Finset.card_filter]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : pos (W.graph.src e)=v ∧ ix (W.graph.src e)=x <;>
    simp [h,MarkedCensus.marked]

omit [Field F] [Fintype V] in
private theorem end_load (endpt : W.graph.Edge→W.graph.Site) (hub : V→Bool)
    (wire β grain : ℕ) (fit : ∀e,W.graph.width e=n e*grain) (v : V) (x : Block k) :
    blockMass W.graph pos ix (fun u=>∑e,if u=endpt e then
      wire*W.graph.width e*(if hub (pos (endpt e)) then β else 1) else 0) v x =
      (wire*grain*(if hub v then β else 1))*Fintype.card (Ends W pos ix n endpt v x) := by
  rw [MarkedCensus.edge_bin,ends_eq,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  by_cases h : pos (endpt e)=v ∧ ix (endpt e)=x <;> simp [h,fit]; ring_nf

omit [Field F] [Fintype V] in
theorem units (hub : V→Bool) (atoms : W.graph.Site→List A) (wire β hist grain : ℕ)
    (fit : ∀e,W.graph.width e=n e*grain) (v : V) (x : Block k) :
    blockMass W.graph pos ix (W.siteUnits (hub ∘ pos) atoms wire β hist) v x =
      (wire*grain*(if hub v then β else 1))*Fintype.card (Ports W pos ix n v x) +
      hist*histories W pos ix atoms v x := by
  let term := fun (endpt : W.graph.Edge→W.graph.Site) u=>∑e, if u=endpt e then
    wire*W.graph.width e*(if hub (pos (endpt e)) then β else 1) else 0
  have split :
      blockMass W.graph pos ix (W.siteUnits (hub ∘ pos) atoms wire β hist) v x =
        blockMass W.graph pos ix (term W.graph.src) v x +
        blockMass W.graph pos ix (term W.graph.dst) v x + hist*histories W pos ix atoms v x := by
    simp only [histories,blockMass,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro u _
    by_cases h : pos u=v ∧ ix u=x <;> simp [h,term,MarkedWorld.siteUnits]
  rw [split,end_load W pos ix n W.graph.src hub wire β grain fit,
    end_load W pos ix n W.graph.dst hub wire β grain fit,Fintype.card_sum,Nat.mul_add]

omit [Field F] [Fintype V] in
theorem ports_fit (hub : V→Bool) (atoms : W.graph.Site→List A) (wire hist grain cap : ℕ)
    (pay : 0<wire*grain) (fit : ∀e,W.graph.width e=n e*grain) (v : V) (x : Block k)
    (small : blockMass W.graph pos ix (W.siteUnits (hub ∘ pos) atoms wire 256 hist) v x ≤
      wire*grain*cap) : Fintype.card (Ports W pos ix n v x)≤cap := by
  rw [units W pos ix n hub atoms wire 256 hist grain fit] at small
  let c := Fintype.card (Ports W pos ix n v x)
  have factor : wire*grain≤wire*grain*(if hub v then 256 else 1) := by cases hub v <;> simp; omega
  exact Nat.le_of_mul_le_mul_left ((Nat.mul_le_mul_right c factor).trans (Nat.le_trans (Nat.le_add_right _ _) small)) pay

end
end Hierarchy.DescentSixParty.PackedCensus

end OAI
