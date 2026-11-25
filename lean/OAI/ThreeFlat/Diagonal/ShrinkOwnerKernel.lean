import OAI.ThreeFlat.Diagonal.ShrinkDemands
import OAI.ThreeFlat.Diagonal.CompressorOwnerRows
import OAI.ThreeFlat.Diagonal.ShrinkLayout
import OAI.ThreeFlat.Diagonal.HistoryContraction

namespace OAI
/-! # Reading shrinking demand words from the old half-indices at one owner -/

namespace ThreeFlat.Diagonal.CompressorPacking

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction
open scoped Classical BigOperators
noncomputable section

variable {c d Q : ℕ} {V H Tag L : Type}
variable [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable (P : PackingData V H Tag L d c)

def oldGraph : PortGraph (Position V H Tag L c) (Arc V H Tag L d c) :=
  ⟨sourcePosition, fun e => sourcePosition (P.actual e)⟩

variable (w : Arc V H Tag L d c → ℕ)

def oldShape : Shape where
  Site := Position V H Tag L c
  Edge := Arc V H Tag L d c
  graph := oldGraph P
  Label e := Fin (2^w e)

/-- The original word at one half-edge. -/
def oldEnds (a : ∀ i, (oldShape P w).Half i) (side : Bool) : OldWords w :=
  fun e => a ((oldGraph P).vertex e side) ⟨(e,side),rfl⟩

/-- The half-index row seen by a kernel at one new site. -/
abbrev OwnedRow (layout : Bool) (v : Site V Tag L) :=
  ∀ i : {i // P.placement layout i = v}, (oldShape P w).Half i.val

/-- Lift just the requested old word from the owner's half-index row. The dummy
zero outside the fiber gives a total accessor and never changes the demand value. -/
def ownedWords (layout : Bool) (v : Site V Tag L) (a : OwnedRow P w layout v) (side : Bool) : OldWords w :=
  fun e => if h : P.placement layout ((oldGraph P).vertex e side) = v then
    a ⟨(oldGraph P).vertex e side,h⟩ ⟨(e,side),rfl⟩ else 0

def partySite (layout : Bool) (m : P.Motif) (j : Fin 6) : Site V Tag L :=
  (![P.roleA m,P.roleB m,P.roleD layout m] : Fin 3 → _) (ShrinkMotif.role layout j)

def demandGraph : PortGraph (Fin 6) (Fin 2) := ⟨ShrinkMotif.demandSrc,ShrinkMotif.demandDst⟩

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
theorem party_demandSite (layout : Bool) (m : P.Motif) (side : Bool) (e : Fin 2) :
    partySite P layout m (demandGraph.vertex e side) = demandSite P layout m side e := by
  cases layout <;> cases side <;> fin_cases e <;>
    simp [partySite,demandSite,demandGraph,PortGraph.vertex,ShrinkMotif.demandSrc,ShrinkMotif.demandDst,
      ShrinkMotif.role]

variable (code : Arc V H Tag L d c ↪ ℕ) (hQ : 0 < Q) (num : P.Motif ≃ (Site V Tag L × Fin d) × Fin Q)

/-- A fully local physical demand half-index: it reads the row of the actual
owner of this party, in the format expected by a history rewrite kernel. -/
def localPartyState (layout : Bool) (m : P.Motif) (j : Fin 6) (a : OwnedRow P w layout (partySite P layout m j)) :
    demandGraph.State (fun e => Fin (2^demandWidth P w num m e)) j :=
  fun p => demandEnd P code w hQ num m
    (ownedWords P w layout _ a false) (ownedWords P w layout _ a true) p.1.2 p.1.1

/-- Restricting a full old assignment to the owner gives the exact same demand
entry. This holds individually for every port, including each orientation of CD. -/
theorem localPartyState_full (bundled : ∀ m, (num m).1 = P.bundle m) (layout : Bool) (m : P.Motif)
    (j : Fin 6) (a : ∀ i, (oldShape P w).Half i) :
    localPartyState P w code hQ num layout m j (fun i => a i.val) =
      fun p : demandGraph.Port j => demandEnd P code w hQ num m (oldEnds P w a false) (oldEnds P w a true) p.1.2 p.1.1 := by
  funext p
  have hv : partySite P layout m j = demandSite P layout m p.1.2 p.1.1 :=
    (congrArg (partySite P layout m) p.property.symm).trans (party_demandSite P layout m _ _)
  apply demandEnd_local P code w hQ num bundled layout m
  · intro e he
    have hp : P.placement layout ((oldGraph P).vertex e false) = partySite P layout m j :=
      he.trans hv.symm
    exact dite_eq_left hp
  · intro e he
    have hp : P.placement layout ((oldGraph P).vertex e true) = partySite P layout m j :=
      he.trans hv.symm
    exact dite_eq_left hp

/-- Equality of the physical old graph wiring and all six-party demand wirings,
with party inputs formed exclusively from the old half-indices at their owners. -/
theorem local_demands_wiring {K : Type*} [CommSemiring K] (bundled : ∀ m, (num m).1 = P.bundle m)
    (layout : Bool) (a : ∀ i, (oldShape P w).Half i) :
    (oldShape P w).graph.wiring (oldShape P w).Label a =
      ∏ m : P.Motif, demandGraph.wiring (K := K) (fun e => Fin (2^demandWidth P w num m e))
        (fun j => localPartyState P w code hQ num layout m j (fun i => a i.val)) := by
  simp_rw [localPartyState_full P w code hQ num bundled]
  rw [← shrink_demands_wiring P code w demandGraph hQ num]
  simp only [PortGraph.wiring,funext_iff,oldEnds]
  split_ifs <;> first | rfl | contradiction

/-- The uniform child index enumerates the dependent rows passed into the
same kernel. No search through the entire old set of sites is needed. -/
def numberedRow (layout : Bool) (v : Site V Tag L)
    (a : ∀ i : {i // Owner.valid P layout v i}, (oldShape P w).Half (Owner.child P layout v i.val)) :
    OwnedRow P w layout v := fun i => by
  let e := Owner.children P layout v
  let t := e.symm i
  have ht : Owner.child P layout v t.val = i.val := congrArg Subtype.val (e.apply_symm_apply i)
  exact ht ▸ a t

end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
