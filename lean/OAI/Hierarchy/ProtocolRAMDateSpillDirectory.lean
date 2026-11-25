import OAI.Hierarchy.ProtocolRAMCoreRouteOrder
import OAI.Hierarchy.ProtocolRAMRouteSettlement

namespace OAI
/-! # Reading the core prefix of the physical route directory -/

noncomputable section
namespace Hierarchy.ProtocolRAMDateSpillRank
open ProtocolRAM ProtocolRAM.Calendar ProtocolRAM.Calendar.CoreRoute AdaptiveProbe ProbeStage CoreBoard
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators Fin.CommRing

variable {h d k K edges w : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
  {place : Site h d k→Fin K} (B : Mount (S:=S) π place edges)

local notation "Goods" => Commodity (Fin (2^h)) (Stages h d) k
local notation "Centers" => Columns h d × Fin k

abbrev coreCount (o : Orders h d k) := ∑j,arity (o.core.symm j)

private def coreOccurrence : (Σ i : Goods,Fin (arity i)) ≃ (Σ i : Goods,Fin (B.ordinary i).length) :=
  Equiv.sigmaCongrRight (fun i=>finCongr (by
    cases i with
    | inl p => simp [arity,Mount.ordinary,commodityWalk,payload_length]
    | inr q => rcases q with ⟨⟨p,t⟩,l⟩;rfl))

private def noCenters (core : Goods→List (Fin edges)) :
    (Σ i : Goods,Fin (core i).length) ≃ RouteOccurrence core (Empty.elim : Empty→List (Fin edges)) where
  toFun:=Sum.inl
  invFun
    | .inl p=>p
    | .inr p=>p.1.elim
  left_inv:=fun _=>rfl
  right_inv
    | .inl _=>rfl
    | .inr p=>p.1.elim

/-- The order enumerates exactly those commodity visits whose directory
entries precede every catalyst-center visit. -/
def spillEnum (o : Orders h d k) : Fin (coreCount o) ≃ RouteOccurrence B.ordinary
    (Empty.elim : Empty→List (Fin edges)) :=
  (corePrefix o).symm.trans ((coreOccurrence B).trans (noCenters B.ordinary))

def fullIndex (o : Orders h d k) (i : Fin (coreCount o)) : Fin (Fintype.card (Slots h d k)) :=
  slotOrder o (.inl ((corePrefix o).symm i))

@[simp] theorem fullIndex_val (o : Orders h d k) (i : Fin (coreCount o)) : (fullIndex o i).val=i.val := by
  change (slotOrder o (.inl ((corePrefix o).symm i))).val=i.val
  exact (corePrefix_val o ((corePrefix o).symm i)).trans
    (congrArg Fin.val ((corePrefix o).apply_symm_apply i))

private theorem fullOccurrence (o : Orders h d k) (i : Fin (coreCount o)) :
    CoreRoute.enum B o (fullIndex o i)=.inl (coreOccurrence B ((corePrefix o).symm i)) := by
  change toOccurrence B ((slotOrder o).symm (slotOrder o (.inl ((corePrefix o).symm i))))=_
  rw [Equiv.symm_apply_apply]; rfl

theorem spillEnum_edge (o : Orders h d k) (i : Fin (coreCount o)) :
    (CoreRoute.enum B o (fullIndex o i)).edge=(spillEnum B o i).edge := by
  rw [fullOccurrence]; rfl

theorem spillEnum_kind (o : Orders h d k) (i : Fin (coreCount o)) :
    RouteSettlement.oddKind (CoreRoute.enum B o (fullIndex o i))=RouteSettlement.oddKind (spillEnum B o i) := by
  rw [fullOccurrence]; rfl

theorem spillEnum_resource (o : Orders h d k) (ci : Goods→ℕ) (cj : Centers→ℕ) (i : Fin (coreCount o)) :
    RouteSettlement.resource ci cj (CoreRoute.enum B o (fullIndex o i))=
      RouteSettlement.resource ci Empty.elim (spillEnum B o i) := by
  rw [fullOccurrence]; rfl

/-- The earlier spill amount comes from its own stock bank using the literal
even and odd directory words of the terminal's original commodity prefix. -/
theorem restrictDirectory (o : Orders h d k) (b : RouteSettlement.Banks) (spill : Bank) (m : Memory w)
    (ci : Goods→ℕ) (cj : Centers→ℕ) (full : RouteSettlement.Directory b m (CoreRoute.enum B o) ci cj) :
    RouteSettlement.Directory {b with stock:=spill} m (spillEnum B o) ci Empty.elim := by
  constructor
  · intro i; simpa only [fullIndex_val] using full.headKind (fullIndex o i)
  · intro i; simpa only [fullIndex_val,spillEnum_edge B o i] using full.headIndex (fullIndex o i)
  · intro i; simpa only [fullIndex_val,spillEnum_kind B o i] using full.tailKind (fullIndex o i)
  · intro i; simpa only [fullIndex_val,spillEnum_resource B o ci cj i] using full.tailIndex (fullIndex o i)

end Hierarchy.ProtocolRAMDateSpillRank
end

end OAI
