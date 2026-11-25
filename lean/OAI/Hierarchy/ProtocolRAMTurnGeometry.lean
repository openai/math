import OAI.Hierarchy.ProtocolRAMTurnChart
import OAI.Hierarchy.ProtocolRAMTurnOrder
import OAI.Hierarchy.ProtocolRAMCoreRouteOrder
import OAI.Hierarchy.TaggedWireRoleIndices

namespace OAI
/-! # The concrete chronological turn ROM is independent of all route choices -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnGeometry

open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix
open ProtocolRAM.Calendar CoreRoute
open scoped BigOperators Classical

variable {h d k edges : ℕ}

abbrev Source (edges h d k : ℕ) :=
  SettledMatrix.Source edges (Commodity (Fin (2^h)) (Stages h d) k) (Columns h d × Fin k)

def sourceOrder (edges h d k:ℕ) : Source edges h d k ≃ Fin (Fintype.card (Source edges h d k)) :=
  SettledMatrix.Layout.ordinal

def length : Source edges h d k → ℕ := Sum.elim (fun _=>1) (Sum.elim CoreRoute.arity (fun _=>2))

/-- The same two contiguous subdirectories that generate kind/edge words for actual
route settlement, after the permanent single-edge occurrences. -/
def origin (o : Orders h d k) : Source edges h d k → ℕ
  | .inl e => e.val
  | .inr (.inl i) => edges + ProtocolRAMTurnOrder.origin (CoreRoute.arity ∘ o.core.symm) (o.core i)
  | .inr (.inr c) => edges + (∑j,CoreRoute.arity (o.core.symm j))+2*(o.center c).val

def label (base : ℕ) : Source edges h d k → ℕ → ℕ
  | .inl _,_ => 0
  | .inr (.inl (.inl _)),_ => base
  | .inr (.inl (.inr (_,axis))),phase => base+(1+3*(2*axis.1.val+axis.2.toNat)+phase)
  | .inr (.inr (_,axis)),phase => base+(1+6*k+3*axis.val+phase)

def fixed : Source edges h d k → Bool := Sum.elim (fun _=>true) (fun _=>false)

def slots (o : Orders h d k) (base : ℕ) (s : Source edges h d k) (j : ℕ) :
    ProtocolRAMTurnChart.Geometry :=
  ⟨(sourceOrder edges h d k s).val,origin o s,length s,j,fixed s,label base s j⟩

/-- Permuting the public enumeration of the original source *items* changes no itinerary
by itself. Within each item all raw turn positions are consecutive in this literal ROM. -/
def header {n : ℕ} (o : Orders h d k) (base : ℕ) (items : Fin n ≃ Source edges h d k) :
    Fin (ProtocolRAMTurnOrder.turns (length ∘ items)) → ProtocolRAMTurnChart.Geometry :=
  fun i=>let p := ProtocolRAMTurnOrder.raw (length ∘ items) i
    slots o base (items p.1) p.2.val

theorem paid_at (o : Orders h d k) (e : Fin edges) : origin o (.inl e) = e.val := rfl

theorem goods_at (o : Orders h d k) (i : Commodity (Fin (2^h)) (Stages h d) k) (j : Fin (CoreRoute.arity i)) :
    origin (edges:=edges) o (.inr (.inl i))+j.val=edges+(CoreRoute.slotOrder o (.inl ⟨i,j⟩)).val := by
  rw [CoreRoute.slotOrder_core]
  change (edges+_)+j.val=edges+(_+j.val)
  exact Nat.add_assoc ..

theorem center_at (o : Orders h d k) (c : Columns h d × Fin k) (j : Fin 2) :
    origin (edges:=edges) o (.inr (.inr c))+j.val=edges+(CoreRoute.slotOrder o (.inr ⟨c,j⟩)).val := by
  change edges+(∑i,CoreRoute.arity (o.core.symm i))+2*(o.center c).val+j.val=_
  rw [CoreRoute.slotOrder_center]
  simp only [Nat.add_assoc]

theorem within {n : ℕ} (o : Orders h d k) (base : ℕ) (items : Fin n ≃ Source edges h d k)
    (i : Fin (ProtocolRAMTurnOrder.turns (length ∘ items))) :
    (header o base items i).raw ≤ (header o base items i).length :=
  Nat.le_of_lt_succ (ProtocolRAMTurnOrder.raw (length ∘ items) i).2.isLt

theorem length_ordinary {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {K : ℕ}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (i : Commodity (Fin (2^h)) (Stages h d) k) :
    (B.ordinary i).length=length (edges:=edges) (.inr (.inl i)) := by
  cases i with
  | inl p => simp [Mount.ordinary,commodityWalk,length,CoreRoute.arity,CoreRoute.payload_length]
  | inr x => rcases x with ⟨⟨p,t⟩,l⟩;rfl

theorem length_center {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {K : ℕ}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges) (c : Columns h d × Fin k) :
    (B.centers c).length=length (edges:=edges) (.inr (.inr c)) := by rcases c with ⟨_,_⟩;rfl

end Hierarchy.ProtocolRAMTurnGeometry

end
end OAI
