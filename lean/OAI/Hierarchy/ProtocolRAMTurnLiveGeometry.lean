import OAI.Hierarchy.ProtocolRAMTurnMap
import OAI.Hierarchy.ProtocolRAMVisitLive

namespace OAI
/-! # Endpoint arithmetic for actual live chronological occurrences -/
noncomputable section
namespace Hierarchy.ProtocolRAMTurnMap
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ProbeStage CoreBoard WireTelescope
open ProtocolRAM.Calendar CoreRoute ProtocolRAM ProtocolRAMTurnChart ProtocolRAMTurnWalk
open scoped Fin.CommRing
variable {h d k edges K n W : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K) (o : Orders h d k)
    (items : Fin n ≃ ProtocolRAMTurnGeometry.Source edges h d k)
local notation "len" => ProtocolRAMTurnGeometry.length ∘ items
local notation "N" => ProtocolRAMTurnOrder.turns len
local notation "paid" => ProtocolRAMTurnOccurrence.edgeAt B inj pad o
local notation "ends" => ProtocolRAMTurnOccurrence.endsAt B inj pad
local notation "routeSite" => ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (items a))
local notation "Count" => Fintype.card (Slots h d k)
local notation "raw" => ProtocolRAMTurnOrder.raw len

theorem live_closed (weight : Fin n → ℕ) (i : Fin N) (pos : 0<(raw i).2.val)
    (on : 0<weight (raw i).1) : 0<weight (raw ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩).1 := by
  rw [ProtocolRAMTurnOrder.previous_eq len i pos]
  exact on

/-- Only incident endpoint pairs along positive old items are read. The program
still traverses all row positions, so its clock and unmodified catalogue order apply. -/
theorem live_endpoint_on (base bits offset : ℕ) (data : Data) (keys tails heads : Bank)
    (m : Memory W) (weight : Fin n→ℕ)
    (rom : Loaded base bits (ProtocolRAMTurnGeometry.header o offset items) m)
    (small : ∀a,len a<2^W)
    (start : ∀a,0<weight a → data.rawSource.read m ((ProtocolRAMTurnGeometry.sourceOrder edges h d k (items a)).val:Word W)=
      (ProtocolRAMTurnEdges.visit B inj pad (items a) 0:Word W))
    (key : ∀a,0<weight a→∀j<len a,
      let q:=ProtocolRAMTurnGeometry.origin o (items a)+j
      keys.read m (q:Word W)=(paid q:Word W))
    (endpoints : ∀a,0<weight a → ∀ j<len a,
      let e := paid (ProtocolRAMTurnGeometry.origin o (items a)+j)
      tails.read m (e:Word W)=((ends e).1:Word W) ∧ heads.read m (e:Word W)=((ends e).2:Word W))
    (i : Fin N) (active : 0<weight (raw i).1) :
    let u := ProtocolRAMTurnGeometry.header o offset items
    let pos := fun j : Fin N=>(u j).raw
    let prior := ProtocolRAMVisitColumns.previous? pos (fun j hj=>ProtocolRAMTurnOrder.has_previous len j hj) i
    (ProtocolRAMVisitColumns.total (walk base bits data keys tails heads)).eval m (i.val:Word W)=
      (routeSite i:Word W)+carried (fun j=>(routeSite j:Word W)) i prior := by
  intro u pos prior
  have rp : (get base bits 3).eval m (i.val:Word W)=((u i).raw:Word W) := rom 3 i
  have it : (get base bits 0).eval m (i.val:Word W)=((u i).item:Word W) := rom 0 i
  have org : (get base bits 1).eval m (i.val:Word W)=((u i).origin:Word W) := rom 1 i
  have positionFits : (u i).raw<2^W := (ProtocolRAMTurnGeometry.within o offset items i).trans_lt (small (raw i).1)
  by_cases hz : (u i).raw=0
  · have startAddress : data.rawSource.read m ((u i).item:Word W)=(routeSite i:Word W) := by
      have pz : (raw i).2.val=0 := hz
      change data.rawSource.read m
          ((ProtocolRAMTurnGeometry.sourceOrder edges h d k (items (raw i).1)).val : Word W) =
        (ProtocolRAMTurnEdges.visit B inj pad (items (raw i).1) (raw i).2.val : Word W)
      rw [pz]
      exact start (raw i).1 active
    simp [ProtocolRAMVisitColumns.total,walk,Expr.eval,Comparison.test,rp,hz,it,startAddress,
      prior,pos,ProtocolRAMVisitColumns.previous?,carried]
  · have hp := Nat.pos_of_ne_zero hz
    have offsetLt : (u i).raw-1<len (raw i).1 := by
      have bound : (u i).raw≤len (raw i).1 := ProtocolRAMTurnGeometry.within o offset items i
      omega
    let q := (u i).origin+((u i).raw-1)
    have paidRead : keys.read m (q:Word W)=(paid q:Word W) := key (raw i).1 active _ offsetLt
    have endsRead : tails.read m (paid q:Word W)=((ends (paid q)).1:Word W) ∧
        heads.read m (paid q:Word W)=((ends (paid q)).2:Word W) := endpoints (raw i).1 active _ offsetLt
    have edgeRead : (ProtocolRAMVisitColumns.edge (walk base bits data keys tails heads)).eval m (i.val:Word W)=(paid q:Word W) := by
      change keys.read m ((get base bits 1).eval m (i.val:Word W)+((get base bits 3).eval m (i.val:Word W)-1))=_
      rw [org,rp]
      simpa only [q,Nat.cast_add,Nat.cast_sub (by omega : 1≤(u i).raw),Nat.cast_one] using paidRead
    have wordNZ : ((u i).raw:Word W)≠0 := by
      intro same
      exact hz (by simpa only [Fin.val_cast_of_lt positionFits,Fin.val_zero] using congrArg Fin.val same)
    have hd := ProtocolRAMTurnOccurrence.adjacent B inj pad o items i hp
    change (ends (paid q)).1+(ends (paid q)).2=routeSite i+routeSite ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩ at hd
    simp only [ProtocolRAMVisitColumns.total,walk,Expr.eval,Comparison.test,rp,Nat.cast_zero,beq_iff_eq,
      ite_eq_right wordNZ,RowOp.opcode,BinaryOp.eval,prior,pos,
      ProtocolRAMVisitColumns.previous?,dite_eq_left hp,carried,previous]
    change tails.read m ((ProtocolRAMVisitColumns.edge (walk base bits data keys tails heads)).eval m (i.val : Word W)) +
        heads.read m ((ProtocolRAMVisitColumns.edge (walk base bits data keys tails heads)).eval m (i.val : Word W)) = _
    rw [edgeRead, endsRead.1, endsRead.2]
    simpa only [Nat.cast_add] using congrArg (fun z : ℕ => (z:Word W)) hd

theorem live_endpoint (base bits offset : ℕ) (data : Data) (keys tails heads : Bank)
    (m : Memory W) (weight : Fin n→ℕ)
    (rom : Loaded base bits (ProtocolRAMTurnGeometry.header o offset items) m)
    (small : ∀a,len a<2^W)
    (start : ∀a,0<weight a → data.rawSource.read m ((ProtocolRAMTurnGeometry.sourceOrder edges h d k (items a)).val:Word W)=
      (ProtocolRAMTurnEdges.visit B inj pad (items a) 0:Word W))
    (key : ∀t<edges+Count,keys.read m (t:Word W)=(paid t:Word W))
    (endpoints : ∀a,0<weight a → ∀ j<len a,
      let e := paid (ProtocolRAMTurnGeometry.origin o (items a)+j)
      tails.read m (e:Word W)=((ends e).1:Word W) ∧ heads.read m (e:Word W)=((ends e).2:Word W))
    (i : Fin N) (active : 0<weight (raw i).1) :
    let u := ProtocolRAMTurnGeometry.header o offset items
    let pos := fun j : Fin N=>(u j).raw
    let prior := ProtocolRAMVisitColumns.previous? pos (fun j hj=>ProtocolRAMTurnOrder.has_previous len j hj) i
    (ProtocolRAMVisitColumns.total (walk base bits data keys tails heads)).eval m (i.val:Word W)=
      (routeSite i:Word W)+carried (fun j=>(routeSite j:Word W)) i prior :=
  live_endpoint_on B inj pad o items base bits offset data keys tails heads m weight rom small start
    (fun a _ j hj=>key _ (ProtocolRAMTurnOccurrence.address o (items a) j hj)) endpoints i active

end Hierarchy.ProtocolRAMTurnMap

end
end OAI
