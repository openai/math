import OAI.Hierarchy.ProtocolRAMTurnCursor
import OAI.Hierarchy.ProtocolRAMTurnOccurrence

namespace OAI
/-! # The native pointer and endpoint scans follow the original CT route rows -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnMap
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe ProbeStage CoreBoard WireTelescope
open ProtocolRAM.Calendar CoreRoute ProtocolRAM ProtocolRAMTurnChart
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

theorem geography (base bits offset : ℕ) (chartData : Data) (edgeBank tailBank headBank : Bank)
    (m : Memory W) (v : Words)
    (rom : Loaded base bits (ProtocolRAMTurnGeometry.header o offset items) m)
    (old : chartData.Before v m (ProtocolRAMTurnGeometry.header o offset items))
    (small : ∀a,len a < 2^W)
    (start : ∀a,v.rawSource (ProtocolRAMTurnGeometry.sourceOrder edges h d k (items a)).val=ProtocolRAMTurnEdges.visit B inj pad (items a) 0)
    (edge : ∀t < edges+Count,edgeBank.read m (t:Word W)=(paid t:Word W))
    (tails : ∀t < edges,tailBank.read m (t:Word W)=((ends t).1:Word W))
    (heads : ∀t < edges,headBank.read m (t:Word W)=((ends t).2:Word W)) :
    let u := ProtocolRAMTurnGeometry.header o offset items
    ProtocolRAMVisitColumns.Geography (walk base bits chartData edgeBank tailBank headBank) m
      (fun i=>(u i).raw) (fun i=>(u i).origin) (fun i=>(u i).item) routeSite
      paid v.rawSource (fun x=>(ends x).1) (fun x=>(ends x).2) := by
  intro u
  let raw := ProtocolRAMTurnOrder.raw len
  have prev (i : Fin N) (hp : 0 < (u i).raw) : (u i).raw-1 < len (raw i).1 := by
    have h := (raw i).2.isLt
    change (raw i).2.val < len (raw i).1 + 1 at h
    change 0 < (raw i).2.val at hp
    change (raw i).2.val-1 < _
    omega
  have loc (i : Fin N) (hp : 0 < (u i).raw) := ProtocolRAMTurnOccurrence.address o (items (raw i).1) _ (prev i hp)
  have valid (i : Fin N) (hp : 0 < (u i).raw) :
      paid ((u i).origin+((u i).raw-1)) < edges := by
    have address : (u i).origin + ((u i).raw - 1) < edges + Count := loc i hp
    rw [ProtocolRAMTurnOccurrence.edgeAt, dite_eq_left address]
    exact Fin.isLt _
  refine ⟨(fun i=>rom 3 i),(fun i=>rom 1 i),(fun i=>rom 0 i),?_,?_,?_,?_,?_,?_,?_,?_⟩
  · exact fun i=>(ProtocolRAMTurnGeometry.within o offset items i).trans_lt (small (raw i).1)
  · exact fun i hp=>ProtocolRAMTurnOrder.has_previous len i hp
  · exact fun i _=>old.rawSource i
  · intro i z
    change v.rawSource (ProtocolRAMTurnGeometry.sourceOrder edges h d k (items (raw i).1)).val =
      ProtocolRAMTurnEdges.visit B inj pad (items (raw i).1) (raw i).2.val
    change (raw i).2.val=0 at z
    rw [z,start]
  · exact fun i hp=>edge _ (loc i hp)
  · exact fun i hp=>tails _ (valid i hp)
  · exact fun i hp=>heads _ (valid i hp)
  · exact fun i hp=>ProtocolRAMTurnOccurrence.adjacent B inj pad o items i hp

end Hierarchy.ProtocolRAMTurnMap

end
end OAI
