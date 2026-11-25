import OAI.Hierarchy.ProtocolRAMTurnEdges
import OAI.Hierarchy.ProtocolRAMTurnDictionary

namespace OAI
/-! # Original-order paid edge lookup at the public turn header address -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnOccurrence
open ProbeStage CoreBoard AdaptiveProbe WireTelescope SettledMatrix
open ProtocolRAM.Calendar CoreRoute
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor

variable {h d k edges K : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k → Fin K} (B : Mount (S:=S) π place edges)
    (inj : Function.Injective place) (pad : Chord K) (o : Orders h d k)

local notation "L" => B.matrixLayout inj pad
local notation "Count" => Fintype.card (Slots h d k)

def endsAt (v : ℕ) : ℕ×ℕ :=
  if hv : v < edges then ProtocolRAMTurnEdges.ends B inj pad ⟨v,hv⟩ else (0,0)

theorem adjacent {n : ℕ} (items : Fin n ≃ ProtocolRAMTurnGeometry.Source edges h d k)
    (i : Fin (ProtocolRAMTurnOrder.turns (ProtocolRAMTurnGeometry.length ∘ items)))
    (pos : 0 < (ProtocolRAMTurnOrder.raw (ProtocolRAMTurnGeometry.length ∘ items) i).2.val) :
    let len := ProtocolRAMTurnGeometry.length ∘ items
    let j := ProtocolRAMTurnOrder.raw len i
    let old := ProtocolRAMTurnGeometry.origin o (items j.1)+(j.2.val-1)
    let e := endsAt B inj pad (edgeAt B inj pad o old)
    let site := ProtocolRAMVisitAdjacency.vertex len (fun a=>ProtocolRAMTurnEdges.visit B inj pad (items a))
    e.1+e.2=site i+site ⟨i.val-1,(Nat.sub_le ..).trans_lt i.isLt⟩ := by
  intro len j old e site
  have prev : j.2.val-1 < (ProtocolRAMTurnEdges.walk B (items j.1)).length := by
    rw [ProtocolRAMTurnEdges.walk_length]
    have h := j.2.isLt
    change j.2.val < ProtocolRAMTurnGeometry.length (items j.1)+1 at h
    change 0 < j.2.val at pos
    omega
  let first := (ProtocolRAMTurnEdges.walk B (items j.1))[j.2.val-1]
  let total (t : ℕ) : Fin edges := if h : edgeAt B inj pad o t < edges then ⟨_,h⟩ else first
  have totalRead (a : Fin n) (t : ℕ) (h : t < (ProtocolRAMTurnEdges.walk B (items a)).length) :
      total (ProtocolRAMTurnGeometry.origin o (items a)+t)=(ProtocolRAMTurnEdges.walk B (items a))[t] := by
    dsimp only [total]
    rw [read B inj pad o _ _ h]
    simp
  have same : edgeAt B inj pad o old=first.val := read B inj pad o (items j.1) (j.2.val-1) prev
  have equality : e=ProtocolRAMTurnEdges.ends B inj pad (total old) := by
    change endsAt B inj pad (edgeAt B inj pad o old)=_
    dsimp only [endsAt,total]
    simp only [same,dite_eq_left first.isLt]
  rw [equality]
  exact ProtocolRAMTurnEdges.adjacent B inj pad items (fun a=>ProtocolRAMTurnGeometry.origin o (items a))
    total totalRead i pos

end Hierarchy.ProtocolRAMTurnOccurrence

end
end OAI
