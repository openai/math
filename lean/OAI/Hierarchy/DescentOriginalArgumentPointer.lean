import OAI.Hierarchy.DescentNodeLocalEnumeration
import OAI.Hierarchy.DescentArchiveWorldShape
import OAI.Hierarchy.DescentBundleTerminal
import OAI.Hierarchy.DescentOperandStateCodec
import OAI.Hierarchy.DescentReached
import OAI.Hierarchy.DescentDatedVenueSources
import OAI.Hierarchy.DescentTerminalPortChart
import OAI.Hierarchy.DescentLocalPrivateNames

namespace OAI
/-! # Pointer names of original arguments before reading a physical row -/
namespace Hierarchy.DescentSixParty.Reached
open DescentBundleHistory DescentKernelHistory DescentLocalArchiveOrder DescentLocalPrivateNames
open DescentSharedCableNames DescentOperandStateBanks DescentCompiler DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing ThreeFlat.Routing
open scoped Classical
noncomputable section
set_option quotPrecheck false
variable {Tag A : Type} (r : Recipe Tag A)
    (address : Slot r→ℕ) (u : r.UsedWord)

private theorem private_hit : ∃n,∃j : Slot r,address j=n ∧ read r j=some u :=by
  obtain ⟨j,hj⟩:=hit r u
  exact ⟨_,j,rfl,hj⟩

def privateAddress : ℕ := Nat.find (private_hit r address u)

theorem privateAddress_at {K : ℕ} («alias» : Slot r↪Fin K) (same : ∀j,address j=(«alias» j).val) :
    privateAddress r address u=(firstAlias r «alias» u).val :=by
  apply Nat.le_antisymm
  · obtain ⟨j,eqn,hr⟩:=firstAlias_read r «alias» u
    apply Nat.find_min' (private_hit r address u)
    exact ⟨j,(same _).trans (congrArg Fin.val eqn),hr⟩
  · obtain ⟨j,eqn,hr⟩:=Nat.find_spec (private_hit r address u)
    unfold privateAddress
    rw [←eqn,same]
    exact firstAlias_le r «alias» j u hr

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist p R : ℕ}
    (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (shape : WorldShape p R B) (hp : 0<p) (pin : P→ℕ) (arity : ℕ)
local notation "recipe" v => ((shape.sites v).recipe hp)
local notation "native" => cap.order.trans Fin.valEmbedding
local notation "ranks" => groupRank ((Function.Embedding.refl (Fin (S.groupCount age))).trans Fin.valEmbedding) (cap.vertex.trans Fin.valEmbedding)
local notation "places" => DescentPacking.PackedMatch.Local.Stage.cableNames k ranks

def firstCable (v : W.graph.Site) (edge : Incident W.graph v) (chunk : ℕ)
    (fits : (chunk+1)*p≤W.graph.width edge.val) : Pointer :=by
  have alive : 0<cap.placement.grainCount edge.val:=by
    by_contra! empty
    have exactWidth:=cap.placement.grainCount_fit S cap.valid edge.val
    rw [show cap.placement.grainCount edge.val=0 by omega,Nat.zero_mul] at exactWidth
    have noRoom : (chunk+1)*p ≤ 0 := fits.trans_eq exactWidth
    exact (Nat.not_lt_of_ge noRoom) (Nat.mul_pos (Nat.zero_lt_succ chunk) hp)
  let wing:=Stage.live cap.placement native S cap.valid places (Stage.home cap.placement v)
    (DescentTerminalPortChart.first cap.placement v edge alive)
  exact .cable wing.neighbor.val wing.wire.val chunk

def argumentPointer (y : NodeOrder.All B) (j : ℕ) : Pointer :=
  if live : j<(recipe y.1).arity y.2 then
    match (recipe y.1).activePort y.2 ⟨j,live⟩ with
    | .inr u => .privateWord (privateAddress (recipe y.1) (fun t=>(number y.1 t.1).val*arity+t.2.val) u)
    | .inl ref => match ref with
      | ⟨.inl edge,chunk,fits⟩ => firstCable cap hp y.1 edge chunk fits
      | ⟨.inr port,chunk,_⟩ => .pin (pin port.val) chunk
  else .privateWord 0

variable (v : W.graph.Site) (node : (B.recipe v).Node) (j : Fin (((shape.sites v).recipe hp).arity node))
local notation "expected" => argumentPointer cap B number shape hp pin arity ⟨v,node⟩ j.val

theorem argumentPointer_private {K : ℕ} («alias» : Slot (recipe v)↪Fin K)
    (addresses : ∀q : Slot (recipe v),(number v q.1).val*arity+q.2.val=(«alias» q).val)
    (word : (recipe v).UsedWord) (source : (recipe v).operand node j=.inr word.val) :
    expected=.privateWord (firstAlias (recipe v) «alias» word).val :=by
  have active : (recipe v).activePort node j=.inr word:=by
    have readback:=(recipe v).activePort_read node j
    rw [source] at readback
    cases e:(recipe v).activePort node j with
    | inl ref=>simp [e] at readback
    | inr q=>
      have same : q.val=word.val:=by simpa [e] using readback
      exact congrArg Sum.inr (Subtype.ext same)
  simp only [argumentPointer,dite_eq_left j.isLt,Fin.eta,active]
  exact congrArg Pointer.privateWord (privateAddress_at (recipe v) _ word «alias» addresses)

private theorem active_public {ref : BlockRef p (boundaryWidth W.graph v)}
    (source : (recipe v).operand node j = .inl ref) :
    (recipe v).activePort node j = .inl ref := by
  have readback := ((recipe v).activePort_read node j).trans source
  cases eqn : (recipe v).activePort node j with
  | inl b =>
    rw [eqn] at readback
    exact congrArg Sum.inl (Sum.inl.inj readback)
  | inr a =>
    rw [eqn] at readback
    cases readback

theorem argumentPointer_cable (edge : Incident W.graph v) (chunk : ℕ)
    (fits : (chunk+1)*p≤W.graph.width edge.val)
    (source : (recipe v).operand node j=.inl ⟨.inl edge,chunk,fits⟩) :
    expected=firstCable cap hp v edge chunk fits :=by
  have active : (recipe v).activePort node j=.inl ⟨.inl edge,chunk,fits⟩:=by
    exact active_public B shape hp v node j source
  simp only [argumentPointer,dite_eq_left j.isLt,Fin.eta,active]

theorem argumentPointer_pin (z : Attached W.graph v) (chunk : ℕ) (fits : (chunk+1)*p≤bits z.val)
    (source : (recipe v).operand node j=.inl ⟨.inr z,chunk,fits⟩) :
    expected=.pin (pin z.val) chunk :=by
  have active : (recipe v).activePort node j=.inl ⟨.inr z,chunk,fits⟩:=by
    exact active_public B shape hp v node j source
  simp only [argumentPointer,dite_eq_left j.isLt,Fin.eta,active]


end
end Hierarchy.DescentSixParty.Reached

end OAI
