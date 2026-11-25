import OAI.Hierarchy.DescentReachedIssuedHeaders
import OAI.Hierarchy.DescentResolvedHeaderRoom

namespace OAI
/-! Uniform output-width bounds from the ordinary resolved inputs and true source wire capacity. -/
namespace Hierarchy.DescentSixParty.Reached
open Computability.BorderVNP.Crossing DescentKernelHistory DescentLocalPrivateNames DescentLocalArchiveOrder DescentBundleHistory
open Chronology DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks DescentDatedPriorOperand
open DescentPackedColony DescentOrdinaryFinal DescentSharedCableNames
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
    {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k age grain degree wire hist p R : ℕ}
    (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W)
    (number : Local B) (shape : WorldShape p R B) (hp : 0<p) (pin : P→ℕ)
local notation:max "recipe" v:arg => ((shape.sites v).recipe hp)

variable (cpu:PhysicalOrdinary F P) (v:W.graph.Site)
local notation "L" => cpu.resolver
local notation "D" => cpu.finalChart
variable (population:Fintype.card (B.recipe v).Node≤(L).nodes) (args:∀u,(recipe v).arity u≤(L).operands)
local notation "onsite" => (number v).toEmbedding.trans (Fin.castLEEmb population)
local notation "mouth" => (D).mouths (recipe v) onsite args
variable (hidden:(recipe v).UsedWord↪Key) (metaRows:cpu.MetaWords) (old:Books (L))
    (jobs:Fin (L).jobs→DescentDatedPriorOperand.Source (L))
    (x:Fin (L).blocks) (h:Fin (L).hosts) (g:Fin (L).groups)
local notation:max "fragment" u:arg j:arg => cpu.issuedFragment jobs x h g (mouth ⟨u,j⟩)
local notation:max "expected" u:arg j:arg => argumentPointer cap B number shape hp pin (L).operands ⟨v,u⟩ (Fin.val j)


private theorem firstCable_serial {v:W.graph.Site} (e:Incident W.graph v) (low:ℕ)
    (alive:(low+1)*p≤W.graph.width e.val) {peer serial chunk:ℕ}
    (eqn:firstCable cap hp v e low alive=Pointer.cable peer serial chunk) : serial<cap.placement.cap :=by
  unfold firstCable at eqn
  have name:=(Pointer.cable.inj eqn).2.1
  rw [←name]
  exact Fin.isLt _

theorem argument_header_room (capacity:cap.placement.cap≤2^(D).field)
    (rectangle:(D).keys≤2^(D).field) (u:(B.recipe v).Node) (j:Fin ((recipe v).arity u))
    (cable:∀(e:Incident W.graph v) k (live:(k+1)*p≤W.graph.width e.val),
      (recipe v).operand u j=.inl ⟨.inl e,k,live⟩→
        Pointer.ofKey 0 (resolve (fragment u j))=firstCable cap hp v e k live)
    (exterior:∀(z:Attached W.graph v) k (live:(k+1)*p≤bits z.val),
      (recipe v).operand u j=.inl ⟨.inr z,k,live⟩→ resolve (fragment u j)=Key.pin (pin z.val) k)
    (f:Fin 4) : (expected u j).header f<2^(D).field :=by
  cases assigned:(recipe v).operand u j with
  | inr a =>
    let word:(recipe v).UsedWord:=⟨a,⟨u,j,assigned⟩⟩
    rw [argumentPointer_private cap B number shape hp pin (L).operands v u j mouth
      (mouth_address B number shape hp cpu v population args) word assigned]
    exact Pointer.private_header_room _ ((firstAlias (recipe v) mouth word).isLt.trans_le rectangle) f
  | inl b =>
    rcases b with ⟨e|z,k,alive⟩
    · have source:=cable e k alive assigned
      rw [argumentPointer_cable cap B number shape hp pin (L).operands v u j e k alive assigned,←source]
      apply Pointer.resolved_header_room
      intro peer serial chunk which
      rw [which] at source
      exact (firstCable_serial cap hp e k alive source.symm).trans_le capacity
    · have source:=exterior z k alive assigned
      rw [argumentPointer_pin cap B number shape hp pin (L).operands v u j z k alive assigned]
      change (Pointer.ofKey 0 (Key.pin (pin z.val) k)).header f<_
      rw [←source]
      apply Pointer.resolved_header_room
      intro peer serial chunk which
      rw [source] at which
      contradiction

end
end Hierarchy.DescentSixParty.Reached

end OAI
