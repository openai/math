import OAI.Hierarchy.DescentTerminalPrimitiveReceipts
import OAI.Hierarchy.DescentTerminalBoundaryBasis
import OAI.Hierarchy.DescentLocalPrivateNames
import OAI.Hierarchy.DescentTerminalMaskOperands

namespace OAI
/-! # The physical q-band operand digit of a true restricted, numbered scalar recipe -/
namespace Hierarchy.DescentTerminalBoundaryPointer
open DescentTerminalVertexFields DescentKernelHistory DescentBundleHistory DescentTerminalGraphPositions
open DescentTerminalChronologicalBooks DescentTerminalBoundaryBasis Computability.BorderVNP.Crossing DescentTerminalRecipeRows
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
variable {P Tag : Type} [Fintype P] {D p tags q : ℕ} {bits:P→ℕ} (G:Network D P bits) (hp:0<p) (v:G.Site)
    (rank:Boundary G v↪ℕ) (r:Recipe Tag (BlockRef p (boundaryWidth G v))) (code:Tag→Fin tags)
    (aliases:r.UsedWord↪ℕ)
local notation "l" => numbered G hp v rank r.restricted code

def num (u:r.Node) (j:Fin (r.arity u)) : ℕ :=
  ((l).operand u j).elim (fun h=>h.val+1) (fun h=>q+(ordinal aliases h).val+1)

/-- The public digit is a direct address in the complete physical incident/exterior chart,
regardless of the multiplicity with which this node or another node reads the same block. -/
theorem public_word (u:r.Node) (j:Fin (r.arity u)) (b:BlockRef p (boundaryWidth G v)) (hit:r.operand u j=.inl b) :
    num (q:=q) G hp v rank r code aliases u j=
      1+ProtocolRAMPortRanks.«prefix» (fun a=>poolBatchCount (boundaryWidth G v a) p) rank b.port+b.block := by
  have selected : r.activePort u j = .inl b := by
    have readback := r.activePort_read u j
    rw [hit] at readback
    cases e : r.activePort u j with
    | inl ref =>
      have same : ref = b := by simpa [e] using readback
      exact congrArg Sum.inl same
    | inr word => simp [e] at readback
  simp [num, numbered, Recipe.restricted, selected, address_val]
 ; omega

/-- The private digit counts only distinct *used* smaller aliases, independent of gaps
and of repeated occurrences of the same old private word. -/
theorem private_word (u:r.Node) (j:Fin (r.arity u)) (h:r.UsedWord) (hit:r.operand u j=.inr h.val) :
    num (q:=q) G hp v rank r code aliases u j=q+1+(Finset.univ.filter (fun t=>aliases t<aliases h)).card := by
  have selected : r.activePort u j = .inr h := by
    have readback := r.activePort_read u j
    rw [hit] at readback
    cases e : r.activePort u j with
    | inl ref => simp [e] at readback
    | inr word =>
      have same : word.val = h.val := by simpa [e] using readback
      exact congrArg Sum.inr (Subtype.ext same)
  simp [num, numbered, Recipe.restricted, selected, ordinal_val]
 ; omega

/-- Two earlier branch-specific numeric readings suffice to identify the scalar argument
byte of an honest local leaf. No optional-union/dense-name surrogate enters the receipt. -/
theorem operand_read (u:r.Node) (j:Fin (r.arity u)) (value:ℕ)
    (ext:∀b,r.operand u j=.inl b→value=1+ProtocolRAMPortRanks.«prefix»
      (fun a=>poolBatchCount (boundaryWidth G v a) p) rank b.port+b.block)
    (priv:∀h:r.UsedWord,r.operand u j=.inr h.val→value=q+1+(Finset.univ.filter (fun t=>aliases t<aliases h)).card) :
    value=num (q:=q) G hp v rank r code aliases u j := by
  cases hit:r.operand u j with
  | inl b=>exact (ext b hit).trans (public_word G hp v rank r code aliases u j b hit).symm
  | inr h=>
    let live:r.UsedWord:=⟨h,u,j,hit⟩
    exact (priv live hit).trans (private_word G hp v rank r code aliases u j live hit).symm

end
end Hierarchy.DescentTerminalBoundaryPointer

end OAI
