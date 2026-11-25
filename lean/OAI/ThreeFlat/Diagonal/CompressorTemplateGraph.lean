import OAI.ThreeFlat.Diagonal.CompressorLiveFields

namespace OAI
/-! # Evaluating the installed graph update against the selected physical graph -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr RAM.DescriptorExpr Placement Graph
open scoped BigOperators Classical Fin.NatCast
variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {w t l : ℕ}
variable (cell : Word w) (pub : Fin 1 → Word w) (mem : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value (fun _=>cell) mem vs
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l)
variable (R : ArcReads P E (g.map (Formula.value (fun _ => cell) mem vs)) mem)
variable (code : B ↪ ℕ) (hc : ∀ b,E.base b=(code b:Word w)) (hi : Function.Injective E.base)
variable (bound : ∀i,S.pieces i≤S.pieceRadix) (fit : ∀e,edgeId S P code bound e<2^w)
variable (lay : Bool) (colors : 2≤S.colors) (good : TagConditions P.slots (shift P) P.offset)

include pub R hc hi in
theorem retained_field (one : (1:Word w)≠0)
    (rad : (radices o ptr S).map V = rowRadices (w:=w) (t:=t) (l:=l) S)
    (cap : liveDegree S≤2^w) (tagsFit : 2^t<2^w)
    (basesFit : ∀v : B × BitWord t,(E.base v.1).val*2^t+(tagOrdinal t v.2).val<2^w)
    (rev : Bool) (p : (B × BitWord t) × Fin (liveDegree S)) (j : Field) (dest : F)
    (bv : V (.op .div (.op .sub (.reg 0) dest) (.lit S.outputDegree))=baseAddress S E p.1)
    (iv : V (.op .mod (.op .sub (.reg 0) dest) (.lit S.outputDegree))=(p.2.val:Word w))
    (live : (p.2.val:Word w)<(S.liveDegree:Word w)) :
    let selected := shrinkingGraph P lay S.pieces
      (edgeOrder P code (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) colors binary_neg good
    V (update S lay rev j dest)=match j with
      | .neighbor => baseAddress S E (SlotImage.oriented selected rev p).1
      | .matePort => ((SlotImage.oriented selected rev p).2.val:Word w)
      | .delta => tagWord E.lanes (SlotImage.shift selected rev p)
      | .identifier => idEmbedding S P code bound fit ((ordinalOf S P code bound lay rev colors).symm p) := by
  dsimp only
  rw [update_live cell pub mem vs one S lay rev j dest _ _ bv iv live]
  unfold physicalCandidates
  rw [rad]
  have h := congrFun (query_graph S P E (g.map V) mem R code hc hi bound fit one lay rev colors cap tagsFit
    basesFit p.1 p.2) j
  have ends := graph_endpoint S P code bound lay colors good rev p
  have shifts := graph_shift S P code bound lay colors good rev p
  cases j <;> simpa only [ends.1,ends.2,shifts] using h

theorem padded_field (S : Stage) (lay rev : Bool) (j : Field) (dest : F)
    (base port : Word w)
    (bv : V (.op .div (.op .sub (.reg 0) dest) (.lit S.outputDegree))=base)
    (iv : V (.op .mod (.op .sub (.reg 0) dest) (.lit S.outputDegree))=port)
    (pad : ¬port<(S.liveDegree:Word w)) :
    V (update S lay rev j dest) = match j with
      | .neighbor => BinaryOp.bitXor.eval base 1
      | .matePort => port
      | _ => 0 := by
  have miss : decide (port < Fin.ofNat (2^w) S.liveDegree) = false :=
    decide_eq_false pad
  cases j <;> simp only [update,Formula.value,Comparison.test] at bv iv ⊢ <;>
    simp only [bv,iv,miss,Bool.false_eq_true,ite_false] <;>
    simp [Fin.ofNat_eq_cast]


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
