import OAI.ThreeFlat.Diagonal.TracePairLeaf
import OAI.ThreeFlat.Diagonal.LaneCursorTrace

namespace OAI
/-! # Cursor contraction after specializing all public H input coordinates -/

namespace ThreeFlat.Diagonal.TraceBitHeader
open Computability.VPVNP.BurstRAM LaneCursor LaneCursor.RowLayout TraceSuffix
open scoped BigOperators Classical
variable {F : Type*} [Fintype F] [CommRing F] {w p S f q low : ℕ}
variable (hF : Fintype.card F ≤ 2^w) (hw : 3≤w+1) (hp : p≤2^(w+1))
    (base : ℕ) (st : Word w) (hs : S≤2^w) (hf : f≤2^(w+1)) (r k : ℕ)
    (fit : S+f≤2^(1+((q+1)+low)))
theorem trueNetwork_cursor {copies T : ℕ} (size : 2*T≤S) (pub : ℕ→Bool) (pin : Fin (2*T)→Bool) :
    (∑ fields : Fields (q+1) copies (Fin (1+(((q+1)+low)+((q+1)+low)))) (PayloadAddress low (TraceStaticRow.gateTable hF hw hp base f st r k ((q+1)+low)).cells),
      ∏ i, ∏ lane, vertexFactor (layout hF hw hp base st hs hf r k fit).mask ((layout hF hw hp base st hs hf r k fit).localTensor (fullHeader size pin pub)) fields i lane) =
        (trueNetwork (q:=q) (low:=low) hF hw hp base st hs hf r k size pub).eval pin :=
  ((layout hF hw hp base st hs hf r k fit).eval_cursor (fullHeader size pin pub)).trans
    (trueNetwork_eval hF hw hp base st hs hf r k size pub pin).symm


end ThreeFlat.Diagonal.TraceBitHeader

end OAI
