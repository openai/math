import OAI.Computability.NearSquareRoot.SynchronizedPermutationActual
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepGeometry

/-! # Supplying all guarded-mask parameters from the generated Fourier pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

set_option maxHeartbeats 1600000
namespace Benes.PackedBatchHeader
open IntegerMultiplication Code Packed Strip Strip.Dims Controlled Staff Carry

variable {X : Type} {r : Regime X}

/-- The polynomial-time header suffices to generate the full extent and signs
read by the native physical mask, including the guard segment for an empty batch. -/
theorem geometryHas (k A H b B : X → ℕ) (head : X → Staging)
    (supply : r.Has fun x => (((tally (k x),tally (A x),tally (H x),tally (b x),tally (B x)), head x) : PlacedHeader)) :
    Realizes r k ∧ Realizes r A ∧ Realizes r H ∧ Realizes r b ∧ Realizes r B ∧
      Realizes r (extent H (fun _ => 0) b) ∧ (r.Has fun x => signs (H x) 0 (b x)) ∧ r.Has head := by
  have hk : Realizes r k := supply.ez (show Easy (fun s : PlacedHeader => s.1.1) by fun_prop)
  have hA : Realizes r A := supply.ez (show Easy (fun s : PlacedHeader => s.1.2.1) by fun_prop)
  have hH : Realizes r H := supply.ez (show Easy (fun s : PlacedHeader => s.1.2.2.1) by fun_prop)
  have hb : Realizes r b := supply.ez (show Easy (fun s : PlacedHeader => s.1.2.2.2.1) by fun_prop)
  have hB : Realizes r B := supply.ez (show Easy (fun s : PlacedHeader => s.1.2.2.2.2) by fun_prop)
  exact ⟨hk,hA,hH,hb,hB,(hb.plus (.fix 1)).times ((hH.plus (.fix 1)).plus (.fix 0)),
    Regime.Has.pair hH (Regime.Has.pair (Realizes.fix 0) hb),supply.ez Easy.snd⟩

/-- A single raw row and stage ticket generates the actual physical dimensions
alongside both compiled permutations and the block query plan. -/
theorem rowGeometryHas (k L : X → ℕ) (D : ℕ) (dir side : X → Bool) (row : X → Tally)
    (j β : X → ℕ) (valid : ∀ x, BoxShape.Valid (k x) (L x) (CoprimeBox.box (k x)))
    (raw : r.Has fun x => (((dir x,tally (k x),row x),(side x,tally (j x)),tally (β x)) : RowPass)) :
    r.Has fun x =>
      (((tally (k x),tally (highBits D (k x) (β x) (j x)),tally (guardWidth (k x)-1),
        tally (live (k x) (β x) (j x)),tally (payloadBits D (k x))),
        fullHeader D ((dir x,tally (k x),row x),(side x,tally (j x)),tally (β x))) : PlacedHeader) := by
  let key (x : X) : RowPass := ((dir x,tally (k x),row x),(side x,tally (j x)),tally (β x))
  have supplied := Regime.Has.thenDo (r := r) (g := key)
    (f := fun z => placedHeader (tally D,z)) raw (placedHeader_fixed D)
  have e : (fun x => placedHeader (tally D,key x)) =
      (fun x => (((tally (k x),tally (highBits D (k x) (β x) (j x)),tally (guardWidth (k x)-1),
        tally (live (k x) (β x) (j x)),tally (payloadBits D (k x))),fullHeader D (key x)) : PlacedHeader)) :=
    funext fun x => geometry_eq (valid x) D (dir x) (row x) (side x) (j x) (β x)
  exact (congrArg (fun v : X → PlacedHeader => r.Has v) e).mp supplied

end Benes.PackedBatchHeader

end NearSquareRoot
end Computability
end OAI
