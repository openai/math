import OAI.Computability.NearSquareRoot.PrecisionGridLocalRulers
import OAI.Computability.NearSquareRoot.BoxProgram

/-! # Computing the finite iteration domains used by a canonical box phase pass -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Staff Strip BoxFin SynchronizedBlocks

variable {I : Type} {s : Regime I} {k l : I → ℕ} {b : I → List (ℕ × ℕ)}

/-- The unary global width produces the physical width and order of every
axis of the canonical box through its uniform coprime-parameter algorithm. -/
theorem generatedBoxHeader (K : Realizes s k) :
    s.Has (fun i ↦ (CoprimeBox.box (k i)).map (fun p ↦ (tally p.1,tally p.2))) := by
  have h := K.thenDo BoxProgram.encoded_poly
  simpa only [BoxProgram.encoded, Function.comp_def, Staff.box,tally_length] using h

/-- Counting the descriptor entries gives the number of synchronized blocks. -/
theorem blockCountAvailable (H : s.Has (fun i ↦ (b i).map (fun p ↦ (tally p.1,tally p.2)))) :
    Realizes s (fun i ↦ (b i).length/4) := by
  have e : Easy (fun x : List (Tally × Tally) ↦ x.map (fun _ ↦ ())) := by fun_prop
  have ready := H.ez e
  have L : Realizes s (fun i ↦ (b i).length) := by
    simpa only [Realizes,Function.comp_def,Staff.box,tally,List.map_const',List.length_map] using ready
  exact L.dividing (.fix 4)

/-- At the block-enumeration header the length of its local phase table is
the computed product of at most seven unary padded radices. -/
theorem blockRadixAvailable (hb : ∀ i, BoxShape.Valid (k i) (l i) (b i))
    (H : s.Has (fun i ↦ (b i).map (fun p ↦ (tally p.1,tally p.2))))
    (D : Realizes s (fun i ↦ (b i).length/4)) :
    Realizes (signal _ D) (fun t : Across (fun i ↦ (b i).length/4) ↦ blockRadix (b t.1) t.2) := by
  let n i := (b i).length/4
  have lifted := sendRoof n D _ H
  exact (blockExtractionRulers (s := signal n D) (fun t : Across n ↦ hb t.1) lifted
    (fun t ↦ t.2) (fun t ↦ firstAxis t.2) (floor_ n D) (.fix 0)).2.2

end PhaseTable

end NearSquareRoot
end Computability
end OAI
