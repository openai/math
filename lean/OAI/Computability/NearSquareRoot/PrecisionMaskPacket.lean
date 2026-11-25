import OAI.Computability.NearSquareRoot.PrecisionGridRecover
import OAI.Computability.NearSquareRoot.SynchronizedCRTStream

/-! # Reading the occupied coefficients from a padded result tape

The command reconstructs the validity mask from the address-width ruler,
then scans it beside the inverse-CRT output. Padding cells may contain arbitrary
rounded data. Only positions marked valid become inputs to coefficient recovery.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedPoint

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits

abbrev boxVolume (box : List (ℕ × ℕ)) := ∏ j, BoxFin.modulus box j

/-- Contents of the occupied slots after an inverse CRT arrangement, in rank order. -/
noncomputable def occupiedRecords {k w l : ℕ} {box : List (ℕ × ℕ)} (hv : BoxShape.Valid k l box)
    (v : Fin (2^k) → Dusk.Grain w) : Fin (boxVolume box) → Dusk.Grain w :=
  letI := BoxFin.modulus_neZero hv
  v ∘ BoxFin.digitSlot hv

private def compactPacket
    (i : List Bool × Tally × Tally × Tally × List Dusk.Pair) :
    Tally × Tally × Tally × List Dusk.Pair :=
  (i.2.1, i.2.2.1, i.2.2.2.1,
    BoxMaskedRecords.compress ([], []) (i.1, i.2.2.2.2))

private theorem compactPacket_easy : Easy compactPacket := by
  have h := BoxMaskedRecords.compress_easy (A := Dusk.Pair) ([], [])
  unfold compactPacket
  fun_prop

/-- Number of actual coefficients never exceeds the padded tape length. -/
theorem boxVolume_le {k l : ℕ} {box : List (ℕ × ℕ)} (hv : BoxShape.Valid k l box) :
    boxVolume box ≤ 2^k := by
  rw [boxVolume, BoxFin.prod_modulus, ← BoxOrder.count_shape,
    ← BoxOrder.length_shape hv]
  exact List.count_le_length

private theorem compactPacket_eq {k w l : ℕ} {box : List (ℕ × ℕ)} (hv : BoxShape.Valid k l box)
    (n b p : ℕ) (v : Fin (2^k) → Dusk.Grain w) :
    compactPacket (BoxOrder.expand (BoxOrder.shape box), tally n, tally b, tally p,
        List.ofFn (fun j => Dusk.mark (v j))) =
      (tally n, tally b, tally p, List.ofFn (fun j => Dusk.mark (occupiedRecords hv v j))) := by
  let := BoxFin.modulus_neZero hv
  unfold compactPacket
  change (_, _, _, BoxMaskedRecords.compress _ (BoxOrder.expand (BoxOrder.shape _), _)) = _
  rw [BoxFin.compress_dense hv]
  rfl

/-- The input supplies compact unary rulers and an array of marked post-inverse
CRT records. The same command handles every valid generated box. -/
theorem recoverOccupiedStream {I : Type} (k w n b p l : I → ℕ) (box : I → List (ℕ × ℕ))
    (hv : ∀ i, BoxShape.Valid (k i) (l i) (box i)) (v : (i : I) → Fin (2^(k i)) → Dusk.Grain (w i))
    (generate : Task (fun i => 2^(k i)) (fun i => send (tally (k i)))
      (fun i => send (BoxOrder.expand (BoxOrder.shape (box i))))) :
    Task (fun i => n i + (2^(k i)+1)*(w i+p i+b i+1))
      (fun i => send (tally (k i), tally (n i), tally (b i), tally (p i),
        List.ofFn (fun j => Dusk.mark (v i j))))
      (fun i => send (tally (n i), tally (b i), tally (p i),
        List.ofFn (fun j => Dusk.mark (occupiedRecords (hv i) (v i) j)))) := by
  let rows i := List.ofFn (fun j => Dusk.mark (v i j))
  let rest i := (tally (n i), tally (b i), tally (p i), rows i)
  have mask := generate.left (fun i => send (rest i))
  have scan := compactPacket_easy.on (fun i => (BoxOrder.expand (BoxOrder.shape (box i)), rest i))
  have run := mask.compose scan
  have hout i : compactPacket (BoxOrder.expand (BoxOrder.shape (box i)), rest i) =
      (tally (n i), tally (b i), tally (p i),
        List.ofFn (fun j => Dusk.mark (occupiedRecords (hv i) (v i) j))) :=
    compactPacket_eq _ _ _ _ _
  simp only [hout] at run
  apply run.bound 20
  intro i
  have hr := markedListSize (List.ofFn (v i))
  rw [List.map_ofFn, List.length_ofFn] at hr
  simp only [Function.comp_def] at hr
  simp only [rest, rows, size_prod, size_word, size_tally, tally_length]
  rw [show (BoxOrder.expand (BoxOrder.shape (box i))).length = 2^(k i) from BoxOrder.length_shape (hv i), hr]
  nlinarith

end FixedPoint

end NearSquareRoot
end Computability
end OAI
