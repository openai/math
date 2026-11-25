import OAI.Computability.NearSquareRoot.InterchangeRepairSchedule
import OAI.Computability.NearSquareRoot.InterchangeCompiledPivot
import OAI.Computability.NearSquareRoot.InterchangeSpectralFibre

/-!
# Exact batch swap on the native records of a compiled frame

The selected minor, finite alphabets and spectral lookup table are chosen
independently of the field width and the three spectator tapes. The equality
holds on every native record, including its two banks of reserve coordinates.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace Interchange.RepairSchedule

open IntegerMultiplication IntegerMultiplication.Port IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangeSlots InterchangeSpectralFibre SwapRepair SwapSpectrum Support RectangleAtlas

variable {K L B H : Type} [Field K] [DecidableEq L] [Fintype L] [Fintype B] [Fintype H]
  {rect : B → Rectangle L} {a m b : ℕ} [NeZero b] {A : RectangleAtlas rect a}

def mainSlots (a m : ℕ) : Fin m ↪ Fin (a+m+a) :=
  ⟨mainRank a, fun _ _ h => Fin.ext (Nat.add_left_cancel (congrArg Fin.val h))⟩

def forward {P G S : Tape} (f : ℕ) (e : Environment K m) :
    (Keys P G S (Fin (a+m+a)) (Block b f) → Coeff K m) →
      Keys P G S (Fin (a+m+a)) (Block b f) → Coeff K m :=
  ((List.finRange m).map (mainSlots a m)).foldl (fun x j => InterchangeSpectralRequest.advance false e.invRadix j x)

def backward {P G S : Tape} (f : ℕ) (e : Environment K m) :
    (Keys P G S (Fin (a+m+a)) (Block b f) → Coeff K m) →
      Keys P G S (Fin (a+m+a)) (Block b f) → Coeff K m :=
  ((List.finRange m).map (mainSlots a m)).reverse.foldl (fun x j => InterchangeSpectralRequest.advance true e.invRadix j x)

/-- Run the ordinary packed predictor on the compiled address atlas, using the
native selected-field spectral sweeps only for the check rows. -/
def physical (F : Frame A m b) (I J : H → L) (M : Matrix H H K) (e : Environment K m)
    (T : Table K m) (P G S : Tape) (f : ℕ) :
    Data K L (Keys P G S (Fin (a+m+a)) (Block b f)) (width m) m →
    Data K L (Keys P G S (Fin (a+m+a)) (Block b f)) (width m) m :=
  schedule e T (tag (mainSlots a m)) (forward f e) (backward f e)
    (predict rect I J M e (extendLayout P G S (F.layout f)))

/-- Any spectral table satisfying the repair identity on the abstract main
cube works unchanged after compiling the rectangle atlas on native records. -/
theorem physical_of_table (F : Frame A m b) (I J : H → L) (M : Matrix H H K)
    (hM : (rectangleMatrix (K := K) rect).submatrix id J * M *
      (rectangleMatrix rect).submatrix I id = rectangleMatrix rect)
    (e : Environment K m) (T : Table K m)
    (hT : ∀ (C : Type) [LinearOrder C]
      (x : Fin (width m) → Row (Fin m) C (Coeff K m)) i a,
      SwapRepair.run e T x i a = x i (swapAll a))
    (P G S : Tape) (f : ℕ)
    (x : Data K L (Keys P G S (Fin (a+m+a)) (Block b f)) (width m) m) (w : L)
    (i : Fin (width m)) (u : Keys P G S (Fin (a+m+a)) (Block b f)) :
    physical F I J M e T P G S f x w i u = x w i (swapMain (mainSlots a m) u) := by
  let s := mainSlots a m
  let k := key s (numerical u) u.1 u.2.2.1 u.2.2.2.2
  let z := numerical u ∘ s
  have hs : k z = u := key_self s u
  let g := extendLayout P G S (F.layout f)
  have swapEq (j : Fin m) (v : L) (d : Address (Fin m) (Fin (b^f))) :
      (g.S j v).symm (g.T j v (k d)) = k (swap j d) :=
    (F.native_pull j v P G S f (k d)).trans (key_swap s _ _ _ _ d j).symm
  have h := schedule_on_fibre e T (tag s) (forward f e) (backward f e)
    (predict rect I J M e g) k w
    (fun y => predict_on_fibre rect I J M e g hM k swapEq y w)
    (forward_key s _ _ _ _ e.invRadix (inv_two e) (List.finRange m))
    (inverse_key s _ _ _ _ e.invRadix (inv_two e) (List.finRange m))
    (tag_key s _ _ _ _) x
  have out := congrFun (congrFun h i) z
  change physical F I J M e T P G S f x w i (k z) =
    SwapRepair.run e T (fun i a => x w i (k a)) i z at out
  rw [hT, show k (swapAll z) = swapMain s (k z) from key_swapAll s _ _ _ _ z, hs] at out
  exact out

/-- One table realizes the simultaneous main-pair swap at all widths, leaving
all spectators fixed. -/
theorem physical_correct (hm : 2 ≤ m) (F : Frame A m b) (I J : H → L) (M : Matrix H H K)
    (hM : (rectangleMatrix (K := K) rect).submatrix id J * M *
      (rectangleMatrix rect).submatrix I id = rectangleMatrix rect)
    (e : Environment K m) :
    ∃ T : Table K m, ∀ (P G S : Tape) (f : ℕ)
      (x : Data K L (Keys P G S (Fin (a+m+a)) (Block b f)) (width m) m) w i u,
      physical F I J M e T P G S f x w i u = x w i (swapMain (mainSlots a m) u) := by
  obtain ⟨T,hT⟩ := exists_table hm e
  exact ⟨T,physical_of_table F I J M hM e T hT⟩

/-- The compiled-frame identity has no assumed choice of an invertible minor
or auxiliary table. Both depend only on the fixed geometry and ground field. -/
theorem exists_shared_physical (hm : 2 ≤ m) (F : Frame A m b) (e : Environment K m) :
    let W := rectangleMatrix (K := K) rect
    ∃ I J : Fin W.rank → L, Function.Injective I ∧ Function.Injective J ∧
      IsUnit (W.submatrix I J) ∧
      ∃ T : Table K m, ∀ (P G S : Tape) (f : ℕ)
        (x : Data K L (Keys P G S (Fin (a+m+a)) (Block b f)) (width m) m) w i u,
        physical F I J (W.submatrix I J)⁻¹ e T P G S f x w i u = x w i (swapMain (mainSlots a m) u) := by
  let W := rectangleMatrix (K := K) rect
  obtain ⟨I,J,hi,hj,hu,hM⟩ := exists_skeleton W
  exact ⟨I,J,hi,hj,hu,physical_correct hm F I J _ hM e⟩

end Interchange.RepairSchedule

end

end NearSquareRoot
end Computability
end OAI
