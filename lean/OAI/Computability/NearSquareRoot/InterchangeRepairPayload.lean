import OAI.Computability.NearSquareRoot.InterchangeRepairPhysical

/-!
# Repair on contiguous payloads

A single physical route carries every position of a record payload together.
At each payload position the scalar repair identity gives the same simultaneous
main-field exchange, for every payload type and every field width.
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

/-- The physical schedule with complete record payloads as used by the tape compiler. -/
def payload (D : Type) (F : Frame A m b) (I J : H → L) (M : Matrix H H K)
    (e : Environment K m) (T : Table K m) (P G S : Tape) (f : ℕ) :
    Data K L (Keys P G S (Fin (a+m+a)) (Block b f) × D) (width m) m →
    Data K L (Keys P G S (Fin (a+m+a)) (Block b f) × D) (width m) m :=
  schedule e T (tag (mainSlots a m) ∘ Prod.fst) (lift (forward f e)) (lift (backward f e))
    (predict rect I J M e (withPayload D (extendLayout P G S (F.layout f))))

theorem payload_of_table (D : Type) (F : Frame A m b) (I J : H → L) (M : Matrix H H K)
    (hM : (rectangleMatrix (K := K) rect).submatrix id J * M *
      (rectangleMatrix rect).submatrix I id = rectangleMatrix rect)
    (e : Environment K m) (T : Table K m)
    (hT : ∀ (C : Type) [LinearOrder C]
      (x : Fin (width m) → Row (Fin m) C (Coeff K m)) i a,
      SwapRepair.run e T x i a = x i (swapAll a))
    (P G S : Tape) (f : ℕ)
    (x : Data K L (Keys P G S (Fin (a+m+a)) (Block b f) × D) (width m) m)
    (w : L) (i : Fin (width m)) (z : Keys P G S (Fin (a+m+a)) (Block b f) × D) :
    payload D F I J M e T P G S f x w i z = x w i (swapMain (mainSlots a m) z.1,z.2) := by
  let s := mainSlots a m
  let g := extendLayout P G S (F.layout f)
  let k := key s (numerical z.1) z.1.1 z.1.2.2.1 z.1.2.2.2.2
  let t := numerical z.1 ∘ s
  have hk : k t = z.1 := key_self s z.1
  have swapEq (j : Fin m) (v : L) (c : Address (Fin m) (Fin (b^f))) :
      (g.S j v).symm (g.T j v (k c)) = k (swap j c) :=
    (F.native_pull j v P G S f (k c)).trans (key_swap s _ _ _ _ c j).symm
  let kp := withPayloadKey k z.2
  have hpred := fun y => predict_on_fibre rect I J M e (withPayload D g) hM kp
    (withPayload_pull g k z.2 swap swapEq) y w
  have hf := lift_key (forward f e) _ k (forward_key s _ _ _ _ e.invRadix (inv_two e) (List.finRange m)) z.2
  have hb := lift_key (backward f e) _ k (inverse_key s _ _ _ _ e.invRadix (inv_two e) (List.finRange m)) z.2
  have h := schedule_on_fibre e T (tag s ∘ Prod.fst) (lift (forward f e)) (lift (backward f e))
    (predict rect I J M e (withPayload D g)) kp w hpred hf hb (tag_key s _ _ _ _) x
  have out := congrFun (congrFun h i) t
  change payload D F I J M e T P G S f x w i (k t,z.2) =
    SwapRepair.run e T (fun i a => x w i (k a,z.2)) i t at out
  rw [hT, show k (swapAll t) = swapMain s (k t) from key_swapAll s _ _ _ _ t, hk] at out
  exact out

end Interchange.RepairSchedule

end

end NearSquareRoot
end Computability
end OAI
