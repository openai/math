import OAI.Computability.NearSquareRoot.CRTControlledMask

/-! # Little-endian positions of the controlled XOR

For chunk width `H+1` and no low guard, the target bit of physical
chunk `j < i` is at offset `j*(H+1)`. The control array has its segments in
most-significant-first order, so this bit uses control `j.rev`.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Packed IntegerMultiplication.Adic
open IntegerMultiplication.Code IntegerMultiplication.Loom IntegerMultiplication.Strip
open IntegerMultiplication.Strip.Dims

noncomputable section

private def littleSeg {H : ℕ} (v : Seg 0 H) : Raw 2 := v.2.2 :: (most v.2.1).reverse

private def segmentsLE {H i : ℕ} (s : Fin i → Seg 0 H) : Raw 2 :=
  (List.ofFn fun j => most ((furrow H 0).cast (s j))).flatten.reverse

private lemma segmentsLE_succ {H i : ℕ} (s : Fin (i+1) → Seg 0 H) :
    segmentsLE s = segmentsLE (fun j => s j.succ) ++ littleSeg (s 0) := by
  simp only [segmentsLE, List.ofFn_succ, List.flatten_cons, List.reverse_append]
  rw [furrow_word, Packed.guard, tile_most]
  change _ ++ ((([] : Raw 2) ++ most (s 0).2.1) ++ [(s 0).2.2]).reverse = _
  simp [littleSeg]

private lemma segmentsLE_length {H i : ℕ} (s : Fin i → Seg 0 H) :
    (segmentsLE s).length = i*(H+1) := by
  induction i with
  | zero => simp [segmentsLE]
  | succ i ih =>
    rw [segmentsLE_succ, List.length_append, ih]
    simp [littleSeg, Nat.succ_mul]

private lemma segmentsLE_slot {H i : ℕ} (s : Fin i → Seg 0 H) (k : Fin i) (d : Fin (H+1)) :
    (segmentsLE s)[k.val * (H+1) + d.val]? = (littleSeg (s k.rev))[d.val]? := by
  induction i with
  | zero => exact Fin.elim0 k
  | succ i ih =>
    induction k using Fin.lastCases with
    | last =>
      rw [segmentsLE_succ, List.getElem?_append_right (by rw [segmentsLE_length]; simp),
        segmentsLE_length]
      simp
    | cast j =>
      have h : j.val * (H+1) + d.val < i * (H+1) := calc
        _ < j.val * (H+1) + (H+1) := Nat.add_lt_add_left d.isLt _
        _ = (j.val+1)*(H+1) := (Nat.succ_mul ..).symm
        _ ≤ i*(H+1) := Nat.mul_le_mul_right _ j.isLt
      rw [segmentsLE_succ, List.getElem?_append_left (by rw [segmentsLE_length]; exact h),
        Fin.rev_castSucc]
      exact ih _ j

private lemma badge_partsLE {H i : ℕ} (v : Queue H 0 i) :
    badge v = segmentsLE v.2.1 ++ (most ((flag H).cast v.1)).reverse := by
  rw [badge, least, labels, Packed.rows]
  change (_ ++ _ ++ ([] : Raw 2)).reverse = _
  simp only [List.append_nil, List.reverse_append]
  rfl

private lemma badge_segment {H i : ℕ} (v : Queue H 0 i) (k : Fin i) (d : Fin (H+1)) :
    (badge v)[k.val*(H+1) + d.val]? = (littleSeg (v.2.1 k.rev))[d.val]? := by
  rw [badge_partsLE, List.getElem?_append_left ?_, segmentsLE_slot]
  rw [segmentsLE_length]
  calc
    _ < k.val*(H+1) + (H+1) := Nat.add_lt_add_left d.isLt _
    _ = (k.val+1)*(H+1) := (Nat.succ_mul ..).symm
    _ ≤ i*(H+1) := Nat.mul_le_mul_right _ k.isLt

/-- Exact Boolean seen at each controlled target slot before XOR. -/
theorem badge_lowSlot {H i : ℕ} (y : Queue H 0 i) (j : Fin i) :
    (badge y)[j.val*(H+1)]? = some ((y.2.1 j.rev).2.2) := by
  simpa [littleSeg] using badge_segment y j (0 : Fin (H+1))

/-- The complete little-endian lookup, including the unaffected high chunk
and out-of-range addresses. A stride `G > 0` is obtained with `H = G-1`. -/
theorem badge_maskTarget_slot {H i : ℕ} (b : Fin i → Bool) (y : Queue H 0 i) (n : ℕ) :
    (badge (maskTarget b y))[n]? =
      if h : n / (H+1) < i ∧ n % (H+1) = 0 then
        (badge y)[n]?.map (fun a => maskDigit (Bool.xor (title a) (b (⟨n/(H+1),h.1⟩ : Fin i).rev)))
      else (badge y)[n]? := by
  by_cases hj : n / (H+1) < i
  · let j : Fin i := ⟨n/(H+1),hj⟩
    let d : Fin (H+1) := ⟨n%(H+1),Nat.mod_lt _ (by omega)⟩
    have hn : n = j.val*(H+1)+d.val := by
      dsimp [j,d]
      exact (Nat.div_add_mod' n (H+1)).symm
    have atSlot (v : Queue H 0 i) : (badge v)[n]? = (littleSeg (v.2.1 j.rev))[d.val]? := by
      conv_lhs => rw [hn]
      exact badge_segment v j d
    rw [atSlot, atSlot]
    by_cases hd : n%(H+1) = 0
    · rw [dite_eq_left ⟨hj,hd⟩]
      simp [littleSeg, d, hd, maskTarget, j]
    · rw [dite_eq_right (fun h => hd h.2)]
      cases e : d.val with
      | zero => exact (hd e).elim
      | succ d => rfl
  · rw [dite_eq_right (fun h => hj h.1)]
    have hn : i*(H+1) ≤ n := (Nat.le_div_iff_mul_le (by omega)).mp (Nat.le_of_not_gt hj)
    have tail (v : Queue H 0 i) : (badge v)[n]? =
        (most ((flag H).cast v.1)).reverse[n-i*(H+1)]? := by
      rw [badge_partsLE, List.getElem?_append_right (by rwa [segmentsLE_length]), segmentsLE_length]
    exact (tail (maskTarget b y)).trans (tail y).symm

/-- The Boolean mask acting on the first physical binary block. -/
noncomputable def maskBlock {H i : ℕ} (b : Fin i → Bool)
    (y : Block 2 (cap i H 0)) : Block 2 (cap i H 0) :=
  (package H 0 i).cast (maskTarget b ((package H 0 i).cast.symm y))

/-- Lookup on an actual flat P192 block. The segment of the virtual control
word is selected by reversing the physical group number. -/
theorem least_maskBlock {H i : ℕ} (b : Fin i → Bool) (v : Block 2 (cap i H 0)) (n : ℕ) :
    (least (maskBlock b v))[n]? =
      if h : n / (H+1) < i ∧ n % (H+1) = 0 then
        (least v)[n]?.map (fun a => maskDigit (Bool.xor (title a) (b (⟨n/(H+1),h.1⟩ : Fin i).rev)))
      else (least v)[n]? := by
  simpa only [maskBlock, badge, Equiv.apply_symm_apply] using
    badge_maskTarget_slot b ((package H 0 i).cast.symm v) n

/-- The stride-`G` form for a positive physical spacing. -/
theorem least_maskBlock_stride {G i : ℕ} (hG : 0 < G) (b : Fin i → Bool)
    (v : Block 2 (cap i (G-1) 0)) (n : ℕ) :
    (least (maskBlock b v))[n]? =
      if h : n / G < i ∧ n % G = 0 then
        (least v)[n]?.map (fun a => maskDigit (Bool.xor (title a) (b (⟨n/G,h.1⟩ : Fin i).rev)))
      else (least v)[n]? := by
  cases G with
  | zero => omega
  | succ G => exact least_maskBlock b v n

/-- The priced masked XOR on a pair of physical binary blocks. -/
theorem maskedBlockStage {X : Type} {r : Regime X} {l : X → ℕ} (H i : X → ℕ)
    (P G S : X → Tape) (ρ : ℝ) {U : X → Type} (u : (x : X) → Series (U x))
    (b : (x : X) → Pin (P x) → Fin (i x) → Bool)
    (hc : r.Has (tally ∘ extent H (fun _ => 0) i))
    (shape : r.Has fun x => Packed.signs (H x) 0 (i x))
    (sparse : ∀ x, (3 * cap (i x) (H x) 0 + 1) * (32 * i x) ≤ 2 ^ width (H x) 0)
    (hp : Told r P) (hg : Told r G) (hs : Told r S)
    (guard : ∀ x j, j ∈ P x ++ G x ++ S x → j ≤ Net.Shuttle.base)
    (sw : RectInterchange r (extent H (fun _ => 0) i) ρ)
    (ready : Strip.Trace r (fun x => layout (P x)) (fun x a => send (List.ofFn (b x a))))
    (z : ∀ x, (u x).count ≤ l x) (hr : 0 ≤ ρ)
    (f : (x : X) → SpanKey (P x) (G x) (S x) (Block 2 (cap (i x) (H x) 0)) → U x → Bead) :
    let n := extent H (fun _ => 0) i
    let s := fun x => stock 2 (P x) (G x) (S x) (n x)
    Breeze (Spindle.modes n (τ := ρ)) r (fun x => (s x).count) l
      (together r.header (cloth s u f)) (cloth s u fun x a =>
        f x (a.1, maskBlock (b x a.1) a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2)) := by
  let n := extent H (fun _ => 0) i
  let raw := fun x => stock 2 (P x) (G x) (S x) (n x)
  let rows := rotationLayout H (fun _ => 0) i P G S
  let block (x : X) := package (H x) 0 (i x)
  let v (x : X) : Adopt (rows x) (raw x) := (Adopt.same _).split <|
    (block x).split ((Adopt.same _).split ((block x).split (Adopt.same _)))
  have transfer (g : (x : X) → SpanKey (P x) (G x) (S x) (Block 2 (n x)) → U x → Bead) :
      cloth raw u g = cloth rows u (fun x a => g x ((v x).cast a)) := by
    funext x
    exact (v x).packet _
  have w := maskedXorStage H (fun _ => 0) i P G S ρ u b hc shape sparse hp hg hs guard sw ready z hr
    (fun x a => f x ((v x).cast a))
  have hb (x : X) (a : RotationAddress H (fun _ => 0) i P G S x) :
      maskBlock (b x a.1) ((block x).cast a.2.1) =
        (block x).cast (maskTarget (b x a.1) a.2.1) := by simp [maskBlock, block]
  change Breeze _ r (fun x => (raw x).count) l (together _ (cloth raw u f))
    (cloth raw u fun x a => f x (a.1, maskBlock (b x a.1) a.2.1, a.2.2.1, a.2.2.2.1, a.2.2.2.2))
  rw [← funext (fun x => (v x).cost), transfer f, transfer]
  convert w using 1
  apply congrArg (cloth rows u)
  funext x a
  change f x (a.1, maskBlock (b x a.1) ((block x).cast a.2.1), a.2.2.1,
    (block x).cast a.2.2.2.1, a.2.2.2.2) = _
  rw [hb x a]
  rfl


end
end Controlled

end NearSquareRoot
end Computability
end OAI
