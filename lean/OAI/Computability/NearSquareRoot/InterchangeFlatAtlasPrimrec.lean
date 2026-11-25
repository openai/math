import OAI.Computability.NearSquareRoot.InterchangeFlatAtlasCheck

/-! # Primitive recursion of flat chart lookups -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatAtlas

open Opcode

variable {X : Type} [Primcodable X]

private theorem primrec_toNat {s : X → Bool} (hs : Primrec s) : Primrec fun x => (s x).toNat := by
  apply (Primrec.cond hs (Primrec.const 1) (Primrec.const 0)).of_eq
  intro x
  cases s x <;> rfl

local macro "index_pr" : tactic => `(tactic|
  repeat' first | assumption | exact Primrec.const _
                | apply Primrec.nat_add.comp | apply Primrec.nat_mul.comp | apply primrec_toNat)

theorem primrec_labelIdx {m L j v : X → ℕ} {s : X → Bool}
    (hm : Primrec m) (hL : Primrec L) (hs : Primrec s) (hj : Primrec j) (hv : Primrec v) :
    Primrec fun x => labelIdx (m x) (L x) (s x) (j x) (v x) := by
  unfold labelIdx
  index_pr

theorem primrec_commonIdx {m L T j t : X → ℕ}
    (hm : Primrec m) (hL : Primrec L) (hT : Primrec T) (hj : Primrec j) (ht : Primrec t) :
    Primrec fun x => commonIdx (m x) (L x) (T x) (j x) (t x) := by
  unfold commonIdx
  index_pr

theorem primrec_prepareIdx {m L T v t : X → ℕ} {s : X → Bool}
    (hm : Primrec m) (hL : Primrec L) (hT : Primrec T) (hs : Primrec s) (hv : Primrec v) (ht : Primrec t) :
    Primrec fun x => prepareIdx (m x) (L x) (T x) (s x) (v x) (t x) := by
  unfold prepareIdx
  index_pr

theorem primrec_localIdx {m L T j v t : X → ℕ} {s : X → Bool}
    (hm : Primrec m) (hL : Primrec L) (hT : Primrec T) (hs : Primrec s) (hj : Primrec j)
    (hv : Primrec v) (ht : Primrec t) :
    Primrec fun x => localIdx (m x) (L x) (T x) (s x) (j x) (v x) (t x) := by
  unfold localIdx
  index_pr

theorem primrec_maskIdx {L T t v : X → ℕ} {s : X → Bool}
    (hL : Primrec L) (hT : Primrec T) (hs : Primrec s) (ht : Primrec t) (hv : Primrec v) :
    Primrec fun x => maskIdx (L x) (T x) (s x) (t x) (v x) := by
  unfold maskIdx
  index_pr

theorem primrec_chart {A : X → List Word} {i : X → ℕ} (hA : Primrec A) (hi : Primrec i) :
    Primrec fun x => chart (A x) (i x) := (Primrec.list_getD []).comp hA hi

theorem primrec_mask {bits : X → List Bool} {L T t v : X → ℕ} {s : X → Bool}
    (hbits : Primrec bits) (hL : Primrec L) (hT : Primrec T) (hs : Primrec s) (ht : Primrec t)
    (hv : Primrec v) : Primrec fun x => mask (bits x) (L x) (T x) (s x) (t x) (v x) :=
  (Primrec.list_getD false).comp hbits (primrec_maskIdx hL hT hs ht hv)

theorem primrec_allN {k : X → ℕ} {f : X → ℕ → Bool} (hk : Primrec k)
    (hf : Primrec fun z : X × ℕ => f z.1 z.2) : Primrec fun x => allN (k x) (f x) :=
  Opcode.primrec_range_all hk hf

private theorem primrec_sides {f : X → Bool → Bool} (hf : Primrec fun x => f x false)
    (ht : Primrec fun x => f x true) : Primrec fun x => sides (f x) := Primrec.and.comp hf ht

private theorem primrec_pivot {i : X → ℕ} (hi : Primrec i) : Primrec fun x => pivot (i x) :=
  (Primrec.const 2).pair (((Primrec.const false).pair hi).pair
    (((Primrec.const true).pair hi).pair (Primrec.const (false,0,1))))

theorem primrec_shape {b a m limit i : X → ℕ} {A : X → List Word}
    (hb : Primrec b) (ha : Primrec a) (hm : Primrec m) (hA : Primrec A) (hc : Primrec limit)
    (hi : Primrec i) : Primrec fun x => shape (b x) (a x) (m x) (A x) (limit x) (i x) := by
  have h := primrec_chart hA hi
  exact Primrec.and.comp (primrec_admissible hb (Primrec.nat_add.comp (Primrec.nat_add.comp ha hm) ha) h)
    (Primrec.nat_le.comp (primrec_price.comp h) hc).decide

theorem primrec_edge {a m L T j v t : X → ℕ} {A : X → List Word} {s : X → Bool}
    (ha : Primrec a) (hm : Primrec m) (hL : Primrec L) (hT : Primrec T) (hA : Primrec A)
    (hs : Primrec s) (hj : Primrec j) (hv : Primrec v) (ht : Primrec t) :
    Primrec fun x => edge (a x) (m x) (L x) (T x) (A x) (s x) (j x) (v x) (t x) := by
  unfold edge
  apply primrec_equal (Primrec.nat_add.comp (Primrec.nat_add.comp ha hm) ha)
  · exact Primrec.list_append.comp (Primrec.list_append.comp
      (primrec_chart hA (primrec_prepareIdx hm hL hT hs hv ht))
      (primrec_chart hA (primrec_localIdx hm hL hT hs hj hv ht)))
      (primrec_chart hA (primrec_commonIdx hm hL hT hj ht))
  · exact primrec_chart hA (primrec_labelIdx hm hL hs hj hv)

theorem primrec_diag {a m L j v : X → ℕ} {A : X → List Word}
    (ha : Primrec a) (hm : Primrec m) (hL : Primrec L) (hA : Primrec A) (hj : Primrec j)
    (hv : Primrec v) : Primrec fun x => diag (a x) (m x) (L x) (A x) (j x) (v x) := by
  unfold diag
  apply primrec_equal (Primrec.nat_add.comp (Primrec.nat_add.comp ha hm) ha)
  · exact Primrec.list_cons.comp (primrec_pivot (Primrec.nat_add.comp ha hj))
      (primrec_chart hA (primrec_labelIdx hm hL (Primrec.const true) hj hv))
  · exact primrec_chart hA (primrec_labelIdx hm hL (Primrec.const false) hj hv)

private theorem primrec_prev {Y Z : Type} [Primcodable Y] [Primcodable Z] {f : X → Z}
    (hf : Primrec f) : Primrec fun z : X × Y => f z.1 := hf.comp Primrec.fst

private theorem lift₂ {Z : Type} [Primcodable Z] {f : X → Z} (hf : Primrec f) :
    Primrec fun z : (X × ℕ) × ℕ => f z.1.1 := primrec_prev (primrec_prev hf)

private theorem lift₃ {Z : Type} [Primcodable Z] {f : X → Z} (hf : Primrec f) :
    Primrec fun z : ((X × ℕ) × ℕ) × ℕ => f z.1.1.1 := primrec_prev (lift₂ hf)

/-- Uniform in all five dimensions, every incidence, and all stored chart instructions. -/
theorem primrec_valid {b a m L T : X → ℕ} {bits : X → List Bool} {A : X → List Word}
    (hb : Primrec b) (ha : Primrec a) (hm : Primrec m) (hL : Primrec L) (hT : Primrec T)
    (hbits : Primrec bits) (hA : Primrec A) :
    Primrec fun x => valid (b x) (a x) (m x) (L x) (T x) (bits x) (A x) := by
  have limit : Primrec fun x => 54*(a x+2) :=
    Primrec.nat_mul.comp (.const 54) (Primrec.nat_add.comp ha (.const 2))
  have labels (s : Bool) : Primrec fun x => allN (m x) fun j => allN (L x) fun v =>
      shape (b x) (a x) (m x) (A x) (54*(a x+2)) (labelIdx (m x) (L x) s j v) := by
    apply primrec_allN hm
    apply primrec_allN (primrec_prev hL)
    exact primrec_shape (lift₂ hb) (lift₂ ha) (lift₂ hm) (lift₂ hA) (lift₂ limit)
      (primrec_labelIdx (lift₂ hm) (lift₂ hL) (.const s) (primrec_prev .snd) .snd)
  have common : Primrec fun x => allN (m x) fun j => allN (T x) fun t =>
      shape (b x) (a x) (m x) (A x) (54*(a x+2)) (commonIdx (m x) (L x) (T x) j t) := by
    apply primrec_allN hm
    apply primrec_allN (primrec_prev hT)
    exact primrec_shape (lift₂ hb) (lift₂ ha) (lift₂ hm) (lift₂ hA) (lift₂ limit)
      (primrec_commonIdx (lift₂ hm) (lift₂ hL) (lift₂ hT) (primrec_prev .snd) .snd)
  have prepare (s : Bool) : Primrec fun x => allN (L x) fun v => allN (T x) fun t =>
      !mask (bits x) (L x) (T x) s t v ||
        shape (b x) (a x) (m x) (A x) (54*(a x+2)) (prepareIdx (m x) (L x) (T x) s v t) := by
    apply primrec_allN hL
    apply primrec_allN (primrec_prev hT)
    apply Primrec.or.comp
    · exact Primrec.not.comp (primrec_mask (lift₂ hbits) (lift₂ hL) (lift₂ hT) (.const s) .snd (primrec_prev .snd))
    · exact primrec_shape (lift₂ hb) (lift₂ ha) (lift₂ hm) (lift₂ hA) (lift₂ limit)
        (primrec_prepareIdx (lift₂ hm) (lift₂ hL) (lift₂ hT) (.const s) (primrec_prev .snd) .snd)
  have localMaps (s : Bool) : Primrec fun x => allN (m x) fun j => allN (L x) fun v => allN (T x) fun t =>
      !mask (bits x) (L x) (T x) s t v ||
        (shape (b x) (a x) (m x) (A x) 0 (localIdx (m x) (L x) (T x) s j v t) &&
          edge (a x) (m x) (L x) (T x) (A x) s j v t) := by
    apply primrec_allN hm
    apply primrec_allN (primrec_prev hL)
    apply primrec_allN (primrec_prev (primrec_prev hT))
    apply Primrec.or.comp
    · exact Primrec.not.comp (primrec_mask (lift₃ hbits) (lift₃ hL) (lift₃ hT) (.const s) .snd (primrec_prev .snd))
    · apply Primrec.and.comp
      · exact primrec_shape (lift₃ hb) (lift₃ ha) (lift₃ hm) (lift₃ hA) (.const 0)
          (primrec_localIdx (lift₃ hm) (lift₃ hL) (lift₃ hT) (.const s) (lift₂ .snd) (primrec_prev .snd) .snd)
      · exact primrec_edge (lift₃ ha) (lift₃ hm) (lift₃ hL) (lift₃ hT) (lift₃ hA) (.const s)
          (lift₂ .snd) (primrec_prev .snd) .snd
  have diagonal : Primrec fun x => allN (m x) fun j => allN (L x) fun v =>
      diag (a x) (m x) (L x) (A x) j v := by
    apply primrec_allN hm
    apply primrec_allN (primrec_prev hL)
    exact primrec_diag (lift₂ ha) (lift₂ hm) (lift₂ hL) (lift₂ hA) (primrec_prev .snd) .snd
  unfold valid
  repeat' first | exact common | exact diagonal | exact primrec_sides (labels false) (labels true)
                | exact primrec_sides (prepare false) (prepare true)
                | exact primrec_sides (localMaps false) (localMaps true) | apply Primrec.and.comp

end FlatAtlas

end NearSquareRoot
end Computability
end OAI
