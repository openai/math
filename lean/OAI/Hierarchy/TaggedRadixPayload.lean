import OAI.Hierarchy.TaggedRadixApproximation
import OAI.Hierarchy.TaggedSliceFeasible

namespace OAI
/-! # Exposed radix calls at the physical payload widths -/

noncomputable section
namespace Hierarchy.Tagged.Radix

open Filter Catalyst

/-- A record with any fixed number of extra fields can be split across
boundedly many calls with the same tags. -/
theorem resize_record {F : Type*} [Field F] {k t w W M : ℕ} {G : ℝ}
    (hw : 0<w) (hW : 0<W) (fit : w ≤ M*W)
    (X : Approximation F k (pins t W)) (g : X.Gap (coeff F t W) G) :
    ∃ Y : Approximation F k (pins t w), Y.size ≤ M*X.size ∧
      Y.Gap (coeff F t w) (G-2*(k:ℝ)*(M:ℝ)) := by
  obtain ⟨Y,bill,score⟩ := Slices.from_one hw hW X g
  have count := TaggedWidthSlices.count_le hW fit
  refine ⟨Y,bill.trans (Nat.mul_le_mul_right _ count),Approximation.Gap.mono _ score ?_⟩
  have numbers : (TaggedWidthSlices.count w W:ℝ) ≤ M := by exact_mod_cast count
  linarith only [mul_le_mul_of_nonneg_left numbers (show 0≤2*(k:ℝ) by positivity)]

/-- Pin the rounded block width and slice the packed payload. The number of
wide slices is bounded solely in terms of the fixed pack exponent. -/
theorem GridScales.adapt_calls {F : Type*} [Field F] {k h t u : ℕ} {a B G J : ℝ}
    (g : GridScales a B h) (ha : 0<a) (hB : 1<B)
    (ht : 2*digitBits a h ≤ t) (hu : h-packBits B h ≤ u)
    (X : Approximation F k (pins t (width t a))) (Y : Approximation F k (pins u (width u B)))
    (block : X.Gap (coeff F t (width t a)) G) (pack : Y.Gap (coeff F u (width u B)) J) :
    let p := h*2^packBits B h
    let N := ⌈2*(2:ℝ)^B⌉₊
    ∃ X' : Approximation F k (pins t h), ∃ Y' : Approximation F k (pins u p),
      X'.size ≤ X.size ∧ X'.Gap (coeff F t h) G ∧ Y'.size ≤ N*Y.size ∧
        Y'.Gap (coeff F u p) (J-2*(k:ℝ)*(N:ℝ)) := by
  dsimp only
  obtain ⟨X',_,cost,price⟩ := narrower (g.block_width ha ht) X block
  have digit := g.digit_room
  have last := g.last_room
  have hh := g.positive
  have up : 0 < u := by omega
  have cap : 0 < width u B := Nat.ceil_pos.mpr
    (Real.rpow_pos_of_pos (show 0 < (u:ℝ) by exact_mod_cast up) _)
  let p := h*2^(packBits B h)
  let N := ⌈2*(2:ℝ)^B⌉₊
  have paid : p ≤ N*width u B := by
    have realCap := g.pack_width hB hu
    have ceil := Nat.le_ceil (2*(2:ℝ)^B)
    have best := realCap.trans (mul_le_mul_of_nonneg_right ceil (Nat.cast_nonneg _))
    exact_mod_cast best
  have pp : 0 < p := Nat.mul_pos hh (pow_pos (by decide) _)
  obtain ⟨Y',bill,score⟩ := resize_record pp cap paid Y pack
  exact ⟨X',Y',cost,price,bill,score⟩

/-- The stable-sort tiebreak adds the calling address to each record. Both
the local and wide records still need at most c+2 slices at their own widths. -/
theorem GridScales.record_fields {a B : ℝ} {h t u w W c d : ℕ} (g : GridScales a B h)
    (padding : d ≤ h) (localHeight : t ≤ 2*digitBits a h+d)
    (packHeight : u ≤ h-packBits B h+d)
    (localRecord : w ≤ c*h+t) (packedRecord : W ≤ c*(h*2^packBits B h)+u) :
    w ≤ (c+2)*h ∧ W ≤ (c+2)*(h*2^packBits B h) := by
  have last := g.last_room
  have payload : h ≤ h*2^packBits B h := Nat.le_mul_of_pos_right h (pow_pos (by decide) _)
  constructor <;> rw [Nat.add_mul] <;> omega

/-- Both preexisting feasibility bounds provide real networks for the data
width h and the packed width h*2^j. All height and slice choices are uniform. -/
theorem feasible_payloads {F : Type*} [Field F] {k : ℕ} {a B r R : ℝ}
    (ha : 1<a) (hB : 1<B) (blocks : Feasible F k a r) (packs : Feasible F k B R) :
    ∃ A C U V : ℝ, 0<A ∧ 0<C ∧ 0<U ∧ 0<V ∧ ∀ᶠ h : ℕ in atTop,
      ∀ t u : ℕ, 2*digitBits a h ≤ t → h-packBits B h ≤ u →
      let p := h*2^packBits B h
      let N := ⌈2*(2:ℝ)^B⌉₊
      ∃ X : Approximation F k (pins t h), ∃ Y : Approximation F k (pins u p),
        (X.size:ℝ) ≤ A*work t (width t a) r ∧ X.Gap (coeff F t h) (gap C t) ∧
        (Y.size:ℝ) ≤ (N:ℝ)*U*work u (width u B) R ∧
        Y.Gap (coeff F u p) (gap V u-2*(k:ℝ)*(N:ℝ)) := by
  obtain ⟨A,C,U,V,hA,hC,hU,hV,grids⟩ := feasible_grids ha hB blocks packs
  refine ⟨A,C,U,V,hA,hC,hU,hV,?_⟩
  filter_upwards [grids] with h ok
  intro t u ht hu
  obtain ⟨X,Y,xc,xg,yc,yg⟩ := ok.2 t u ht hu
  obtain ⟨X',Y',xs,xg',ys,yg'⟩ := ok.1.adapt_calls (by linarith) hB ht hu X Y xg yg
  refine ⟨X',Y',(by exact_mod_cast xs : (X'.size:ℝ) ≤ X.size).trans xc,xg',?_,yg'⟩
  let N := ⌈2*(2:ℝ)^B⌉₊
  calc
    _ ≤ (N:ℝ)*(Y.size:ℝ) := by exact_mod_cast ys
    _ ≤ (N:ℝ)*(U*work u (width u B) R) := mul_le_mul_of_nonneg_left yc (Nat.cast_nonneg _)
    _ = _ := by ring

/-- The actual exposed calls have the per-pass prices at exponents r/a and R,
after charging all block copies and the packed payload slices. -/
theorem priced_payloads {F : Type*} [Field F] {k : ℕ} {a B r R : ℝ}
    (ha : 1<a) (hB : 1<B) (hr : 0≤r) (hR : 0≤R)
    (blocks : Feasible F k a r) (packs : Feasible F k B R) {K : ℝ} (hK : 0<K) (d : ℕ) :
    ∃ A C U V : ℝ, 0<A ∧ 0<C ∧ 0<U ∧ 0<V ∧ ∀ᶠ h : ℕ in atTop, ∀ (t u : ℕ) (s : ℝ),
      2*digitBits a h ≤ t → t ≤ 2*digitBits a h+d →
      h-packBits B h ≤ u → u ≤ h-packBits B h+d →
      0≤s → s*(2:ℝ)^t ≤ K*(2:ℝ)^h →
      let p := h*2^packBits B h
      ∃ X : Approximation F k (pins t h), ∃ Y : Approximation F k (pins u p),
        s*(X.size:ℝ) ≤ A*work h h (r/a) ∧ X.Gap (coeff F t h) (gap C t) ∧
        (Y.size:ℝ) ≤ U*work h h R ∧
        Y.Gap (coeff F u p) (gap V u-2*(k:ℝ)*(⌈2*(2:ℝ)^B⌉₊:ℝ)) := by
  obtain ⟨A,C,U,V,hA,hC,hU,hV,calls⟩ := feasible_payloads ha hB blocks packs
  let N := (⌈2*(2:ℝ)^B⌉₊:ℝ)
  let localFactor := K*(((2+(d:ℝ))^a+1)*(2+(d:ℝ))^r)
  let wideFactor := (2:ℝ)^d*((1+(d:ℝ))^B+1)*(1+(d:ℝ))^R
  have hN : 0 < N := by
    change (0:ℝ) < (⌈2*(2:ℝ)^B⌉₊:ℝ)
    exact Nat.cast_pos.mpr (Nat.ceil_pos.mpr (by positivity))
  refine ⟨A*localFactor,C,N*U*wideFactor,V,?_,hC,?_,hV,?_⟩
  · dsimp [localFactor]
    positivity
  · dsimp [wideFactor]
    positivity
  filter_upwards [eventual_grid_scales ha hB,calls] with h scales usable
  intro t u s lower upper start finish hs rows
  obtain ⟨X,Y,xc,xg,yc,yg⟩ := usable t u lower start
  have localPrice : s*work t (width t a) r ≤ localFactor*work h h (r/a) :=
    scales.block_batch_price (by linarith) hr hs d upper rows
  have widePrice : work u (width u B) R ≤ wideFactor*work h h R :=
    scales.pack_price hB hR d finish
  refine ⟨X,Y,?_,xg,?_,yg⟩
  · calc
      s*(X.size:ℝ) ≤ s*(A*work t (width t a) r) := mul_le_mul_of_nonneg_left xc hs
      _ = A*(s*work t (width t a) r) := by ring
      _ ≤ A*(localFactor*work h h (r/a)) := mul_le_mul_of_nonneg_left localPrice hA.le
      _ = _ := by ring
  · calc
      (Y.size:ℝ) ≤ (N*U)*work u (width u B) R := yc
      _ ≤ (N*U)*(wideFactor*work h h R) :=
        mul_le_mul_of_nonneg_left widePrice (mul_nonneg (Nat.cast_nonneg _) hU.le)
      _ = _ := by ring

end Hierarchy.Tagged.Radix

end
end OAI
