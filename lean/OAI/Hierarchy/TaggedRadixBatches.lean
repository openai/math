import OAI.Hierarchy.TaggedRadixPayload
import OAI.Hierarchy.TaggedAmplified

namespace OAI
/-! # Amplified radix batches at the parent-height price and gap -/

noncomputable section
namespace Hierarchy.Tagged.Radix

open Filter Real Catalyst CorrectionFrame

private theorem resize {F : Type*} [Field F] {k t w W M : ℕ} {G : ℝ}
    (hM : 0<M) (hW : 0<W) (fit : w ≤ M*W)
    (X : Approximation F k (pins t W)) (g : X.Gap (coeff F t W) G) :
    ∃ Y : Approximation F k (pins t w), Y.size ≤ M*X.size ∧
      Y.Gap (coeff F t w) (G-2*(k:ℝ)*(M:ℝ)) := by
  rcases Nat.eq_zero_or_pos w with rfl | hw
  · obtain ⟨Y,_,size,price⟩ := narrower (Nat.zero_le W) X g
    exact ⟨Y,size.trans (Nat.le_mul_of_pos_left _ hM),Approximation.Gap.mono _ price
      (sub_le_self _ (by positivity))⟩
  · exact resize_record hw hW fit X g

/-- Uniform physical circuits for every occupied local batch and wide pack
call at every pass. The costs include all record slicing and sparse correction.
Both calls leave twice the target gap for substitution into the pass network. -/
theorem priced_batches {F : Type*} [Field F] {k : ℕ} {a B r R : ℝ}
    (ha : 1<a) (hB : 1<B) (hr : 0≤r) (hR : 0≤R)
    (blocks : Feasible F k a r) (packs : Feasible F k B R)
    {K : ℝ} (hK : 0<K) (c d : ℕ) :
    ∃ A U D : ℝ, 0<A ∧ 0<U ∧ 6≤D ∧ ∀ᶠ h : ℕ in atTop,
      ∀ t u s w W : ℕ, 2*digitBits a h ≤ t → t ≤ 2*digitBits a h+d →
      h-packBits B h ≤ u → u ≤ h-packBits B h+d →
      (2:ℝ)^h ≤ (s:ℝ)*(2:ℝ)^t → (s:ℝ)*(2:ℝ)^t ≤ K*(2:ℝ)^h →
      w ≤ c*h → W ≤ c*(h*2^packBits B h) →
      ∃ X : Approximation F k (s*pins t w), ∃ Y : Approximation F k (pins u W),
        (X.size:ℝ) ≤ A*work h h (r/a) ∧ X.Gap (dataProduct s (coeff F t w)) (2*gap D h) ∧
        (Y.size:ℝ) ≤ U*work h h R ∧ Y.Gap (coeff F u W) (2*gap D h) := by
  obtain ⟨A,C,U,V,hA,hC,hU,hV,payloads⟩ := priced_payloads ha hB hr hR blocks packs hK d
  obtain ⟨amp,amplify⟩ := amplified_batches F
  let M := c+1
  let L := 2*(k:ℝ)*(M:ℝ)
  let J := 2*(k:ℝ)*(⌈2*(2:ℝ)^B⌉₊:ℝ)+L
  let D := max 6 (max C (V+1))
  have hD : 6 ≤ D := le_max_left _ _
  have localMargin : C ≤ D := (le_max_left _ _).trans (le_max_right _ _)
  have wideMargin : V < D :=
    lt_of_lt_of_le (by linarith : V < V+1) ((le_max_right _ _).trans (le_max_right _ _))
  have positiveM : 0 < M := by dsimp [M]; omega
  have realM : 0 < (M:ℝ) := by exact_mod_cast positiveM
  have budget := eventual_packing_gaps_with_losses ha hB hD localMargin hV.le wideMargin
    (m:=1) zero_lt_one (K:=1) zero_le_one d k L J
  have uniform := eventual_grid_components ha hB (amplify (a+1) (by linarith))
    (Filter.Eventually.of_forall (fun _ : ℕ => True.intro))
  refine ⟨((amp:ℝ)+1)*(M:ℝ)*A,(M:ℝ)*U,D,by positivity,by positivity,hD,?_⟩
  filter_upwards [payloads,eventual_grid_scales ha hB,budget,uniform,
    (tendsto_natCast_atTop_atTop (R:=ℝ)).eventually_ge_atTop (logb 2 K)]
    with h placed scales margins power logK
  intro t u s w W tlo thi ulo uhi filled slots nw nW
  have hs : 0<s := by
    by_contra! zero
    have eq : s=0 := by omega
    have bad : (2:ℝ)^h ≤ 0 := by simpa only [eq,Nat.cast_zero,zero_mul] using filled
    exact (by positivity : (0:ℝ)<2^h).not_ge bad
  have hh := scales.positive
  let p := h*2^(packBits B h)
  have pp : 0 < p := Nat.mul_pos hh (pow_pos (by decide) _)
  obtain ⟨X,Y,xc,xg,yc,yg⟩ := placed t u s tlo thi ulo uhi (Nat.cast_nonneg _) slots
  have cM : c ≤ M := Nat.le_succ _
  obtain ⟨X',xsize,xprice⟩ := resize positiveM hh
    (nw.trans (Nat.mul_le_mul_right _ cM)) X xg
  obtain ⟨Y',ysize,yprice⟩ := resize positiveM pp
    (nW.trans (Nat.mul_le_mul_right p cM)) Y yg
  let H := (((t+1)^2:ℕ):ℝ)
  have eqH : H = ((t:ℝ)+1)^2 := by simp [H]
  have Hpos : 0 < H := by rw [eqH]; positivity
  obtain ⟨localGap,wideGap,threshold⟩ := margins t u s H tlo thi ulo (by simpa only [one_mul] using filled)
    Hpos (by rw [eqH,one_mul])
  have callSize := scales.batch_log (by linarith) hK logK tlo hs slots
  obtain ⟨Z,_,zsize,zgap⟩ := (power t u tlo ulo).1 X' hs callSize xprice threshold
  refine ⟨Z,Y',?_,Approximation.Gap.mono _ zgap localGap,?_,Approximation.Gap.mono _ yprice ?_⟩
  · have natural := zsize.trans (Nat.mul_le_mul_left (amp*s) xsize)
    have cost : (Z.size:ℝ) ≤ (amp:ℝ)*(s:ℝ)*((M:ℝ)*(X.size:ℝ)) := by exact_mod_cast natural
    calc
      _ ≤ ((amp:ℝ)+1)*(M:ℝ)*((s:ℝ)*(X.size:ℝ)) := by
        linarith only [cost,mul_nonneg realM.le
          (mul_nonneg (Nat.cast_nonneg (α:=ℝ) s) (Nat.cast_nonneg (α:=ℝ) X.size))]
      _ ≤ ((amp:ℝ)+1)*(M:ℝ)*(A*work h h (r/a)) := mul_le_mul_of_nonneg_left xc (by positivity)
      _ = _ := by ring
  · have cost : (Y'.size:ℝ) ≤ (M:ℝ)*(Y.size:ℝ) := by exact_mod_cast ysize
    exact cost.trans (by simpa only [mul_assoc] using mul_le_mul_of_nonneg_left yc realM.le)
  · change 2*gap D h ≤ gap V u - (2*(k:ℝ)*(⌈2*(2:ℝ)^B⌉₊:ℝ))-L
    simpa only [J,sub_add_eq_sub_sub] using wideGap

end Hierarchy.Tagged.Radix

end
end OAI
