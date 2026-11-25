import OAI.Computability.IntegerMultiplication.Thin.Exchange
import OAI.Computability.NearSquareRoot.BoundedProgram

/-! # A finite map on two separated address fields

P192's fixed-field lifts expose both selected bits at the front. Their four long
slices can then be rearranged by any prescribed two-bit gate and lowered back into
place. All work is linear in the physical bit volume, including for width-one payloads.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Thin

private theorem staticPrefix {I X : Type} {w : I → ℝ} {z : I → Tree} {S : I → Type}
    (x : Series X) (s : (i : I) → Series (S i)) (hs : Rim w z s) (perm : X → X)
    (f : (i : I) → X × S i → Tree)
    (h : Carries w z (stackRun (fun i => x.cart (s i)) f)) :
    Carries w z (stackRun (fun i => x.cart (s i)) (fun i a => f i (perm a.1,a.2))) := by
  obtain ⟨D, size⟩ := hs.pay.rate s
  have area : ∃ B : ℕ, ∀ i, (x.count+1:ℝ)*((s i).count+1) ≤ (B:ℝ)*w i := by
    refine ⟨(x.count+1)*(D+1),fun i => ?_⟩
    push_cast
    have b := h.budget i
    have sz := size i
    calc
      _ ≤ (x.count+1:ℝ)*(D*w i + w i) := by gcongr
      _ = _ := by ring
  have rows := carve (fun _ : I => x) s f h
    ((fixture h.small h.budget (send (tally x.count))).twice hs.pay) area
  have moved := finite_series x (fun i j => stripe (s i) (fun a => f i (perm j,a)))
    h.small h.budget (fun j => finite_cell x _ rows (perm j))
  exact flatten (fun _ : I => x) s _ moved

variable {I X : Type} {w : I→ℝ} {z : I→Tree} {S T U : I→Type}
variable (p : (i:I)→Series (S i)) (g : (i:I)→Series (T i)) (b : (i:I)→Series (U i))
    (x : Series X) (qx : 1 ≤ x.count)
    (s : Rim w z p) (t : Rim w z g) (u : Rim w z b)
    (fit : ∃ D:ℕ,∀ i,((p @@ g @@ b) i).count ≤ (D:ℝ)*w i)

include qx s t u fit in
/-- A constant finite gate on two separated fields, with all intervening data carried
intact. The input supplies the three real range tallies. -/
theorem elementaryGate (gate : X × X → X × X)
    (a : (i:I)→S i× X×T i×X×U i→Tree)
    (h : Carries w z (stackRun (p @@ sr x @@ g @@ sr x @@ b) a)) :
    Carries w z (stackRun (p @@ sr x @@ g @@ sr x @@ b)
      (fun i v => let gateBits := gate (v.2.1,v.2.2.2.1)
                  a i (v.1,gateBits.1,v.2.2.1,gateBits.2,v.2.2.2.2))) := by
  have raw : ∃ D:ℕ,∀ i,((g @@ b) i).count ≤ (D:ℝ)*w i := by
    obtain ⟨D,e⟩ := fit
    refine ⟨D,fun i=>le_trans ?_ (e i)⟩
    have := s.li i
    change ((g i).cart (b i)).count ≤ (((p i).cart ((g i).cart (b i))).count:ℝ)
    rw [Series.count_cart (p i)]; push_cast
    apply le_mul_of_one_le_left (by positivity)
    exact_mod_cast this
  obtain ⟨D,e⟩ := fit
  let E := x.count * D
  have raw₀ (i:I) : (p i).count*(g i).count*(x.count:ℝ)*(b i).count ≤ (E:ℝ)*w i := by
    specialize e i
    simp only [fusion,Series.count_cart,Nat.cast_mul] at e
    unfold E; push_cast
    have j := mul_le_mul_of_nonneg_left e (Nat.cast_nonneg (α:=ℝ) x.count)
    nlinarith
  let R := sr (I:=I) x
  have a₀ := Rim.fixR _ t x qx
  -- combine XG by associating p x g (x b) -> p (x g) (x b)
  let a₁ (i:I) (j : S i×(X×T i)×X×U i) := a i (j.1,j.2.1.1,j.2.1.2,j.2.2)
  have f₁ : Carries w z (stackRun (p @@ (R @@ g) @@ R @@ b) a₁) := by
    let d i := (Adopt.same (p i)).split (Adopt.rotate x (g i) (x.cart (b i)))
    have e (i:I) :
        stripe ((p @@ R @@ g @@ R @@ b) i) (a i)=
        stripe ((p @@ (R @@ g) @@ R @@ b) i) (a₁ i) := (d i).packet _
    change Carries w z (stackRun (p @@ R @@ g @@ R @@ b) a) at h
    unfold stackRun at h ⊢; simp_rw [← e]; exact h
  have d₁ : ∃ D:ℕ,∀ i,((p @@ (R @@ g) @@ b) i).count ≤ (D:ℝ)*w i := by
    refine ⟨E,fun i=>?_⟩
    specialize raw₀ i
    simp only [fusion,R,sr,Series.count_cart,Nat.cast_mul]; nlinarith
  have y := mount p (R @@ g) b x qx s a₀ u d₁ a₁ f₁
  let a₂ (i:I) (j:X×S i×X×T i×U i) := a i (j.2.1,j.2.2.1,j.2.2.2.1,j.1,j.2.2.2.2)
  have y₂ : Carries w z (stackRun (R @@ p @@ R @@ g @@ b) a₂) := by
    unfold stackRun
    have e (i:I) :
        stripe ((R @@ p @@ R @@ g @@ b) i) (a₂ i)=
        stripe ((R @@ p @@ (R @@ g) @@ b) i)
          (fun j=> a₁ i (j.2.1,j.2.2.1,j.1,j.2.2.2)) :=
      ((Adopt.same _).split ((Adopt.same _).split (Adopt.rotate ..))).packet _
    simp_rw [e]; exact y
  have M : Rim w z R := Rim.rigid x h.small h.budget qx
  have a₃ := rimProd t u raw
  have d₂ : ∃ D:ℕ,∀ i, ((R @@ p @@ (g @@ b)) i).count ≤ (D:ℝ)*w i := by
    refine ⟨E,fun i=>?_⟩
    specialize raw₀ i
    simp only [fusion,R,sr,Series.count_cart,Nat.cast_mul]; nlinarith
  have y₃ := mount R p (g @@ b) x qx M s a₃ d₂ a₂ y₂
  -- [Xl Xr P G B], combine PG
  let a₄ (i:I) (j:X×X×(S i×T i)×U i) := a i (j.2.2.1.1,j.1,j.2.2.1.2,j.2.1,j.2.2.2)
  have y₄ : Carries w z (stackRun (R @@ R @@ (p @@ g) @@ b) a₄) := by
    unfold stackRun at *
    have e (i:I) :
        stripe ((R @@ R @@ p @@ g @@ b) i)
          (fun (j:X×X×S i×T i×U i)=> a i (j.2.2.1,j.1,j.2.2.2.1,j.2.1,j.2.2.2.2))=
        stripe ((R @@ R @@ (p @@ g) @@ b) i) (a₄ i) :=
      ((Adopt.same _).split ((Adopt.same _).split (Adopt.rotate ..))).packet _
    simp_rw [← e]; exact y₃
  have pgBound : ∃ D : ℕ, ∀ i, ((p @@ g) i).count ≤ (D:ℝ)*w i := by
    refine ⟨D,fun i => le_trans ?_ (e i)⟩
    simp only [fusion,Series.count_cart,Nat.cast_mul]
    have hb : (1:ℝ) ≤ (b i).count := by exact_mod_cast u.li i
    nlinarith only [mul_le_mul_of_nonneg_left hb (show 0 ≤ ((p i).count : ℝ) * (g i).count by positivity)]
  have M' := rimProd s t pgBound
  have e₄ : ∃ D:ℕ,∀ i, ((R @@ (p @@ g) @@ b) i).count ≤ (D:ℝ)*w i := by
    refine ⟨E,fun i=> ?_⟩
    specialize raw₀ i
    simp only [fusion,R,sr,Series.count_cart,Nat.cast_mul]; nlinarith
  let fused := (p @@ g) @@ b
  have together : Rim w z fused := rimProd M' u ⟨D,fun i => by
    simpa only [fusion,Series.count_cart,Nat.cast_mul,mul_assoc] using e i⟩
  let flat (i : I) (v : (X × X) × (S i × T i) × U i) :=
    a₄ i (v.1.1,v.1.2,v.2)
  let rows (i : I) := Adopt.rotate x x (fused i)
  have group : Carries w z (stackRun (fun i => (x.cart x).cart (fused i)) flat) := by
    have eq (i : I) : stripe ((R @@ R @@ (p @@ g) @@ b) i) (a₄ i) =
      stripe ((x.cart x).cart (fused i)) (flat i) := (rows i).packet _
    unfold stackRun at *
    simp_rw [← eq]
    exact y₄
  let bits (i : I) (v : X × X × (S i × T i) × U i) :=
    a i (v.2.2.1.1,(gate (v.2.1,v.1)).1,v.2.2.1.2,(gate (v.2.1,v.1)).2,v.2.2.2)
  have lifted := staticPrefix (x.cart x) fused together (fun c => gate c.swap) flat group
  have changed : Carries w z (stackRun (R @@ R @@ (p @@ g) @@ b) bits) := by
    have eq (i : I) : stripe ((R @@ R @@ (p @@ g) @@ b) i) (bits i) =
        stripe ((x.cart x).cart (fused i)) (fun v => flat i (gate v.1.swap,v.2)) := (rows i).packet _
    unfold stackRun at *
    simp_rw [eq]
    exact lifted
  have y₅ := slide R (p @@ g) b x qx M M' u e₄ bits changed
  -- now Xr (PG) Xl b. expand PG
  let a₆ (i:I) (j:X×S i×T i×X×U i) := a i (j.2.1,(gate (j.1,j.2.2.2.1)).1,j.2.2.1,(gate (j.1,j.2.2.2.1)).2,j.2.2.2.2)
  have y₆ : Carries w z (stackRun (R @@ p @@ g @@ R @@ b) a₆) := by
    unfold stackRun
    have e (i:I) :
        stripe ((R @@ p @@ g @@ R @@ b) i) (a₆ i) =
        stripe ((R @@ (p @@ g) @@ R @@ b) i)
          (fun j=> bits i (j.2.2.1,j.1,j.2.1,j.2.2.2)) :=
      ((Adopt.same _).split (Adopt.rotate ..)).packet _
    simp_rw [e]; exact y₅
  have e₆ : ∃ D:ℕ,∀ i, ((g @@ R @@ b) i).count ≤ (D:ℝ)*w i := by
    refine ⟨E,fun i=> ?_⟩
    have hv : (1:ℝ)≤(p i).count := by exact_mod_cast s.li i
    calc
     _ ≤ (((p @@ g @@ R @@ b) i).count:ℝ) := by
      simp only [fusion,R,sr,Series.count_cart,Nat.cast_mul]
      exact le_mul_of_one_le_left (by positivity) hv
     _ ≤ _ := by
      specialize raw₀ i
      simpa only [fusion,R,sr,Series.count_cart,Nat.cast_mul,mul_assoc] using raw₀
  have k₀ := rimProd t (Rim.fixR _ u x qx) e₆
  have e₇ : Rim w z (p @@ g @@ R @@ b) := by
    apply rimProd s k₀; refine ⟨E,fun i=>?_⟩
    specialize raw₀ i
    simpa only [fusion,R,sr,Series.count_cart,Nat.cast_mul,mul_assoc] using raw₀
  exact trail p _ x s k₀ e₇ a₆ y₆ qx

end Controlled

end NearSquareRoot
end Computability
end OAI
