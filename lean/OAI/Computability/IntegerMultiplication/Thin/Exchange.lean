import OAI.Computability.IntegerMultiplication.Thin.Rank

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Thin
open Strip Code Code.Task
variable {I X Y : Type} {w : I→ℝ} {z : I→Tree}
variable {S T U V : I→Type}
variable (p : (i:I)→Series (S i)) (g:(i:I)→Series (T i))
    (b : (i:I)→Series (U i))
-- shorthand
abbrev fusion {A B : I→Type} (x : (i:I)→Series (A i)) (v : (i:I)→Series (B i)) (i:I) := (x i).cart (v i)
infixr:66 " @@ " => fusion
theorem rimProd {A B:I→Type} {p : (i:I)→Series (A i)} {g : (i:I)→Series (B i)}
    (s : Rim w z p) (t : Rim w z g)
    (n : ∃ D:ℕ,∀ i,(fusion p g i).count ≤ (D:ℝ)*w i) :
    Rim w z (fusion p g) := Rim.mulR p g s t (by simpa only [fusion,Series.count_cart,Nat.cast_mul] using n)

private theorem adjust {A B C:I→Type} (p:(i:I)→Series (A i)) (b:(i:I)→Series (B i)) (g:(i:I)→Series (C i))
    (u:(i:I)→ A i× B i×C i→Tree) :
    stackRun (p @@ b @@ g) u = stackRun ((p @@ b) @@ g)
      (fun i x => u i (x.1.1,x.1.2,x.2)) := by
  funext; exact (Adopt.rotate ..).packet _

-- transpose X across two under any rest
variable (x:Series X) (qx : 1≤x.count)
abbrev sr (_i:I) := x
omit qx
variable (s : Rim w z p) (t : Rim w z g) (u : Rim w z b)
    (fit : ∃ D:ℕ,∀ i,((p @@ g @@ b) i).count ≤ (D:ℝ)*w i)
-- adjust syntax pipe
include qx s t u fit
omit qx s t in
private theorem boundS :
    ∃ D:ℕ,∀ i,((p @@ g) i).count ≤ (D:ℝ)*w i := by
  obtain ⟨D,e⟩ := fit
  refine ⟨D,fun i=> le_trans ?_ (e i)⟩
  have f := u.li i
  simp only [fusion,Series.count_cart,Nat.cast_mul]
  gcongr
  exact_mod_cast Nat.le_mul_of_pos_right _ f

/-- raise static past two -/
theorem mount
    (a : (i:I)→S i × T i × X × U i→Tree)
    (h : Carries w z (stackRun (p @@ g @@ sr x @@ b) a)) :
    Carries w z (stackRun (sr x @@ p @@ g @@ b)
      (fun i v=> a i (v.2.1,v.2.2.1,v.1,v.2.2.2))) := by
  rw [adjust p g] at h
  have n := rimProd s t (boundS p g b u fit)
  have k : Rim w z (fusion (fusion p g) b) := by
    apply rimProd n u
    simpa only [fusion,Series.count_cart,Nat.cast_mul,mul_assoc] using fit
  have A := antTrail (fusion p g) b x n u k _ h qx
  have v (i) := ((Adopt.same x).split (Adopt.rotate (p i) (g i) (b i))).packet
  unfold stackRun
  simp_rw [v]
  exact A

theorem slide
    (a : (i:I)→ X × S i × T i × U i→Tree)
    (h : Carries w z (stackRun (sr x @@ p @@ g @@ b) a)) :
    Carries w z (stackRun (p @@ g @@ sr x @@ b)
      (fun i v => a i (v.2.2.1,v.1,v.2.1,v.2.2.2))) := by
  rw [adjust p g]
  have n := rimProd s t (boundS p g b u fit)
  have k : Rim w z (fusion (fusion p g) b) := by
    apply rimProd n u
    simpa only [fusion,Series.count_cart,Nat.cast_mul,mul_assoc] using fit
  let a₀ (i:I) (v:X × (S i× T i)× U i) := a i (v.1,v.2.1.1,v.2.1.2,v.2.2)
  have v (i) := ((Adopt.same x).split (Adopt.rotate (p i) (g i) (b i))).packet (a i)
  exact trail (fusion p g) b x n u k a₀ (by unfold stackRun fusion; unfold stackRun fusion sr at h; simp_rw [v] at h; exact h) qx

-- p x g x b -> P x₂ g x₁ b
theorem skew
    (a : (i:I)→S i× X×T i×X×U i→Tree)
    (h : Carries w z (stackRun (p @@ sr x @@ g @@ sr x @@ b) a)) :
    Carries w z (stackRun (p @@ sr x @@ g @@ sr x @@ b)
      (fun i v=> a i (v.1,v.2.2.2.1,v.2.2.1,v.2.1,v.2.2.2.2))) := by
  -- mount right X across p+XG; mount left X past X2+P ; slide X1 past X2+PG ; trail X2 past P
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
  have M' := rimProd s t (boundS p g b u ⟨_,e⟩)
  have e₄ : ∃ D:ℕ,∀ i, ((R @@ (p @@ g) @@ b) i).count ≤ (D:ℝ)*w i := by
    refine ⟨E,fun i=> ?_⟩
    specialize raw₀ i
    simp only [fusion,R,sr,Series.count_cart,Nat.cast_mul]; nlinarith
  have y₅ := slide R (p @@ g) b x qx M M' u e₄ a₄ y₄
  -- now Xr (PG) Xl b. expand PG
  let a₆ (i:I) (j:X×S i×T i×X×U i) := a i (j.2.1,j.2.2.2.1,j.2.2.1,j.1,j.2.2.2.2)
  have y₆ : Carries w z (stackRun (R @@ p @@ g @@ R @@ b) a₆) := by
    unfold stackRun
    have e (i:I) :
        stripe ((R @@ p @@ g @@ R @@ b) i) (a₆ i) =
        stripe ((R @@ (p @@ g) @@ R @@ b) i)
          (fun j=> a₄ i (j.2.2.1,j.1,j.2.1,j.2.2.2)) :=
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
end Thin

end IntegerMultiplication
end Computability
end OAI
