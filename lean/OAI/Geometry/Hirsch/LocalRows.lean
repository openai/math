import OAI.Geometry.Hirsch.Stencil

noncomputable section

namespace OAI.Geometry.Hirsch.Layer

open Forest

variable {I : Type} {L V B : ℕ} {code : Bundles L V} {par : Parameters code}
  {data : SampleData par} {D : ℝ} {b : Fin B} {i : I} {x : Space I B V}

def Standard (data : SampleData par) (D : ℝ) (b : Fin B) (i : I) (x : Space I B V) :=
  ∀ r, bound data D b r ≤ standard par i r x

theorem Standard.lower (hs : Standard data D b i x) (l : Fin V) : D/2 ≤ W i l x :=
  hs (.inl (none,false,l))

theorem Standard.prices (hs : Standard data D b i x)
    (hc : Expanded data.cuts par.M (adjusted data D (widths i x))) :
    data.Prices (adjusted data D (widths i x)) (fun l => P i l x - D) := by
  refine ⟨fun l => ?_,hc,fun l => ?_,fun l => ?_,fun e => ?_⟩
  · change -data.shift ≤ W i l x - D/2 - data.shift
    linarith [hs.lower l]
  · have hh : D - par.K*par.eps ≤ P i l x := hs (.inr (.inl l))
    linarith
  · have hh : D/2 - data.shift - 3*par.mu ≤ x (i,none,true,l) := hs (.inl (none,true,l))
    change W i l x - D/2 - data.shift - 3*par.mu ≤ W i l x + x (i,none,true,l) - D
    linarith
  · apply nonpos_of_mul_nonpos_right _ par.epos
    rw [bid_formula]
    exact sub_nonpos.mpr (hs (.inr (.inr e)))

theorem Standard.first (hs : Standard data D b i x) (l : Fin V) (d : Fin B) (hd : d ≠ b) :
    W i l x - D/2 - data.shift ≤ W i l x + terminal i d (false,l) x - D := by
  have hh := hs (.inl (some d,false,l))
  simp only [bound,standard,hd,↓reduceIte,sub_zero] at hh
  unfold terminal
  linarith

theorem cost_mul (data : SampleData par) (p : Values V) (l : Fin V) :
    par.eps * data.cost p l = p l + par.eps * data.child := by
  unfold SampleData.cost
  field_simp [par.epos.ne']

theorem Standard.second (hs : Standard data D b i x) (l : Fin V) (d : Fin B) (hd : d ≠ b) :
    par.eps * (data.cost (fun l => P i l x - D) l + par.lam) ≤
      P i l x + terminal i d (true,l) x - D := by
  have hh := hs (.inl (some d,true,l))
  simp only [bound,standard,hd,↓reduceIte] at hh
  rw [mul_add,cost_mul]
  unfold terminal
  linarith

theorem standard_stops {w v f g : Values V}
    (hp : ∀ pos, 0 < base i pos x + terminal i b pos x - D)
    (hm : data.Motion (fun l => W i l x - D/2 - data.shift) (fun l => P i l x - D) w v f g)
    (r : Stencil code B) (he : standard par i r x = bound data D b r) :
    standard par i r (impulse i b w v f g) = 0 := by
  rcases r with ⟨_ | d,kind,l⟩ | l | e
  · cases kind
    · change W i l x = D/2 at he
      change W i l _ = _
      rw [impulse.width]
      exact (hm.first l (by linarith [data.shiftPos,par.mupos])).1
    · change x (i,none,true,l) = D/2-data.shift-3*par.mu at he
      have ht := hm.priceLink l (show W i l x + x (i,none,true,l) - D = _ by linarith)
      simp [standard,impulse,ht]
  · change terminal i d (kind,l) _ = _
    rw [impulse.endpt]
    by_cases hd : d = b
    swap
    · simp [hd]
    subst d
    cases kind
    · simp only [bound,standard,↓reduceIte] at he
      have hh : 0 < W i l x + terminal i b (false,l) x - D := hp (false,l)
      unfold terminal at hh
      simp [hm.firstLink l (by linarith)]
    · simp only [bound,standard,↓reduceIte] at he
      have hh : 0 < P i l x + terminal i b (true,l) x - D := hp (true,l)
      unfold terminal at hh
      have ht : par.lam < data.cost (fun l => P i l x - D) l := by
        apply lt_of_mul_lt_mul_left _ par.epos.le
        rw [cost_mul]
        linarith
      simp [hm.secondLink l ht]
  · change P i l x = D-par.K*par.eps at he
    change P i l _ = 0
    rw [impulse.price]
    exact hm.floor l (by linarith)
  · have ht : code.bid par.q e (data.u (fun l => P i l x - D) e.1) = 0 := by
      apply (mul_eq_zero.mp ?_).resolve_left par.epos.ne'
      rw [bid_formula]
      exact sub_eq_zero.mpr he.symm
    change code.bid par.q e (prices i (impulse i b w v f g)) = 0
    have hv : prices i (impulse i b w v f g) = v := funext fun l => impulse.price i b w v f g l
    rw [hv]
    exact hm.contest _ ht

end OAI.Geometry.Hirsch.Layer
