import OAI.Geometry.Hirsch.Prices

noncomputable section

namespace OAI.Geometry.Hirsch.Layer.SampleData

variable {L V : ℕ} {code : Bundles L V} {par : Parameters code}
  (data : SampleData par) (z p : Values V)

structure Motion (w v f g : Values V) : Prop where
  first : ∀ l, z l ≤ par.mu → w l = 0 ∧ f l = 0
  coarse : ∀ c ∈ data.cuts, ∀ mask, dot (replace par.M c mask) z = 1 → dot (replace par.M c mask) w = 0
  second : ∀ l, data.cost p l ≤ -(3*par.lam/4) → g l = 0
  low : ∀ l, data.cost p l ≤ par.lam/4 → v l = 0
  locked : ∀ l, data.Locked p l → v l = 0
  priceLink : ∀ l, p l = z l - 3*par.mu → v l = w l
  firstLink : ∀ l, par.sigma ≤ z l → f l = 0
  secondLink : ∀ l, par.lam < data.cost p l → g l = 0

def Fixed : Prop :=
  ∀ w v f g, data.Motion z p w v f g → w = 0 ∧ v = 0 ∧ f = 0 ∧ g = 0

variable {data z p}

theorem Fixed.rigid (fix : data.Fixed z p) (hf : data.Prices z p) : data.Rigid z p := by
  classical
  have nonzero : ∀ l : Fin V, (Pi.single l 1 : Values V) ≠ 0 := by
    intro l he
    simpa using congrFun he l
  have blank : data.Motion z p 0 0 0 0 := by constructor <;> simp
  refine ⟨?_,?_,?_,?_⟩
  · intro dir hz hp hl hc
    exact (fix dir dir 0 0 ⟨fun l hh => ⟨hz l hh,rfl⟩,hc,blank.second,hp,hl,fun _ _ => rfl,
      blank.firstLink,blank.secondLink⟩).1
  · intro l hl
    by_contra! hn
    apply nonzero l
    have hm : data.Motion z p 0 0 (Pi.single l 1) 0 := {
      blank with
      first := fun j hj => ⟨rfl,by
        have : j ≠ l := by rintro rfl; exact hn.not_ge hj
        simp [this]⟩
      firstLink := fun j hj => by
        have : j ≠ l := by rintro rfl; exact hl.not_ge hj
        simp [this] }
    exact (fix _ _ _ _ hm).2.2.1
  · intro l hl
    by_contra! hn
    apply nonzero l
    have hm : data.Motion z p 0 0 0 (Pi.single l 1) := {
      blank with
      second := fun j hj => by
        have : j ≠ l := by rintro rfl; exact hl.not_ge hj
        simp [this]
      secondLink := fun j hj => by
        have : j ≠ l := by rintro rfl; exact hn.not_gt hj
        simp [this] }
    exact (fix _ _ _ _ hm).2.2.2
  · intro l hz hl
    by_contra hn
    apply nonzero l
    have hm : data.Motion z p 0 (Pi.single l 1) 0 0 := {
      blank with
      low := fun j hj => by
        have : j ≠ l := by rintro rfl; linarith [par.lpos]
        simp [this]
      locked := fun j hj => by
        have : j ≠ l := by rintro rfl; exact hn hj
        simp [this]
      priceLink := fun j hj => by
        have : j ≠ l := by intro he; subst j; linarith [hf.floor l,par.priceSmall]
        simp [this] }
    exact (fix _ _ _ _ hm).2.1

theorem Motion.floor {w v f g} (hm : data.Motion z p w v f g) (l : Fin V)
    (he : p l = -(par.K*par.eps)) : v l = 0 := by
  apply hm.low
  unfold cost
  rw [he,← neg_mul,mul_div_cancel_right₀ _ par.epos.ne']
  linarith [data.current.2,(data.range data.site).1,par.lpos,par.lsmall]

theorem Motion.contest {w v f g} (hm : data.Motion z p w v f g) (e : code.Contest)
    (he : code.bid par.q e (data.u p e.1) = 0) : code.bid par.q e v = 0 :=
  code.bid_zero fun l hl => hm.locked l ⟨e,hl,he⟩

end OAI.Geometry.Hirsch.Layer.SampleData
