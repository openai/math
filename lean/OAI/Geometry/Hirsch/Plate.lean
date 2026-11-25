import OAI.Geometry.Hirsch.LocalRows

noncomputable section

namespace OAI.Geometry.Hirsch.Layer

open Forest

namespace Supported

variable {T : Type} {time value : T → ℝ} (hs : Supported time value)

def line (t : T) := (hs t).choose

theorem touch (t : T) : hs.line t (time t) = value t := (hs t).choose_spec.1

theorem below (s t : T) : hs.line s (time t) ≤ value t := (hs s).choose_spec.2 t

end Supported

theorem replace_le {V : ℕ} {M : ℝ} {c : Values V} (hc : ∀ l, c l ≤ M) (mask : Fin V → Bool) :
    c ≤ replace M c mask := by intro l; unfold replace; split <;> simp [hc]

namespace Plate

variable {I : Type} {L V B N C : ℕ} {code : Bundles L V} {par : Parameters code}
  {time D : Probe N B → ℝ} {data : Probe N B → SampleData par} (plate : Plate time par data D C)

abbrev Rows (data : Probe N B → SampleData par) :=
  Σ t, Stencil code B ⊕ (↥(data t).cuts × (Fin V → Bool))

def normal (i : I) : Rows data → Form I B V
  | ⟨_,.inl r⟩ => standard par i r
  | ⟨_,.inr (c,m)⟩ => coarseForm i (replace par.M c.val m)

def rhs : Rows data → Line
  | ⟨t,.inl r⟩ => (plate.ordinary r).line t
  | ⟨t,.inr (c,m)⟩ => (plate.extra t c.val c.property m).choose

variable [NeZero B]

include plate in
theorem valid (i : I) (r : Rows data) :
    Monotone (normal i r) ∧ 0 < normal i r 1 ∧ Localized i (normal i r) := by
  rcases r with ⟨t,r | ⟨c,m⟩⟩
  · exact standard_ok par i r
  · obtain ⟨hn,hp⟩ := plate.weights t c.val c.property
    have hh := replace_le ((data t).bounded _ c.property) m
    exact coarse_ok i _ (hn.trans hh) (hp.trans_le (dot_weights hh zero_le_one))

variable [NeZero N]

def panel (i : I) : Panel I B V i where
  Row := Rows data
  coeff := normal i
  rhs := plate.rhs
  mono r := (plate.valid i r).1
  pos r := (plate.valid i r).2.1
  individual role pos := ⟨⟨(0,0),.inl (.inl (role,pos))⟩,rfl⟩
  localizes r := (plate.valid i r).2.2

theorem internal (i : I) (t : Probe N B) : (plate.panel i).Internal (time t) (D t) t.2 (data t) := by
  intro x hx
  have hs : Standard (data t) (D t) t.2 i x := by
    intro r
    exact ((plate.ordinary r).touch t).symm.trans_le (hx ⟨t,.inl r⟩)
  have hc : Expanded (data t).cuts par.M (adjusted (data t) (D t) (widths i x)) := by
    intro c hh m
    rw [dot_adjusted,le_sub_iff_add_le]
    exact (plate.extra t c hh m).choose_spec.1.symm.trans_le (hx ⟨t,.inr (⟨c,hh⟩,m)⟩)
  refine ⟨hs.prices hc,hs.first,hs.second,fun hp w v f g hm r he => ?_⟩
  rcases r with ⟨s,r | ⟨c,m⟩⟩
  · exact standard_stops hp hm r (le_antisymm (he.trans_le ((plate.ordinary r).below s t)) (hs r))
  · by_cases ht : t = s
    swap
    · exact ((plate.extra s _ c.property m).choose_spec.2 t ht _ hs.lower hc).ne' he |>.elim
    subst s
    have hh : dot (replace par.M c.val m) (adjusted (data t) (D t) (widths i x)) = 1 := by
      rw [dot_adjusted,sub_eq_iff_eq_add]
      exact he.trans (plate.extra t _ c.property m).choose_spec.1
    change dot _ (widths i (impulse i t.2 w v f g)) = 0
    have hw : widths i (impulse i t.2 w v f g) = w := funext fun l => impulse.width i t.2 w v f g l
    rw [hw]
    exact hm.coarse _ c.property m hh

def budget (code : Bundles L V) (C : ℕ) :=
  5*V + Fintype.card code.Contest + C*2^V

theorem rows (i : I) : Fintype.card (plate.panel i).Row ≤ budget code C * N * B^2 := by
  change Fintype.card (Rows data) ≤ _
  rw [Fintype.card_sigma]
  have hb := NeZero.pos B
  calc
    _ ≤ ∑ _ : Probe N B, B * budget code C := by
      apply Finset.sum_le_sum
      intro t _
      rw [Fintype.card_sum,Fintype.card_prod,Fintype.card_coe,Fintype.card_fun]
      have h₁ : Fintype.card (Stencil code B) = (B+1)*(2*V) + (V + Fintype.card code.Contest) := by
        simp [Stencil,Index,Position]
      rw [h₁,Fintype.card_fin,Fintype.card_bool]
      unfold budget
      have h₂ := Nat.mul_le_mul_right (2^V) (plate.count t)
      have h₃ := Nat.le_mul_of_pos_left (Fintype.card code.Contest + C*2^V) hb
      nlinarith
    _ = _ := by simp [Probe]; ring

end Plate
end OAI.Geometry.Hirsch.Layer
