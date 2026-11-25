import OAI.Geometry.Hirsch.ModulePlan

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

open Forest

variable {I : Type} {L V B N : ℕ} {code : Bundles L V} {par : Parameters code}

def Supported {T : Type} (time value : T → ℝ) : Prop :=
  ∀ t, ∃ f : Line, f (time t) = value t ∧ ∀ s, f (time s) ≤ value s

abbrev Index (B V : ℕ) := Option (Fin B) × Position V
abbrev Stencil (code : Bundles L V) (B : ℕ) := Index B V ⊕ Fin V ⊕ code.Contest

def widths (i : I) : Space I B V →ₗ[ℝ] Values V := LinearMap.pi (W i)
def prices (i : I) : Space I B V →ₗ[ℝ] Values V := LinearMap.pi (P i)

def standard (par : Parameters code) (i : I) : Stencil code B → Form I B V
  | .inl key => LinearMap.proj (i,key)
  | .inr (.inl l) => P i l
  | .inr (.inr e) => (code.bid par.q e).comp (prices i)

def bound (data : SampleData par) (D : ℝ) (b : Fin B) : Stencil code B → ℝ
  | .inl (none,false,_) => D/2
  | .inl (none,true,_) => D/2 - data.shift - 3*par.mu
  | .inl (some d,false,_) => D/2 - data.shift - if d = b then par.sigma else 0
  | .inl (some d,true,_) => par.eps * (data.child + if d = b then -par.lam else par.lam)
  | .inr (.inl _) => D - par.K*par.eps
  | .inr (.inr e) => (D + par.eps * data.offset e.1) * code.bid par.q e 1

def coarseForm (i : I) (c : Values V) : Form I B V := (dot c).comp (widths i)

def adjusted (data : SampleData par) (D : ℝ) (w : Values V) :=
  fun l => w l - D/2 - data.shift

theorem dot_adjusted (data : SampleData par) (D : ℝ) (w c : Values V) :
    dot c (adjusted data D w) = dot c w - (D/2 + data.shift) * dot c 1 := by
  have he : adjusted data D w = w - (D/2 + data.shift) • 1 := by
    ext l; simp [adjusted]; ring
  rw [he,map_sub,map_smul,smul_eq_mul]

theorem bid_formula (data : SampleData par) (D : ℝ) (p : Values V) (e : code.Contest) :
    par.eps * code.bid par.q e (data.u (fun l => p l - D) e.1) =
      (D + par.eps * data.offset e.1) * code.bid par.q e 1 - code.bid par.q e p := by
  have he : par.eps • data.u (fun l => p l - D) e.1 = (D + par.eps * data.offset e.1) • 1 - p := by
    ext l
    simp only [Pi.smul_apply,smul_eq_mul,Pi.sub_apply,Pi.one_apply,mul_one,SampleData.u]
    field_simp [par.epos.ne']; ring
  simpa only [map_smul,smul_eq_mul,map_sub] using congrArg (code.bid par.q e) he

theorem dot_mono {c : Values V} (hc : 0 ≤ c) : Monotone (dot c) :=
  fun _ _ hh => Finset.sum_le_sum (s := Finset.univ) fun l _ => mul_le_mul_of_nonneg_left (hh l) (hc l)

theorem dot_weights {c c' w : Values V} (hc : c ≤ c') (hw : 0 ≤ w) : dot c w ≤ dot c' w :=
  Finset.sum_le_sum (s := Finset.univ) fun l _ => mul_le_mul_of_nonneg_right (hc l) (hw l)

def Localized (i : I) (form : Form I B V) :=
  ∃ b : Fin B, ∀ x, (∀ pos, x (i,none,pos) = 0 ∧ x (i,some b,pos) = 0) → form x = 0

theorem standard_ok [NeZero B] (par : Parameters code) (i : I) (r : Stencil code B) :
    Monotone (standard par i r) ∧ 0 < standard par i r 1 ∧ Localized i (standard par i r) := by
  rcases r with ⟨role,pos⟩ | l | e
  · refine ⟨fun _ _ h => h _,one_pos,?_⟩
    cases role with
    | none => exact ⟨0,fun _ h => (h _).1⟩
    | some b => exact ⟨b,fun _ h => (h _).2⟩
  · exact ⟨fun _ _ h => add_le_add (h _) (h _),add_pos one_pos one_pos,
      0,fun _ h => (congrArg₂ (· + ·) (h (false,l)).1 (h (true,l)).1).trans (add_zero _)⟩
  · refine ⟨fun _ _ h => code.bid_mono par.qpos.le e (fun l => add_le_add (h _) (h _)),?_,0,?_⟩
    · apply (code.bid_pos par.qpos e).trans_le
      exact code.bid_mono par.qpos.le e (fun _ => le_add_of_nonneg_right zero_le_one)
    · intro x hx
      apply code.bid_zero
      intro l _
      change x (i,none,false,l) + x (i,none,true,l) = 0
      rw [(hx _).1,(hx _).1,add_zero]

theorem coarse_ok [NeZero B] (i : I) (c : Values V) (hc : 0 ≤ c) (hp : 0 < dot c 1) :
    Monotone (coarseForm (B := B) i c) ∧ 0 < coarseForm (B := B) i c 1 ∧
      Localized (B := B) i (coarseForm i c) := by
  refine ⟨fun _ _ h => dot_mono hc (fun l => h _),hp,0,fun x hx => ?_⟩
  have he : widths i x = 0 := funext fun l => (hx (false,l)).1
  change dot c (widths i x) = 0
  rw [he,map_zero]

structure Plate (time : Probe N B → ℝ) (par : Parameters code)
    (data : Probe N B → SampleData par) (D : Probe N B → ℝ) (C : ℕ) : Prop where
  count : ∀ t, (data t).cuts.card ≤ C
  weights : ∀ t c, c ∈ (data t).cuts → 0 ≤ c ∧ 0 < dot c 1
  ordinary : ∀ r : Stencil code B, Supported time (fun t => bound (data t) (D t) t.2 r)
  extra : ∀ t c, c ∈ (data t).cuts → ∀ mask,
    let v := replace par.M c mask
    ∃ line : Line, line (time t) = 1 + (D t/2 + (data t).shift) * dot v 1 ∧
      ∀ s ≠ t, ∀ w : Values V, (∀ l, D s/2 ≤ w l) →
        Expanded (data s).cuts par.M (adjusted (data s) (D s) w) → line (time s) < dot v w

end OAI.Geometry.Hirsch.Layer
