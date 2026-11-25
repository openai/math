import OAI.ThreeFlat.Diagonal.PhysicalTotals

namespace OAI
/-! # Estimates for chronological lists of numerical stage effects -/

namespace ThreeFlat.Diagonal.PhysicalStage
noncomputable section

def Totals.Positive (v : Totals) : Prop := 0 ≤ v.energy ∧ 0 ≤ v.sites

def Effect.Positive (u : Effect) : Prop := 0 ≤ u.leading ∧ 0 ≤ u.error

theorem Effect.apply_positive (u : Effect) (hu : u.Positive) (v : Totals) (hv : v.Positive) :
    (u.apply v).Positive := by
  constructor
  · exact add_nonneg (mul_nonneg hu.1 hv.1) (mul_nonneg hu.2 (sq_nonneg _))
  · cases h : u.shrink <;> simp only [Effect.apply,h,Bool.false_eq_true,ite_false,ite_true]
    · exact hv.2
    · exact div_nonneg hv.2 (by norm_num)

def Effect.errors (us : List Effect) : ℝ := (us.map Effect.error).sum

theorem Effect.errors_nonneg (us : List Effect) (hu : ∀ u ∈ us, 0 ≤ u.error) : 0 ≤ errors us := by
  induction us with
  | nil => simp [errors]
  | cons a as ih =>
    exact add_nonneg (hu a List.mem_cons_self) (ih (fun u h => hu u (List.mem_cons_of_mem _ h)))

/-- All shrink stages have the same coefficient. Their additive errors may differ. -/
theorem Effect.fold_shrinks (us : List Effect) (v : Totals) (hP : 0 ≤ v.sites)
    (h : ∀ u ∈ us, u.leading=126/127 ∧ 0≤u.error ∧ u.shrink=true) :
    let w := us.foldl Effect.apply v
    w.energy ≤ (126/127:ℝ)^us.length*v.energy+errors us*v.sites^2 ∧
    w.sites = v.sites/4^us.length := by
  induction us generalizing v with
  | nil => simp [errors]
  | cons u us ih =>
    obtain ⟨lead,err,shrink⟩ := h u List.mem_cons_self
    have ht := fun a (ha : a ∈ us) => h a (List.mem_cons_of_mem _ ha)
    have pos : 0 ≤ (u.apply v).sites := by
      simpa only [apply,shrink,ite_true] using (div_nonneg hP (by norm_num : (0:ℝ) ≤ 4))
    obtain ⟨E,P⟩ := ih (u.apply v) pos ht
    have energy : (Effect.apply v u).energy=(126/127:ℝ)*v.energy+u.error*v.sites^2 := by
      simp only [Effect.apply,lead]
    have sites : (Effect.apply v u).sites=v.sites/4 := by simp only [Effect.apply,shrink,ite_true]
    rw [energy,sites] at E
    rw [sites] at P
    constructor
    · change (us.foldl Effect.apply (Effect.apply v u)).energy ≤
        (126/127:ℝ)^(u::us).length*v.energy+errors (u::us)*v.sites^2
      have aa : (126/127:ℝ)^us.length ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
      have bb : 0 ≤ errors us := errors_nonneg us (fun a ha => (ht a ha).2.1)
      have term : (126/127:ℝ)^us.length*(u.error*v.sites^2) ≤ u.error*v.sites^2 := by
        simpa only [one_mul] using mul_le_mul_of_nonneg_right aa (mul_nonneg err (sq_nonneg v.sites))
      have tail := mul_le_mul_of_nonneg_left (show (v.sites/4)^2 ≤ v.sites^2 by nlinarith [sq_nonneg v.sites]) bb
      calc
        _ ≤ (126/127:ℝ)^us.length*((126/127:ℝ)*v.energy+u.error*v.sites^2)+errors us*(v.sites/4)^2 := E
        _ = (126/127:ℝ)^us.length*((126/127:ℝ)*v.energy)+
            ((126/127:ℝ)^us.length*(u.error*v.sites^2)+errors us*(v.sites/4)^2) := by rw [mul_add,add_assoc]
        _ ≤ (126/127:ℝ)^us.length*((126/127:ℝ)*v.energy)+(u.error*v.sites^2+errors us*v.sites^2) :=
          add_le_add le_rfl (add_le_add term tail)
        _ = _ := by rw [List.length_cons,pow_succ (126/127:ℝ) us.length];simp only [errors,List.map_cons,List.sum_cons];ring
    · change (us.foldl Effect.apply (Effect.apply v u)).sites = v.sites/4^(u::us).length
      rw [P,List.length_cons,pow_succ (4:ℝ) us.length,div_div,mul_comm (4:ℝ) (4^us.length)]

/-- The final refresh may expand energy. The stored block inequality already pays for it. -/
theorem Effect.fold_block (us : List Effect) (r : Effect) (v : Totals) (vz : v.Positive)
    (h : ∀ u ∈ us, u.leading=126/127 ∧ 0≤u.error ∧ u.shrink=true)
    (nonempty : 0 < us.length) (hr : r.Positive) (refresh : r.shrink=false)
    (contracts : r.leading*(126/127:ℝ)^us.length ≤ 1/4) :
    let w := (us++[r]).foldl Effect.apply v
    w.energy ≤ v.energy/4+(r.leading*errors us+r.error)*v.sites^2 ∧ 4*w.sites ≤ v.sites := by
  obtain ⟨he,hp⟩ := fold_shrinks us v vz.2 h
  let w := us.foldl Effect.apply v
  have four : (4:ℝ) ≤ 4^us.length := by
    calc (4:ℝ) = 4^1 := by norm_num
         _ ≤ _ := pow_le_pow_right₀ (by norm_num) nonempty
  have hsites : 4*w.sites ≤ v.sites := by
    change 4*(us.foldl Effect.apply v).sites ≤ v.sites
    rw [hp]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : (0:ℝ) < 4^us.length)]
    nlinarith only [mul_le_mul_of_nonneg_right four vz.2]
  have hle : w.sites ≤ v.sites := by
    dsimp only [w]
    rw [hp,div_le_iff₀ (by positivity : (0:ℝ) < 4^us.length)]
    nlinarith only [mul_le_mul_of_nonneg_right (show (1:ℝ) ≤ 4^us.length by linarith) vz.2]
  have h0 : 0≤ w.sites := by dsimp only [w]; rw [hp]; exact div_nonneg vz.2 (by positivity)
  have hsq := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hle 2) hr.2
  have he' := mul_le_mul_of_nonneg_left he hr.1
  have hc := mul_le_mul_of_nonneg_right contracts vz.1
  simp only [List.foldl_append,List.foldl_cons,List.foldl_nil,Effect.apply,refresh,Bool.false_eq_true,ite_false]
  exact ⟨by dsimp only [w] at hsq; nlinarith only [hsq,he',hc],hsites⟩

end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
