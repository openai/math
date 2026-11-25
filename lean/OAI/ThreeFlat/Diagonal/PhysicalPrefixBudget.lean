import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import OAI.ThreeFlat.Diagonal.PhysicalRepeatEnergy

namespace OAI
/-! # Uniform bounds at intermediate states inside each contracting physical block -/

namespace ThreeFlat.Diagonal.PhysicalStage
noncomputable section

def Effect.growth (u : Effect) : ℝ := 1+u.leading+u.error

theorem Effect.fold_sites_le (us : List Effect) (v : Totals) (hp : 0≤v.sites) :
    (us.foldl Effect.apply v).sites ≤ v.sites := by
  induction us generalizing v with
  | nil => exact le_rfl
  | cons u us ih =>
    have next : 0 ≤ (u.apply v).sites ∧ (u.apply v).sites ≤ v.sites := by
      cases h : u.shrink <;> simp only [Effect.apply,h,Bool.false_eq_true,ite_false,ite_true]
      · exact ⟨hp,le_rfl⟩
      · exact ⟨by positivity,by linarith⟩
    exact (ih _ next.1).trans next.2

theorem Effect.in_scan (us : List Effect) (hu : ∀ a ∈ us,a.Positive) (v : Totals) (hv : v.Positive)
    (w : Totals) (hw : w ∈ us.scanl Effect.apply v) :
    w.energy+w.sites^2 ≤ (us.map Effect.growth).prod*(v.energy+v.sites^2) := by
  induction us generalizing v w with
  | nil =>
    have eq : w=v := by simpa using hw
    simp [eq]
  | cons a as ih =>
    have ha := hu a List.mem_cons_self
    have ht := fun t (hm : t ∈ as) => hu t (List.mem_cons_of_mem _ hm)
    have growth : 1 ≤ a.growth := by dsimp [Effect.growth]; linarith [ha.1,ha.2]
    have prod' : 1 ≤ (as.map Effect.growth).prod := by
      apply List.one_le_prod
      intro x hx
      obtain ⟨u,hm,rfl⟩ := List.mem_map.mp hx
      dsimp [Effect.growth]
      linarith [(ht u hm).1,(ht u hm).2]
    rw [List.scanl_cons,List.mem_cons] at hw
    rw [List.map_cons,List.prod_cons]
    rcases hw with rfl|rest
    · exact le_mul_of_one_le_left (add_nonneg hv.1 (sq_nonneg _)) (one_le_mul_of_one_le_of_one_le growth prod')
    · have each : (a.apply v).energy+(a.apply v).sites^2 ≤ a.growth*(v.energy+v.sites^2) := by
        have hsites : (a.apply v).sites^2 ≤ v.sites^2 := by
          cases h : a.shrink <;> simp only [Effect.apply,h,Bool.false_eq_true,ite_false,ite_true]
          · exact le_rfl
          · nlinarith only [sq_nonneg v.sites]
        change a.leading*v.energy+a.error*v.sites^2+_ ≤ _
        dsimp only [Effect.growth]
        nlinarith only [hsites,hv.1,mul_nonneg ha.1 (sq_nonneg v.sites),mul_nonneg ha.2 hv.1]
      refine (ih ht _ (a.apply_positive ha _ hv) _ rest).trans ?_
      calc
        _ ≤ (as.map Effect.growth).prod * (a.growth*(v.energy+v.sites^2)) :=
          mul_le_mul_of_nonneg_left each (by linarith)
        _ = _ := by ring

namespace Block
variable {F : Type} [Field F] (B : Block F)

def stageGrowth : ℝ := ((B.oneBlockEffects shrinkError).map Effect.growth).prod

private theorem effect_positive (u : Effect) (hu : u ∈ B.oneBlockEffects shrinkError) : u.Positive := by
  apply List.mem_append.mp at hu
  rcases hu with hs|hr
  · have hh := B.shrinkEffects_spec _ _ u hs
    exact ⟨by rw [hh.1]; norm_num,hh.2.1⟩
  · obtain rfl := List.mem_singleton.mp hr
    exact ⟨le_max_left _ _,B.refresh.nonneg⟩

theorem stageGrowth_one_le : 1 ≤ B.stageGrowth := by
  apply List.one_le_prod
  intro x hx
  obtain ⟨u,hm,rfl⟩ := List.mem_map.mp hx
  have pos := B.effect_positive u hm
  dsimp [Effect.growth]
  linarith [pos.1,pos.2]

/-- The extra site term covers any physical block whose tile-table error is zero. -/
def initialBudget (v : Totals) : ℝ := B.potential v+v.sites

theorem initialBudget_nonneg (v : Totals) (hv : v.Positive) : 0 ≤ B.initialBudget v := by
  dsimp only [initialBudget,potential]
  exact add_nonneg (add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hv.2)) hv.2

private theorem sqrt_start (v : Totals) (hv : v.Positive) (u : Totals) (h : u.energy+u.sites^2 ≤ B.stageGrowth*(v.energy+v.sites^2)) :
      Real.sqrt u.energy ≤ Real.sqrt B.stageGrowth*B.initialBudget v := by
  have start : v.energy+v.sites^2 ≤ (B.initialBudget v)^2 := by
    have ex : Real.sqrt v.energy + v.sites ≤ B.initialBudget v := by
      dsimp [initialBudget,potential]
      linarith only [mul_nonneg (show 0 ≤ 4*Real.sqrt B.blockError by positivity) hv.2]
    have ss := pow_le_pow_left₀ (add_nonneg (Real.sqrt_nonneg _) hv.2) ex 2
    rw [add_sq,Real.sq_sqrt hv.1] at ss
    nlinarith only [ss,mul_nonneg (Real.sqrt_nonneg v.energy) hv.2]
  apply Real.sqrt_le_iff.mpr
  have hG := B.stageGrowth_one_le
  refine ⟨mul_nonneg (Real.sqrt_nonneg _) (B.initialBudget_nonneg v hv),?_⟩
  rw [mul_pow,Real.sq_sqrt (show 0≤B.stageGrowth by linarith)]
  exact (le_add_of_nonneg_right (sq_nonneg _)).trans (h.trans (mul_le_mul_of_nonneg_left start (by linarith)))

theorem scan_energy (n : ℕ) (v : Totals) (hv : v.Positive) (w : Totals)
    (hw : w ∈ ((B.repeat n).effects shrinkError).scanl Effect.apply v) :
    Real.sqrt w.energy ≤ Real.sqrt B.stageGrowth*B.initialBudget v := by
  induction n generalizing v w with
  | zero =>
    have eq : w=v := by simpa [«repeat»,Program.effects] using hw
    subst w
    apply B.sqrt_start v hv
    exact le_mul_of_one_le_left (add_nonneg hv.1 (sq_nonneg _)) B.stageGrowth_one_le
  | succ n ih =>
    rw [B.effects_repeat_succ,List.scanl_append,List.mem_append] at hw
    rcases hw with before|after
    · exact B.sqrt_start v hv _ (Effect.in_scan _ B.effect_positive v hv w before)
    · let b := (B.oneBlockEffects shrinkError).foldl Effect.apply v
      have hb := B.apply_block v hv
      have later := ih b hb.1 w (List.mem_of_mem_tail after)
      apply later.trans
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      have decrease := Effect.fold_sites_le (B.oneBlockEffects shrinkError) v hv.2
      have nonneg : 0≤B.potential v := by
        exact add_nonneg (Real.sqrt_nonneg _) (mul_nonneg (by positivity) hv.2)
      change B.potential b+b.sites ≤ B.potential v+v.sites
      have half : B.potential b≤B.potential v/2 := hb.2
      change b.sites ≤ v.sites at decrease
      linarith

end Block
end
end ThreeFlat.Diagonal.PhysicalStage

end OAI
