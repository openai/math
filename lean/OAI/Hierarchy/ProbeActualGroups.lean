import OAI.Hierarchy.ProbePermutationRoute
import OAI.Hierarchy.ProbeStageTemplateSize
import OAI.Hierarchy.ProbeChainDensity

namespace OAI
/-! # Port and ceiling estimates summed over every actual CT stage group -/

namespace Hierarchy.ProbeStage
open Filter AdaptiveProbe
open scoped BigOperators
noncomputable section

abbrev StageAt (h d : ℕ) := Fin (permutationFabric h d).shapes.length

def stageAt (h d : ℕ) (i : StageAt h d) := (permutationFabric h d).shapes.get i

abbrev AllGroups (h d : ℕ) := Σ i : StageAt h d, (stageAt h d i).Group

instance (h d : ℕ) : Fintype (AllGroups h d) := inferInstanceAs
  (Fintype (Σ i : StageAt h d, (stageAt h d i).Group))

theorem all_ports {h d : ℕ} (hd : 1 ≤ d) :
    (∑ g : AllGroups h d, ((stageAt h d g.1).span:ℝ)) ≤
      (permutationFabric h d).shapes.length*((4:ℝ)^(rounds d+1)*2^h) := by
  have bound (i : StageAt h d) : (Fintype.card (stageAt h d i).Group:ℝ)*(stageAt h d i).span ≤
      (4:ℝ)^(rounds d+1)*2^h := by exact_mod_cast (template_dyadic hd _ (List.get_mem ..)).2
  rw [Fintype.sum_sigma]
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
  have total := Finset.sum_le_sum (s:=Finset.univ) fun i _ => bound i
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] using total

theorem all_groups_sparse {d : ℕ} (hd : 1 ≤ d) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ h : ℕ in atTop, (Fintype.card (AllGroups h d):ℝ) ≤
      (permutationFabric h d).shapes.length*(ε*(2:ℝ)^h) := by
  filter_upwards [eventually_sparse_groups hd hε] with h small
  have row (i : StageAt h d) : (Fintype.card (stageAt h d i).Group:ℝ) ≤ ε*(2:ℝ)^h :=
    small _ (List.get_mem ..)
  have total := Finset.sum_le_sum (s:=Finset.univ) fun i _ => row i
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at total
  simpa only [AllGroups,Fintype.card_sigma,Nat.cast_sum] using total

/-- A positive fraction of marked actual tiles purchases a linear number of probes,
with one δ independent of h, π and the selected signed direction. -/
theorem acquire_linear {C : Type*} [Fintype C] [Nonempty C] {d H : ℕ} (hd : 1 ≤ d) (hH : 0 < H)
    {β : ℝ} (hβ : 0 < β) : ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ h : ℕ in atTop,
    ∀ purchased left mark : AllGroups h d → C → ℕ,
    (∀ g c, purchased g c*H+left g c=mark g c) →
    (∀ g c, left g c < H*(2*⌈δ*((stageAt h d g.1).span:ℝ)⌉₊)) →
    let tiles := (permutationFabric h d).shapes.length*(2:ℝ)^h
    β*tiles ≤ ∑ g, ∑ c, (mark g c:ℝ) → β*tiles/(2*H) ≤ ∑ g, ∑ c, (purchased g c:ℝ) := by
  let D := (Fintype.card C:ℝ)*(2*H)
  let K := (4:ℝ)^(rounds d+1)
  have count : 0 < (Fintype.card C:ℝ) := by exact_mod_cast Fintype.card_pos (α:=C)
  have dpos : 0 < D := by dsimp [D]; positivity
  have kpos : 0 < K := by dsimp [K]; positivity
  let δ := β/(4*D*K)
  let ε := β/(4*D)
  have pos : 0 < δ := by dsimp [δ]; positivity
  have epos : 0 < ε := by dsimp [ε]; positivity
  refine ⟨δ,pos,?_⟩
  filter_upwards [all_groups_sparse hd epos] with h sparse
  intro purchased left mark actual maxed tiles many
  apply purchased_density (fun g : AllGroups h d => (stageAt h d g.1).span) purchased left mark
    hH pos.le actual maxed many
  · have cost := mul_le_mul_of_nonneg_left (all_ports (h:=h) hd) (mul_nonneg dpos.le pos.le)
    convert cost using 1
    dsimp [δ,tiles,K]
    field_simp [dpos.ne']
  · have cost := mul_le_mul_of_nonneg_left sparse dpos.le
    convert cost using 1
    dsimp [ε,tiles]; field_simp [dpos.ne']

/-- One actual scan per stage and sign, over all that stage's groups. This sum uses
its genuine global purchase count and projects its leftover bank to each group. -/
theorem acquire_native_linear {C : Type*} [Fintype C] [Nonempty C] {d H : ℕ}
    (hd : 1 ≤ d) (hH : 0 < H) {β : ℝ} (hβ : 0 < β) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ h : ℕ in atTop,
    ∀ bought marked : StageAt h d → C → ℕ, ∀ left : AllGroups h d → C → ℕ,
    (∀ s c, bought s c*H+(∑ g : (stageAt h d s).Group, left ⟨s,g⟩ c)=marked s c) →
    (∀ g c, left g c < H*(2*⌈δ*((stageAt h d g.1).span:ℝ)⌉₊)) →
    let tiles := (permutationFabric h d).shapes.length*(2:ℝ)^h
    β*tiles ≤ ∑ s, ∑ c, (marked s c:ℝ) → β*tiles/(2*H) ≤ ∑ s, ∑ c, (bought s c:ℝ) := by
  let D := (Fintype.card C:ℝ)*(2*H)
  let K := (4:ℝ)^(rounds d+1)
  have count : 0 < (Fintype.card C:ℝ) := by exact_mod_cast Fintype.card_pos (α:=C)
  have dpos : 0 < D := by dsimp [D]; positivity
  have kpos : 0 < K := by dsimp [K]; positivity
  let δ := β/(4*D*K)
  let ε := β/(4*D)
  have pos : 0 < δ := by dsimp [δ]; positivity
  have epos : 0 < ε := by dsimp [ε]; positivity
  refine ⟨δ,pos,?_⟩
  filter_upwards [all_groups_sparse hd epos] with h sparse
  intro bought marked left actual maxed tiles many
  have row (g : AllGroups h d) (c : C) : (left g c:ℝ) ≤ 2*H*(δ*((stageAt h d g.1).span:ℝ)+1) := by
    have one := (Nat.ceil_lt_add_one (mul_nonneg pos.le (Nat.cast_nonneg (stageAt h d g.1).span))).le
    have nrow : (left g c:ℝ) ≤ H*(2*(⌈δ*((stageAt h d g.1).span:ℝ)⌉₊:ℝ)) := by exact_mod_cast (maxed g c).le
    nlinarith only [nrow,mul_le_mul_of_nonneg_left one (show 0 ≤ 2*(H:ℝ) by positivity)]
  have localSum (g : AllGroups h d) : ∑ c, (left g c:ℝ) ≤ D*δ*((stageAt h d g.1).span:ℝ)+D := by
    have le := Finset.sum_le_sum (s:=Finset.univ) fun c _ => row g c
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at le
    exact le.trans_eq (by dsimp [D]; ring)
  have allLeft := Finset.sum_le_sum (s:=Finset.univ) fun g _ => localSum g
  rw [Finset.sum_add_distrib,←Finset.mul_sum,Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at allLeft
  have mass := mul_le_mul_of_nonneg_left (all_ports (h:=h) hd) (mul_nonneg dpos.le pos.le)
  have num := mul_le_mul_of_nonneg_right sparse dpos.le
  have portCost : D*δ*((permutationFabric h d).shapes.length*((4:ℝ)^(rounds d+1)*2^h))=β*tiles/4 := by
    dsimp [δ,K,tiles]; field_simp [dpos.ne']
  have groupCost : ((permutationFabric h d).shapes.length*(ε*(2:ℝ)^h))*D=β*tiles/4 := by
    dsimp [ε,tiles]; field_simp [dpos.ne']
  rw [portCost] at mass; rw [groupCost] at num
  have leftBudget : (∑ g, ∑ c, (left g c:ℝ)) ≤ β*tiles/2 := by linarith
  have decomp (s : StageAt h d) : ∑ c, (marked s c:ℝ) =
      (∑ c, (bought s c:ℝ))*H + ∑ g : (stageAt h d s).Group, ∑ c, (left ⟨s,g⟩ c:ℝ) := by
    have per (c : C) : (marked s c:ℝ)=(bought s c:ℝ)*H+∑ g, (left ⟨s,g⟩ c:ℝ) := by exact_mod_cast (actual s c).symm
    simp_rw [per]; rw [Finset.sum_add_distrib,Finset.sum_mul,Finset.sum_comm (f:=fun c g => (left ⟨s,g⟩ c:ℝ))]
  simp_rw [decomp] at many
  rw [Finset.sum_add_distrib,←Finset.sum_mul,←Fintype.sum_sigma (fun g : AllGroups h d => ∑ c, (left g c:ℝ))] at many
  have hH' : 0 < (H:ℝ) := by exact_mod_cast hH
  apply (div_le_iff₀ (show 0 < 2*(H:ℝ) by positivity)).2
  nlinarith only [many,leftBudget]

end
end Hierarchy.ProbeStage

end OAI
