import OAI.Hierarchy.DescentScanMinimum
import OAI.Hierarchy.DescentMultiplierSeeds
import OAI.Hierarchy.DescentColonyEstimate
import OAI.Hierarchy.DescentColonyScanLeaves
import OAI.Hierarchy.DescentColonyMultipliers

namespace OAI
/-! # Minimizing the actual propagated leaf count over the field multiplier family -/

namespace Hierarchy.DescentColonies
open DescentGL
open scoped Classical BigOperators
noncomputable section

variable {k : ℕ} {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G]

/-- Count the actual propagated leaves at every group and site using a common
layout of the block indices. -/
def colonyCount (weight : G → V → Block k → ℕ) (adj : V → V → Prop) (a B Δ : ℕ)
    (limit : ∀g v i,weight g v i≤B) (L : Layout k) : ℕ :=
  ∑g,(leaves (rearrangedLoad (weight g) L) adj (32*Nat.clog 2 (2*Δ)) a B
    (fun v i=>limit g v ((rearrange L).symm i))).card

end

noncomputable section
variable {k : ℕ} {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G]

/-- Exhaust the nonzero scalar multipliers and choose the one minimizing the
integer leaf count. Its common permutation pays the quantitative colony bound. -/
theorem minimizing_multiplier_colonies (hk : 0<k) (weight : G → V → Block k → ℕ)
    (adj : V → V → Prop) (a B Δ : ℕ) (limit : ∀g v i,weight g v i≤B)
    (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ) (scale_pos : 0<2^a*B) (two : 2≤2^a) :
    let Q := fun μ : Nonzero k => colonyCount weight adj a B Δ limit (multiplier hk μ)
    Fintype.card (Nonzero k)=2^k-1 ∧ ∃ μ, (∀ ν,Q μ≤Q ν) ∧
      (Q μ : ℝ) ≤ (Fintype.card G:ℝ)*Fintype.card V +
        240*(∑g,∑v,∑i,(weight g v i:ℝ))/(2^a*B:ℕ) := by
  let : Nonempty (Nonzero k) := Fintype.card_pos_iff.mp (by
    rw [card_nonzero]
    have : 1<2^k := Nat.one_lt_pow hk.ne' (by decide)
    omega)
  let Q := fun μ : Nonzero k => colonyCount weight adj a B Δ limit (multiplier hk μ)
  refine ⟨card_nonzero k,?_⟩
  obtain ⟨good,bound⟩ := exists_shared_colonies_family (multiplier hk) (fun hj=>multiplier_pairs hk hj)
    weight adj a B Δ limit degree branch scale_pos two
  obtain ⟨μ,_,best⟩ := Finset.univ.exists_min_image Q Finset.univ_nonempty
  refine ⟨μ,fun ν=>best ν (Finset.mem_univ _),?_⟩
  have small : (Q μ:ℝ)≤Q good := by exact_mod_cast best good (Finset.mem_univ _)
  exact small.trans (by simpa [Q,colonyCount] using bound)

/-- The scan of all nonzero field elements charges exactly one colony-count
evaluation to each of the `2^k-1` candidates. -/
theorem scanned_multiplier_colonies (hk : 0<k) (weight : G → V → Block k → ℕ)
    (adj : V → V → Prop) (a B Δ : ℕ) (limit : ∀g v i,weight g v i≤B)
    (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ) (scale_pos : 0<2^a*B) (two : 2≤2^a) :
    let Q := fun μ : Nonzero k => colonyCount weight adj a B Δ limit (multiplier hk μ)
    let out := scanMinimum Q (nonzeroWords k)
    out.2=2^k-1 ∧ ∃ μ, out.1=some (μ,Q μ) ∧ (∀ ν,Q μ≤Q ν) ∧
      (Q μ : ℝ)≤(Fintype.card G:ℝ)*Fintype.card V+240*(∑g,∑v,∑i,(weight g v i:ℝ))/(2^a*B:ℕ) := by
  let Q := fun μ : Nonzero k => colonyCount weight adj a B Δ limit (multiplier hk μ)
  let seeds := nonzeroWords k
  obtain ⟨_,good,_,bound⟩ := minimizing_multiplier_colonies hk weight adj a B Δ limit degree branch scale_pos two
  obtain ⟨length,correct⟩ := scanMinimum_spec Q seeds
  refine ⟨length.trans (by simp [seeds]),?_⟩
  cases winner : (scanMinimum Q seeds).1 with
  | none =>
    simp only [winner] at correct
    have : good∈seeds := by simp [seeds]
    simp [correct] at this
  | some p =>
    simp only [winner] at correct
    obtain ⟨v,score⟩ := p
    change score = Q v ∧ (∀ t∈seeds,score≤Q t) at correct
    obtain ⟨rfl,lowest⟩ := correct
    have all (μ) := lowest μ (by simp [seeds])
    exact ⟨v,rfl,all,(show (Q v:ℝ)≤Q good by exact_mod_cast all good).trans bound⟩

/-- The score computed by building and reading one buffer per group. -/
def scannedColonyCount (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (D cap : ℕ) (L : Layout k) :=
  ∑g,Scan.leafScore incoming (rearrangedLoad (weight g) L) D cap

theorem scannedColonyCount_eq (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (adj : V → V → Prop) (spec : ∀u v,u∈incoming v ↔ adj u v) (a B Δ : ℕ) (branch : 2≤Δ)
    (limit : ∀g v i,weight g v i≤B) (L : Layout k) :
    scannedColonyCount incoming weight (32*Nat.clog 2 (2*Δ)) (2^a*B) L =
      colonyCount weight adj a B Δ limit L :=
  Finset.sum_congr rfl fun g _ => Scan.leafScore_eq incoming adj spec (rearrangedLoad (weight g) L)
    (DescentColonyGrowth.positive_gap Δ branch) a B (fun v i=>limit g v ((rearrange L).symm i))

/-- Sum the per-candidate buffer read budgets across the whole multiplier sweep.
The extra factor `k+1` allows a lookup to scan the stored depth indices. -/
def multiplierReadBudget (hk : 0<k) (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (D cap : ℕ) :=
  ∑ μ : Nonzero k, ∑g, (k+1)*(Scan.readBudget (k:=k) incoming k +
    Scan.leafVisits (Scan.build incoming (rearrangedLoad (weight g) (multiplier hk μ)) D cap k))

omit [DecidableEq V] in
theorem multiplierReadBudget_bound (hk : 0<k) (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (D cap Δ : ℕ) (degree : ∀v,(incoming v).length≤Δ) :
    multiplierReadBudget hk incoming weight D cap ≤
      (2^k-1)*Fintype.card G*Fintype.card V*(k+1)*(k*(2+Δ)*(2^k)^2 + 2^k*(k+2^k)) := by
  let rate := (k+1)*(Fintype.card V*k*(2+Δ)*(2^k)^2 + Fintype.card V*2^k*(k+2^k))
  calc
    _ ≤ ∑ _μ : Nonzero k, ∑ _g : G, rate := by
      apply Finset.sum_le_sum
      intro μ _
      apply Finset.sum_le_sum
      intro g _
      exact Nat.mul_le_mul_left _ (Nat.add_le_add (Scan.scan_cost incoming Δ degree) (Scan.leafVisits_bound _))
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,card_nonzero,smul_eq_mul,rate]; ring

/-- Evaluate the scores from the packed buffers, scan all scalar multipliers,
and return the shared permutation minimizing the actual propagated leaves. -/
theorem native_multiplier_colonies (hk : 0<k) (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (adj : V → V → Prop) (spec : ∀u v,u∈incoming v ↔ adj u v) (a B Δ : ℕ) (limit : ∀g v i,weight g v i≤B)
    (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ) (scale_pos : 0<2^a*B) (two : 2≤2^a) :
    let D := 32*Nat.clog 2 (2*Δ)
    let score := fun μ : Nonzero k => scannedColonyCount incoming weight D (2^a*B) (multiplier hk μ)
    let Q := fun μ : Nonzero k => colonyCount weight adj a B Δ limit (multiplier hk μ)
    let out := scanMinimum score (nonzeroWords k)
    out.2=2^k-1 ∧ ∃ μ, out.1=some (μ,Q μ) ∧ (∀ ν,Q μ≤Q ν) ∧
      (Q μ : ℝ)≤(Fintype.card G:ℝ)*Fintype.card V+240*(∑g,∑v,∑i,(weight g v i:ℝ))/(2^a*B:ℕ) := by
  dsimp only
  simp_rw [scannedColonyCount_eq incoming weight adj spec a B Δ branch limit]
  exact scanned_multiplier_colonies hk weight adj a B Δ limit degree branch scale_pos two

end
end Hierarchy.DescentColonies

end OAI
