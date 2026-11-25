import OAI.Hierarchy.GridTickAddresses
import OAI.Hierarchy.FactorSchedule
import OAI.Hierarchy.LinePassages

namespace OAI
/-! # The unique touched cell and the reserved passages of each scheduled rail -/

namespace Hierarchy.GridTicks

open FactorAllocation

/-- A pair is indexed by its assigned tick and its position among the pairs there. -/
def pairsOn {ι : Type*} (counts : ι → ℕ) (ticks : Finset ι) : Finset (Σ t, Fin (counts t)) :=
  ticks.sigma (fun _ => Finset.univ)

@[simp] theorem card_pairsOn {ι : Type*} (counts : ι → ℕ) (ticks : Finset ι) :
    (pairsOn counts ticks).card = ∑ t∈ticks, counts t := by
  simp [pairsOn, Finset.card_sigma]

theorem pairsOn_subset {ι : Type*} {a b : Finset ι} (h : a ⊆ b) (counts : ι → ℕ) :
    pairsOn counts a ⊆ pairsOn counts b := by
  intro p hp
  exact Finset.mem_sigma.mpr ⟨h (Finset.mem_sigma.mp hp).1, Finset.mem_univ _⟩

/-- For a real resource coordinate representing one direction's pairs, allocate
the original list to ticks, give each pair its tick as its one touch, and retain
at least B passages on that line outside any given cell. -/
theorem scheduled_line_passages {α : Type*} {k g q d w cap B : ℕ} (hg : 4 ≤ g) (hq : 0 < q)
    (cost : α → Fin d → ℕ) (items : List α) (coord : Fin d)
    (width : ∀ a∈items, ∀ j, cost a j ≤ 2^w) (bounded : ∀ a∈items, ∀ j, cost a j ≤ cap)
    (total : (items.map (fun x => cost x coord)).sum = 2*g^(k-1)*B)
    (small : ((20*((w:ℝ)+1)+2)^d * cap) * (g*q:ℕ) ≤ B/16)
    (axis : Fin k) (z : Cell k g) :
    let count (t : Tick k g q) := ((factors w cost items t).map (fun x => cost x coord)).sum
    let line := pairsOn count (lineTicks axis z)
    let touched := pairsOn count (cellTicks z)
    B ≤ line.card ∧ line.card ≤ 3*B ∧ B ≤ (line \ touched).card := by
  classical
  let count (t : Tick k g q) := ((factors w cost items t).map (fun x => cost x coord)).sum
  change B ≤ (pairsOn count (lineTicks axis z)).card ∧
    (pairsOn count (lineTicks axis z)).card ≤ 3*B ∧
    B ≤ ((pairsOn count (lineTicks axis z)) \ pairsOn count (cellTicks z)).card
  let mean : ℝ := (items.map (fun x => (cost x coord : ℝ))).sum / (g^k*q)
  let err : ℝ := (20*((w:ℝ)+1)+2)^d * cap
  have sumCost : (items.map (fun x => (cost x coord : ℝ))).sum = (2*g^(k-1)*B:ℕ) := by
    have eqn := congrArg (fun n : ℕ => (n : ℝ)) total
    simpa [List.map_map, Function.comp_def] using eqn
  have exp : g^k = g^(k-1)*g := by
    have hk : k-1+1 = k := by have := axis.isLt; omega
    exact hk ▸ (pow_succ g (k-1))
  have realG : (0:ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  have realQ : (0:ℝ) < q := by exact_mod_cast hq
  have meanPairs : mean * (g*q:ℕ) = 2*(B:ℝ) := by
    dsimp only [mean]
    rw [sumCost]
    push_cast
    have exp' : (g:ℝ)^k = (g:ℝ)^(k-1)*g := by exact_mod_cast exp
    rw [exp']
    field_simp
  have loads (t : Tick k g q) : mean/(21/20)-err ≤ (count t : ℝ) ∧
      (count t : ℝ) ≤ (21/20)*mean + (21/20)*err := by
    have h := tickLoad_bounds cost items cap width bounded coord t
    rw [← sum_factors_eq_tickLoad] at h
    dsimp only [mean, err]
    simp only [Nat.cast_mul, Nat.cast_pow] at h
    simpa only [mul_left_comm (21/20:ℝ)] using h
  have h := line_passages (lineTicks (q:=q) axis z) (cellTicks z) (fun t => (count t : ℝ))
    hg hq (cell_subset_line axis z) (card_lineTicks axis z) (card_cellTicks z)
    B mean err (by positivity) meanPairs small (fun i _ => (loads i).1) (fun i _ => (loads i).2)
  have untouched := Finset.card_sdiff_of_subset (pairsOn_subset (cell_subset_line (q:=q) axis z) count)
  rw [untouched, card_pairsOn, card_pairsOn]
  have lb : B ≤ ∑ t∈lineTicks axis z, count t := by exact_mod_cast h.1
  have ub : (∑ t∈lineTicks axis z, count t) ≤ 3*B := by exact_mod_cast h.2.1
  have diff : (B:ℝ) + (∑ t∈cellTicks z, (count t : ℝ)) ≤ ∑ t∈lineTicks axis z, (count t : ℝ) := by
    linarith only [h.2.2]
  have rem : B + (∑ t∈cellTicks z, count t) ≤ ∑ t∈lineTicks axis z, count t := by exact_mod_cast diff
  exact ⟨lb, ub, by omega⟩

end Hierarchy.GridTicks

end OAI
