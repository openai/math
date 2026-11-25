import OAI.Hierarchy.ProbeNativeGroups
import OAI.Hierarchy.ProbeActualGroups
import OAI.Hierarchy.ProbeMaskedRoute

namespace OAI
/-! # Positive purchase density in true, advised subdivision permutations -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ProtocolRAM Filter
open scoped BigOperators Classical
noncomputable section

/-- Extract the occupied sockets of any stage of the advised route while retaining its
template type, so the sampler, addressing ordinal, and time budget are independent of π. -/
def advisedStage (h d : ℕ) (π : Equiv.Perm (Fin (2^h))) (s : StageAt h d) :
    Tiles (Fin (2^h)) (stageAt h d s).Group (stageAt h d s).span := by
  let path := advisedRoute h d π
  have shape := path.layer_shapes
  have len : path.layers.length = (permutationFabric h d).shapes.length := by
    simpa only [List.length_map] using congrArg List.length shape
  let index : Fin path.layers.length := ⟨s.val,by simpa only [len] using s.isLt⟩
  let layer := path.layers.get index
  have actual : layer.shape = stageAt h d s := by
    have get := congrArg (fun l => l[s.val]?) shape
    simpa [layer,index,stageAt,List.getElem?_eq_getElem, s.isLt,show s.val < path.layers.length by omega] using get
  exact actual ▸ layer.tiles

/-- One family of constant-degree ROM samplers for all positive stage widths. -/
structure PurchaseSampler where
  degree : ℕ
  rows : (m : ℕ) → Fin m → List (Fin m)
  out_degree : ∀ m o, (rows m o).length ≤ degree
  in_degree : ∀ m i, (Finset.univ.filter fun o => i ∈ rows m o).card ≤ degree

def PurchaseSampler.Mixes (sampler : PurchaseSampler) (δ : ℝ) :=
  ∀ m, 0 < m → SamplerMixes (fun i j => j ∈ sampler.rows m i) ⌈δ*m⌉₊

theorem purchase_sampler {δ : ℝ} (hδ : 0 < δ) : ∃ S : PurchaseSampler, S.Mixes δ := by
  obtain ⟨D,rows⟩ := exists_group_samplers hδ
  classical
  have family (m : ℕ) : ∃ (next : Fin m → List (Fin m)),
      (∀ o, (next o).length ≤ D) ∧ (∀ i, (Finset.univ.filter fun o => i ∈ next o).card ≤ D) ∧
      (0 < m → SamplerMixes (fun i j => j ∈ next i) ⌈δ*m⌉₊) := by
    by_cases pos : 0 < m
    · obtain ⟨next,od,id,graph⟩ := rows m pos
      exact ⟨next,od,id,fun _ => graph (Equiv.refl _) _ (Nat.le_ceil _)⟩
    · have zero : m=0 := by omega
      subst m; exact ⟨Fin.elim0,finZeroElim,finZeroElim,by omega⟩
  choose rows outDeg inDeg mixes using family
  exact ⟨⟨D,rows,outDeg,inDeg⟩,mixes⟩

/-- The exact output of a stage's global chronological native candidate traversal. -/
def advisedPurchases {h d : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (s : StageAt h d) (depth : ℕ) (marked : Finset (Fin (2^h))) :=
  let sh := stageAt h d s
  let tiles := advisedStage h d π s
  let choices := ProtocolRAMPurchaseOwners.successor tiles (Fintype.equivFin sh.Group).toEmbedding
    (D:=S.degree) (portDigits (S.rows sh.span))
  scanPaths (PurchaseDFS.candidates choices depth) marked

/-- Starting with a fixed positive fraction of all stage rows marked, the actual fixed
sampler addresses and the chosen permutation's real occupied sockets yield linearly many
vertex-disjoint purchases. The sampler and threshold do not depend on the matching. -/
theorem advised_purchases_linear {C : Type*} [Fintype C] [Nonempty C] {d : ℕ}
    (hd : 1 ≤ d) (depth : ℕ) {β : ℝ} (positive : 0 < β) :
    ∃ S : PurchaseSampler, ∀ᶠ h : ℕ in atTop, ∀ (π : Equiv.Perm (Fin (2^h)))
      (marked : StageAt h d → C → Finset (Fin (2^h))),
      let tiles := (permutationFabric h d).shapes.length*(2:ℝ)^h
      β*tiles ≤ ∑ s, ∑ c, ((marked s c).card:ℝ) →
      β*tiles/(2*(depth+1:ℕ)) ≤ ∑ s, ∑ c, ((advisedPurchases S π s depth (marked s c)).1.length:ℝ) := by
  classical
  obtain ⟨δ,pos,event⟩ := acquire_native_linear (C:=C) (H:=depth+1) hd (Nat.succ_pos _) positive
  obtain ⟨S,good⟩ := purchase_sampler pos
  refine ⟨S,?_⟩
  filter_upwards [event] with h stageBound
  intro π marked tiles many
  let leftover (g : AllGroups h d) (c : C) :=
    ((advisedPurchases S π g.1 depth (marked g.1 c)).2.filter fun r => (advisedStage h d π g.1).group r=g.2).card
  apply stageBound (fun s c => (advisedPurchases S π s depth (marked s c)).1.length)
    (fun s c => (marked s c).card) leftover _ _ many
  · intro s c
    let p := advisedStage h d π s
    let sh := stageAt h d s
    let choices := ProtocolRAMPurchaseOwners.successor p (Fintype.equivFin sh.Group).toEmbedding
      (D:=S.degree) (portDigits (S.rows sh.span))
    have account := (PurchaseDFS.purchase_spec choices depth (marked s c)).2.2
    let remain := (advisedPurchases S π s depth (marked s c)).2
    have allGroups : remain.card = ∑ g, (remain.filter fun r => p.group r=g).card :=
      Finset.card_eq_sum_card_fiberwise (fun r _ => Finset.mem_univ (p.group r))
    change _+remain.card=_ at account
    rw [allGroups] at account
    exact account
  · intro g c
    let sh := stageAt h d g.1
    have hz : 0 < sh.span := lt_of_lt_of_le (Nat.two_pow_pos _) (template_dyadic hd sh (List.get_mem ..)).span_lower
    have ha : 0 < ⌈δ*sh.span⌉₊ := Nat.ceil_pos.mpr (mul_pos pos (by exact_mod_cast hz))
    exact native_group_residue (advisedStage h d π g.1) (Fintype.equivFin sh.Group).toEmbedding
      (S.rows sh.span) (S.out_degree sh.span) ha (good sh.span hz) depth (marked g.1 c) g.2

end
end Hierarchy.ProbeStage

end OAI
