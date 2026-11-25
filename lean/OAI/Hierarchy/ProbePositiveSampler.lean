import OAI.Hierarchy.ProbeAdvisedPurchase

namespace OAI
/-! # A positive native port span on the sampler used for every input -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ProtocolRAM Filter
open scoped BigOperators Classical
noncomputable section

/-- Public guarantee on the actual maximal-DFS output for arbitrary frozen marks. -/
def AdvisedCoverage (S : PurchaseSampler) (d k depth : ℕ) (T : ℝ) : Prop :=
  ∀ᶠ h : ℕ in atTop, ∀ (π : Equiv.Perm (Fin (2^h))) (marked : StageAt h d→Fin (2*k)→Finset (Fin (2^h))),
    let tiles:=(permutationFabric h d).shapes.length*(2:ℝ)^h
    T^2/(4*k)*tiles≤∑s,∑j,((marked s j).card:ℝ) →
    T^2/(4*k)*tiles/(2*(depth+1:ℕ))≤∑s,∑j,((advisedPurchases S π s depth (marked s j)).1.length:ℝ)

/-- All positive spans now use the very sampler which passes the native counts.
Increasing the public degree by one provides space for every physical source row. -/
theorem advised_purchases_linear_positive {C : Type*} [Fintype C] [Nonempty C] {d : ℕ}
    (hd : 1 ≤ d) (depth : ℕ) {β : ℝ} (positive : 0 < β) :
    ∃ S : PurchaseSampler, 0<S.degree ∧ ∀ᶠ h : ℕ in atTop, ∀ (π : Equiv.Perm (Fin (2^h)))
      (marked : StageAt h d → C → Finset (Fin (2^h))),
      let tiles := (permutationFabric h d).shapes.length*(2:ℝ)^h
      β*tiles ≤ ∑ s, ∑ c, ((marked s c).card:ℝ) →
      β*tiles/(2*(depth+1:ℕ)) ≤ ∑ s, ∑ c, ((advisedPurchases S π s depth (marked s c)).1.length:ℝ) := by
  classical
  obtain ⟨δ,pos,event⟩ := acquire_native_linear (C:=C) (H:=depth+1) hd (Nat.succ_pos _) positive
  obtain ⟨base,mixing⟩ := purchase_sampler pos
  let S : PurchaseSampler := {base with
    degree:=base.degree+1
    out_degree:=fun m j=>(base.out_degree m j).trans (Nat.le_succ _)
    in_degree:=fun m i=>(base.in_degree m i).trans (Nat.le_succ _)}
  have good : S.Mixes δ := mixing
  refine ⟨S,Nat.succ_pos _,?_⟩
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
