import OAI.Hierarchy.ProbeChainBall
import OAI.Hierarchy.ProbePayload

namespace OAI
/-! # Distinct physical roots of marked chains and exceptional local-price tests -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe
open scoped BigOperators Classical
noncomputable section

/-- Each actual inlet has separate group, port and stage addresses. -/
abbrev Inlet (h d : ℕ) := Σ s : StageAt h d, (stageAt h d s).Port

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

/-- A stage-wise canonical sign assignment ensures the first purchased tile is unique
across different signs as well as inside each individual native MarkTape scan. -/
def boughtRoot (unique : ∀ s c c' r, r∈marked s c → r∈marked s c' → c=c') :
    LiveChains S π depth marked ↪ Inlet h d where
  toFun x := ⟨x.1,(advisedStage h d π x.1).first (liveRow S π depth marked x 0)⟩
  inj' := by
    rintro ⟨s,c,i⟩ ⟨s',c',i'⟩ same
    have stage := congrArg Sigma.fst same
    dsimp at stage; subst s'
    have sites := Sigma.mk.inj_iff.mp same
    have rows := (advisedStage h d π s).first.injective (eq_of_heq sites.2)
    let x : LiveChains S π depth marked := ⟨s,c,i⟩
    let y : LiveChains S π depth marked := ⟨s,c',i'⟩
    have xin := liveSlot_marked S π depth marked x 0
    have yin := liveSlot_marked S π depth marked y 0
    change liveRow S π depth marked x 0=liveRow S π depth marked y 0 at rows
    change liveRow S π depth marked x 0∈marked s c at xin
    change liveRow S π depth marked y 0∈marked s c' at yin
    have member : liveRow S π depth marked x 0∈marked s c' := by rw [rows]; exact yin
    have color := unique s c c' _ xin member
    subst c'
    have indices := (liveDigit S π depth marked s c).injective rows
    have sameIndex := congrArg Prod.fst indices
    exact congrArg (fun j => (⟨s,c,j⟩ : LiveChains S π depth marked)) sameIndex

/-- The actual purchased roots failing a post-purchase test each consume a distinct
summand of total discrepancy. This accounts for exceptionality on every native run. -/
theorem bought_bad_charge (unique : ∀ s c c' r, r∈marked s c → r∈marked s c' → c=c')
    (disc : Inlet h d → ℝ) (nonneg : ∀ r, 0 ≤ disc r) (ε : ℝ) (he : 0 ≤ ε) :
    let root := boughtRoot S π depth marked unique
    let bad := Finset.univ.filter (fun x => ε < disc (root x))
    (bad.card:ℝ)*ε ≤ ∑ r, disc r := by
  classical
  intro root bad
  let failures := Finset.univ.filter (fun r => ε < disc r)
  have sub : bad.map root ⊆ failures := by
    intro r mem
    obtain ⟨x,hx,rfl⟩ := Finset.mem_map.mp mem
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_filter.mp hx).2⟩
  have count : bad.card ≤ failures.card := by simpa only [Finset.card_map] using Finset.card_le_card sub
  exact (mul_le_mul_of_nonneg_right (by exact_mod_cast count) he).trans (exceptional_test_mass disc nonneg ε)

end
end Hierarchy.ProbeStage

end OAI
