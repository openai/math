import OAI.Hierarchy.DescentColonyLayout
import OAI.Hierarchy.DescentColonyOrigins
import OAI.Hierarchy.DescentBaseOverload

namespace OAI
/-! # Reading actual dyadic loads through the selected invertible layout -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped Classical BigOperators
noncomputable section

variable {k : ℕ} {V : Type*}

def rearrangedLoad (load : V → Block k → ℕ) (L : Layout k) (v : V) (i : Block k) : ℕ :=
  load v ((rearrange L).symm i)

def normalized (load : V → Block k → ℕ) (scale : ℝ) (v : V) (i : Block k) : ℝ :=
  (load v i : ℝ)/scale

def bin {d : ℕ} (hd : d≤k) (x : Block k) : Block d :=
  ⟨group d x,by
    apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos (k-d))).mpr
    rw [←pow_add,show d+(k-d)=k by omega]
    exact x.isLt⟩

/-- The weighted bin on the original block IDs equals the load of the actual
contiguous interval after placing those blocks in the linear layout. -/
theorem bin_mass (weight : V → Block k → ℕ) (scale : ℝ) (v : V) {d : ℕ}
    (hd : d≤k) (L : Layout k) (x : Block k) :
    DescentBaseVariance.load (dyadicLayout hd L) (normalized weight scale v) (bin hd x)=
      (mass (rearrangedLoad weight L) v d x:ℝ)/scale := by
  have matchId (i : Block k) : bin hd x=dyadicLayout hd L i ↔ group d (rearrange L i)=group d x := by
    rw [Fin.ext_iff,layout_id]
    exact eq_comm
  unfold DescentBaseVariance.load mass interval
  rw [Finset.sum_filter]
  push_cast
  rw [Finset.sum_div]
  have order := Equiv.sum_comp (rearrange L) (fun i =>
    (if group d i=group d x then (rearrangedLoad weight L v i:ℝ) else 0)/scale)
  rw [←order]
  apply Finset.sum_congr rfl
  intro i _
  simp only [matchId,rearrangedLoad,Equiv.symm_apply_apply,normalized]
  split <;> simp_all

/-- Integer initial marks inject into the normalized overloaded bins counted by
the level estimator. The threshold factor t will be 1 for colonies and 2 for
reset bases. -/
theorem initialIds_le_normalized (weight : V → Block k → ℕ) (scale t : ℕ)
    (pos : 0<scale) (v : V) {d : ℕ} (hd : d≤k) (L : Layout k) :
    (initialIds (rearrangedLoad weight L) (t*scale) v d).card ≤
      (Finset.univ.filter fun j => (t:ℝ)<DescentBaseVariance.load (dyadicLayout hd L)
        (normalized weight scale v) j).card := by
  let heavy := Finset.univ.filter fun j => (t:ℝ)<DescentBaseVariance.load (dyadicLayout hd L)
    (normalized weight scale v) j
  apply (Finset.card_le_card (t:=heavy.image Fin.val) ?_).trans Finset.card_image_le
  intro a marked
  obtain ⟨x,h,rfl⟩ := Finset.mem_image.mp marked
  have raw := (Finset.mem_filter.mp h).2
  refine Finset.mem_image.mpr ⟨bin hd x,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
  rw [bin_mass]
  apply (lt_div_iff₀ (by exact_mod_cast pos)).mpr
  exact_mod_cast raw

/-- The estimator of Section 4.3 bounds the number of actual heavy address
intervals at this position and this level of the chosen layout. -/
theorem actual_level_charge (weight : V → Block k → ℕ) (scale : ℕ) (pos : 0<scale) (v : V)
    {d : ℕ} (hd : d≤k) (L : Layout k) (s : ℕ) (F : ℝ)
    (small : ∀i,weight v i≤scale) (avg : mean (normalized weight scale v) (Block d)≤1) :
    ((initialIds (rearrangedLoad weight L) (2*scale) v d).card:ℝ) ≤
      levelCharge s F (dyadicLayout hd L) (normalized weight scale v) := by
  let bins := Finset.univ.filter fun j => (2:ℝ)<DescentBaseVariance.load (dyadicLayout hd L)
    (normalized weight scale v) j
  have count : ((initialIds (rearrangedLoad weight L) (2*scale) v d).card:ℝ)≤bins.card := by
    exact_mod_cast initialIds_le_normalized weight scale 2 pos v hd L
  apply count.trans
  apply (marked_bins s F (dyadicLayout hd L) (normalized weight scale v) ?_ ?_ avg).1
  · intro i
    dsimp [normalized]
    positivity
  · intro i
    apply (div_le_one (by exact_mod_cast pos : (0:ℝ)<scale)).2
    exact_mod_cast small i

end
end Hierarchy.DescentColonies

end OAI
