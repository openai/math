import OAI.Computability.NearSquareRoot.PhysicalWalshNode

/-! # Coordinates of a physical nonterminal Walsh node -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FlatWalshNode

open KernelPass PhysicalWalshNode

abbrev NodeAddress (a : ℕ) (s : Shape) := Addr (a+1) ((a+1)^(s.level-1))

abbrev axisSize (a : ℕ) (s : Shape) := 2^((a+1)*(2*((a+1)^(s.level-1))))

theorem inner_eq (a : ℕ) (s : Shape) (hl : 0 < s.level) :
    PhysicalWalshNode.inner (a+1) s = axisSize a s * s.suff := by
  have he : 2*(a+1)^s.level = (a+1)*(2*(a+1)^(s.level-1)) := by
    nth_rw 1 [← Nat.sub_add_cancel hl]
    rw [pow_succ]; ring
  simp only [PhysicalWalshNode.inner, grow, axisSize, he]

/-- Ordinal in a lane, with one group of active addresses for each prefix. -/
def rowPos (a : ℕ) (s : Shape) (g : ℕ) (u : NodeAddress a s) (t : Fin s.suff) : ℕ :=
  (g*axisSize a s + (KernelScaleLayout.rank u).val)*s.suff+t.val

private def rect (a W : ℕ) (s : Shape) :
    ((Fin (groups W s) × Fin W × Fin s.suff) × NodeAddress a s) ≃
      ((Fin (groups W s) × Fin W) × (Fin (axisSize a s) × Fin s.suff)) where
  toFun x := ((x.1.1,x.1.2.1), (KernelScaleLayout.rank x.2,x.1.2.2))
  invFun x := ((x.1.1,x.1.2,x.2.2), KernelScaleLayout.address a _ x.2.1)
  left_inv _ := by simp only [KernelScaleLayout.address_rank]
  right_inv x := by
    rcases x with ⟨⟨g,b⟩,n,t⟩
    change ((g,b), KernelScaleLayout.rank (KernelScaleLayout.address a ((a+1)^(s.level-1)) n),t) = _
    rw [KernelScaleLayout.rank_address (a := a) (h := (a+1)^(s.level-1)) n]

/-- Group, lane, trailing spectator and all active paired kernel coordinates. -/
def chart (a W : ℕ) (s : Shape) (hl : 0 < s.level) (hd : W^s.level ∣ s.pref) :
    Fin (count (a+1) s) ≃ (Fin (groups W s) × Fin W × Fin s.suff) × NodeAddress a s :=
  ((((rect a W s).trans (Equiv.prodCongr finProdFinEquiv finProdFinEquiv)).trans
    finProdFinEquiv).trans (finCongr (by rw [count, groups_mul hl hd, inner_eq a s hl]))).symm

theorem chart_symm_val (a W : ℕ) (s : Shape) (hl : 0 < s.level) (hd : W^s.level ∣ s.pref)
    (g : Fin (groups W s)) (b : Fin W) (t : Fin s.suff) (u : NodeAddress a s) :
    ((chart a W s hl hd).symm ((g,b,t),u)).val = rowPos a s (g.val*W+b.val) u t := by
  change (t.val + s.suff * (KernelScaleLayout.rank u).val) +
    (axisSize a s*s.suff)*(b.val+W*g.val) = _
  unfold rowPos; ring

private def laneRect (a W : ℕ) (s : Shape) :
    ((Fin (groups W s) × Fin s.suff) × NodeAddress a s) ≃
      (Fin (groups W s) × (Fin (axisSize a s) × Fin s.suff)) where
  toFun x := (x.1.1, KernelScaleLayout.rank x.2, x.1.2)
  invFun x := ((x.1,x.2.2), KernelScaleLayout.address a _ x.2.1)
  left_inv _ := by simp only [KernelScaleLayout.address_rank]
  right_inv x := by
    rcases x with ⟨g,n,t⟩
    change (g, KernelScaleLayout.rank (KernelScaleLayout.address a ((a+1)^(s.level-1)) n),t) = _
    rw [KernelScaleLayout.rank_address (a := a) (h := (a+1)^(s.level-1)) n]

/-- Restriction of the physical array layout to any particular batch lane. -/
def laneChart (a W : ℕ) (s : Shape) (hl : 0 < s.level) :
    Fin (groups W s * PhysicalWalshNode.inner (a+1) s) ≃
      (Fin (groups W s) × Fin s.suff) × NodeAddress a s :=
  ((((laneRect a W s).trans (Equiv.prodCongr (Equiv.refl _) finProdFinEquiv)).trans
    finProdFinEquiv).trans (finCongr (by rw [inner_eq a s hl]))).symm

theorem laneChart_symm_val (a W : ℕ) (s : Shape) (hl : 0 < s.level)
    (g : Fin (groups W s)) (t : Fin s.suff) (u : NodeAddress a s) :
    ((laneChart a W s hl).symm ((g,t),u)).val = rowPos a s g u t := by
  change (t.val+s.suff*(KernelScaleLayout.rank u).val)+(axisSize a s*s.suff)*g.val = _
  unfold rowPos; ring

theorem rowPos_local_lt (a : ℕ) (s : Shape) (hl : 0 < s.level)
    (u : NodeAddress a s) (t : Fin s.suff) : rowPos a s 0 u t < PhysicalWalshNode.inner (a+1) s := by
  have h := (finProdFinEquiv ((KernelScaleLayout.rank u),t)).isLt
  change t.val+s.suff*(KernelScaleLayout.rank u).val < axisSize a s*s.suff at h
  rw [inner_eq a s hl]
  simpa [rowPos, Nat.add_comm, Nat.mul_comm] using h

theorem rowPos_block (a : ℕ) (s : Shape) (hl : 0 < s.level)
    (g : ℕ) (u : NodeAddress a s) (t : Fin s.suff) :
    rowPos a s g u t = g*PhysicalWalshNode.inner (a+1) s + rowPos a s 0 u t := by
  rw [inner_eq a s hl]; unfold rowPos; ring

theorem rowPos_div (a : ℕ) (s : Shape) (hl : 0 < s.level)
    (g : ℕ) (u : NodeAddress a s) (t : Fin s.suff) :
    rowPos a s g u t / PhysicalWalshNode.inner (a+1) s = g := by
  have p : 0 < PhysicalWalshNode.inner (a+1) s := Nat.mul_pos (by positivity) s.suff_pos
  rw [rowPos_block a s hl g, Nat.mul_comm g, Nat.mul_add_div p,
    Nat.div_eq_of_lt (rowPos_local_lt a s hl u t), Nat.add_zero]

theorem rowPos_mod (a : ℕ) (s : Shape) (hl : 0 < s.level)
    (g : ℕ) (u : NodeAddress a s) (t : Fin s.suff) :
    rowPos a s g u t % PhysicalWalshNode.inner (a+1) s = rowPos a s 0 u t := by
  rw [rowPos_block a s hl g, Nat.mul_comm g, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (rowPos_local_lt a s hl u t)]

theorem lane_chart (a W : ℕ) (s : Shape) (hl : 0 < s.level) (hd : W^s.level ∣ s.pref)
    (x : Data s) (g : Fin (groups W s)) (b : Fin W) (t : Fin s.suff) (u : NodeAddress a s) :
    lane (a+1) W s x b (rowPos a s g u t) = x ((chart a W s hl hd).symm ((g,b,t),u)) := by
  rw [lane, rowPos_div a s hl, rowPos_mod a s hl, chart_symm_val, rowPos_block a s hl (g.val*W+b.val)]

theorem unlane_chart (a W : ℕ) (hW : 0 < W) (s : Shape) (hl : 0 < s.level)
    (hd : W^s.level ∣ s.pref) (x : Fin W → Data s)
    (g : Fin (groups W s)) (b : Fin W) (t : Fin s.suff) (u : NodeAddress a s) :
    unlane (a+1) hW s x ((chart a W s hl hd).symm ((g,b,t),u)) = x b (rowPos a s g u t) := by
  rw [unlane, chart_symm_val]
  apply congrArg₂ x
  · apply Fin.ext
    change (rowPos a s (g.val*W+b.val) u t / PhysicalWalshNode.inner (a+1) s) % W = b.val
    rw [rowPos_div a s hl, Nat.mul_comm g.val W, Nat.mul_add_mod, Nat.mod_eq_of_lt b.isLt]
  · rw [rowPos_div a s hl, rowPos_mod a s hl, Nat.mul_comm g.val W, Nat.mul_add_div hW,
      Nat.div_eq_of_lt b.isLt, Nat.add_zero, rowPos_block a s hl g.val]

theorem rowPos_suffix (a : ℕ) (s : Shape) (g : ℕ) (u : NodeAddress a s) (t : Fin s.suff) :
    rowPos a s g u t % s.suff = t.val ∧
      rowPos a s g u t / s.suff = g*axisSize a s + (KernelScaleLayout.rank u).val := by
  unfold rowPos
  rw [Nat.mul_comm _ s.suff, Nat.mul_add_mod, Nat.mod_eq_of_lt t.isLt, Nat.mul_add_div s.suff_pos,
    Nat.div_eq_of_lt t.isLt, Nat.add_zero]
  exact ⟨rfl,rfl⟩

theorem coord_rowPos (a W : ℕ) (s : Shape) (g : ℕ) (u : NodeAddress a s) (t : Fin s.suff) :
    (coords a W).coord s (rowPos a s g u t) = u := by
  change KernelScaleLayout.address a _ ((rowPos a s g u t / s.suff) % axisSize a s) = u
  rw [(rowPos_suffix a s g u t).2, Nat.mul_comm g, Nat.mul_add_mod,
    Nat.mod_eq_of_lt (KernelScaleLayout.rank u).isLt, KernelScaleLayout.address_rank]

theorem xorIndex_rowPos (a : ℕ) (gate : Fin (a+1) × Fin (a+1)) (s : Shape)
    (g : ℕ) (u : NodeAddress a s) (t : Fin s.suff) :
    xorIndex a gate s (rowPos a s g u t) =
      rowPos a s g (xorColumn gate ∘ u) t := by
  have h := coord_rowPos a 1 s g u t
  change KernelScaleLayout.coord a _ _ _ = u at h
  have pos : 0 < axisSize a s := by unfold axisSize; positivity
  change ((rowPos a s g u t / s.suff / axisSize a s * axisSize a s +
      (KernelScaleLayout.rank (xorColumn gate ∘ _)).val)*s.suff+rowPos a s g u t % s.suff) = _
  rw [h, (rowPos_suffix a s g u t).1, (rowPos_suffix a s g u t).2, Nat.mul_comm g,
    Nat.mul_add_div pos, Nat.div_eq_of_lt (KernelScaleLayout.rank u).isLt, Nat.add_zero]
  rfl

end FlatWalshNode

end NearSquareRoot
end Computability
end OAI
