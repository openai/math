import OAI.Computability.BorderVNP.CubeGroupWeightLayout

/-! # Exact memory image of the sparse histogram updates -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.GroupWeights

/-- Target symbol and additive increment of one public row. -/
def Phase.target (p : Phase) (l : Layout) (orig : ℕ → ℕ) (i : ℕ) := match p with
  | .init => i | .shared => i/l.groups | .data => l.symbol orig i

/-- Joint-weight increment for a declaration or incoming-cell descriptor. -/
def Phase.delta (p : Phase) (l : Layout) (orig : ℕ → ℕ) (i : ℕ) := match p with
  | .init => 0
  | .shared => 1000000*l.rowCharge orig i (i/l.groups)
  | .data => 1000000*orig (l.demands+i)

/-- Store the initial raw charge or add the incident contribution to its actual symbol. -/
def Phase.step (p : Phase) (l : Layout) (orig mem : ℕ → ℕ) (i : ℕ) :=
  let addr := l.weights + p.target l orig i
  Function.update mem addr (if p = .init then l.raw else mem addr+p.delta l orig i)

/-- Every target belongs to the actual alphabet. -/
theorem Phase.target_lt {l : Layout} {orig : ℕ → ℕ} (p : Phase) (hd : 0 < l.groups)
    {i : ℕ} (hi : i < p.count l) : p.target l orig i < l.groups := by
  cases p with
  | init => exact hi
  | shared => exact (Nat.div_lt_iff_lt_mul hd).2 hi
  | data => exact Nat.mod_lt _ hd

private theorem charge_target (p : Phase) (hp : p ≠ .init) (l : Layout)
    (orig : ℕ → ℕ) (i : ℕ) :
    p.value l orig (i+1) (p.target l orig i) =
      p.value l orig i (p.target l orig i) + p.delta l orig i := by
  cases p with
  | init => contradiction
  | shared =>
    simp [Phase.value,Phase.target,Phase.delta,TeamNative.scaledWeight,Layout.sharedTotal,
      Finset.sum_range_succ,Nat.mul_add]
    omega
  | data =>
    simp [Phase.value,Phase.target,Phase.delta,TeamNative.scaledWeight,Layout.dataTotal,
      Layout.dataCharge,Finset.sum_range_succ,Nat.mul_add]
    omega

/-- A total-word bound controls every intermediate additive update of the RAM pass. -/
theorem Image.incrementFits {p : Phase} {l : Layout} {orig mem : ℕ → ℕ} {i w : ℕ}
    (h : Image p l orig mem i) (f : l.Fits w orig) (hp : p ≠ .init) (hi : i < p.count l) :
    mem (l.weights+p.target l orig i)+p.delta l orig i < 2^w := by
  have ht := p.target_lt (orig := orig) f.positive hi
  rw [h.weights _ ht, ← charge_target p hp]
  exact (value_le_weight p hp _ _ hi).trans_lt (f.weightsFit _ ht)

/-- A single concrete store moves the exact histogram image to its next prefix. -/
theorem Image.advance {p : Phase} {l : Layout} {orig mem : ℕ → ℕ} {i : ℕ}
    (h : Image p l orig mem i) (hd : 0 < l.groups) (hi : i < p.count l) :
    Image p l orig (p.step l orig mem i) (i+1) := by
  have ht := p.target_lt (orig := orig) hd hi
  constructor
  · intro s hs
    by_cases he : s = p.target l orig i
    · subst s
      rw [Phase.step, Function.update_self]
      by_cases hp : p = .init
      · subst p
        simp [Phase.value,Phase.target]
      · rw [ite_eq_right hp, h.weights _ ht, ← charge_target p hp]
    · rw [Phase.step, Function.update_of_ne (show l.weights+s ≠ l.weights+p.target l orig i by omega),
        h.weights _ hs]
      cases p with
      | init =>
        change s ≠ i at he
        simp [Phase.value, show s < i+1 ↔ s < i by omega]
      | shared =>
        change s ≠ i/l.groups at he
        simp [Phase.value,Layout.sharedTotal,Finset.sum_range_succ,Layout.rowCharge,Ne.symm he]
      | data =>
        change s ≠ l.symbol orig i at he
        simp [Phase.value,Layout.dataTotal,Finset.sum_range_succ,Layout.dataCharge,Ne.symm he]
  · intro a ha
    rw [Phase.step,Function.update_of_ne (ha _ ht)]
    exact h.outside a ha

end Cube.GroupWeights

end BorderVNP
end Computability
end OAI
