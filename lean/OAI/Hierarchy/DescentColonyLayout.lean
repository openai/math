import OAI.Hierarchy.DescentColonies
import OAI.Hierarchy.DescentLinearLayouts

namespace OAI
/-! # Binary linear layouts of the actual contiguous block addresses -/

namespace Hierarchy.DescentColonies
open DescentGL DescentBaseVariance
open scoped Classical BigOperators
noncomputable section

/-- The first row is the most significant bit so that linear prefixes coincide
simultaneously with all contiguous dyadic address intervals. -/
def value : (k : ℕ) → Bits k → ℕ
  | 0,_ => 0
  | k+1,x => 2*value k (headRows (Nat.le_succ k) x)+(x (Fin.last k)).val

private theorem value_lt (k : ℕ) (x : Bits k) : value k x<2^k := by
  induction k with
  | zero => simp [value]
  | succ k ih =>
    have old := ih (headRows (Nat.le_succ k) x)
    have last := ZMod.val_lt (x (Fin.last k))
    rw [value,pow_succ]
    omega

private theorem value_injective (k : ℕ) : Function.Injective (value k) := by
  induction k with
  | zero => exact fun _ _ _ => Subsingleton.elim _ _
  | succ k ih =>
    intro x y eqn
    change 2*value k (headRows (Nat.le_succ k) x)+(x (Fin.last k)).val =
      2*value k (headRows (Nat.le_succ k) y)+(y (Fin.last k)).val at eqn
    have lx := ZMod.val_lt (x (Fin.last k))
    have ly := ZMod.val_lt (y (Fin.last k))
    have old := ih (show value k (headRows (Nat.le_succ k) x)=value k (headRows (Nat.le_succ k) y) by omega)
    funext i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · exact (ZMod.val_injective 2) (by omega)
    · exact congrFun old j

def address (k : ℕ) : Bits k ≃ Block k :=
  let f := fun x : Bits k => (⟨value k x,value_lt k x⟩ : Block k)
  Equiv.ofBijective f <| (Fintype.bijective_iff_injective_and_card f).2
    ⟨fun _ _ h => value_injective k (congrArg Fin.val h),by simp []⟩

theorem prefix_value {k d : ℕ} (hd : d≤k) (x : Bits k) :
    group d (address k x)=value d (headRows hd x) := by
  induction k with
  | zero =>
    obtain rfl : d=0 := by omega
    change 0 / 2^(0-0)=0
    decide
  | succ k ih =>
    rcases Nat.eq_or_lt_of_le hd with eq | lt
    · subst d
      have self : headRows hd x=x := funext fun _=>rfl
      simp [group,width,address,self]
    · have le : d≤k := by omega
      have tail := ih le (headRows (Nat.le_succ k) x)
      change value k (headRows (Nat.le_succ k) x)/2^(k-d)=_ at tail
      change (2*value k (headRows (Nat.le_succ k) x)+(x (Fin.last k)).val)/2^(k+1-d)=_
      have exponent : k+1-d=(k-d)+1 := by omega
      have bit := ZMod.val_lt (x (Fin.last k))
      rw [exponent,pow_succ,mul_comm ((2:ℕ)^(k-d)) 2,←Nat.div_div_eq_div_mul]
      have half : (2*value k (headRows (Nat.le_succ k) x)+(x (Fin.last k)).val)/2 =
          value k (headRows (Nat.le_succ k) x) := by omega
      rw [half,tail]
      rfl

/-- Every chosen invertible matrix acts by a genuine permutation of the original
block set. The same permutation is used at every position and every depth. -/
def rearrange {k : ℕ} (L : Layout k) : Equiv.Perm (Block k) :=
  (address k).symm.trans (L.toEquiv.trans (address k))

def dyadicLayout {k d : ℕ} (hd : d≤k) (L : Layout k) (x : Block k) : Block d :=
  address d (headRows hd (L ((address k).symm x)))

theorem layout_id {k d : ℕ} (hd : d≤k) (L : Layout k) (x : Block k) :
    (dyadicLayout hd L x).val=group d (rearrange L x) := (prefix_value hd _).symm

/-- Actual address layouts meet the same collision bound as the underlying
binary row system, with the entire linear permutation shared across levels. -/
theorem real_layout_pairs {k d : ℕ} (hd : d≤k) : PairBound (dyadicLayout hd) := by
  intro x y ne
  have result := DescentLinearLayouts.pairBound k d hd ((address k).symm x) ((address k).symm y)
    (fun h => ne ((address k).symm.injective h))
  have cardEq : Fintype.card (Block d)=Fintype.card (Bits d) := Fintype.card_congr (address d).symm
  rw [cardEq]
  apply le_trans _ result
  apply le_of_eq
  unfold collision
  congr 2
  apply congrArg Finset.card
  ext L
  simp [dyadicLayout,DescentLinearLayouts.layout]
  let pred := fun a : Layout k => DescentLinearLayouts.layout hd a ((address k).symm x) =
    DescentLinearLayouts.layout hd a ((address k).symm y)
  have mem := @Finset.mem_filter (Layout k) pred (fun a=>Classical.propDecidable (pred a))
    Finset.univ L
  exact ⟨fun h=>mem.mpr ⟨Finset.mem_univ _,h⟩,fun h=>(mem.mp h).2⟩

end
end Hierarchy.DescentColonies

end OAI
