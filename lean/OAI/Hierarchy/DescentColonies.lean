import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # The propagated dyadic colonies in a compiler subround -/

namespace Hierarchy.DescentColonies
open scoped BigOperators Classical
noncomputable section

abbrev Block (k : ℕ) := Fin (2^k)

/-- The width and quotient identify the actual contiguous dyadic interval. -/
def width (k d : ℕ) := 2^(k-d)
def group {k : ℕ} (d : ℕ) (i : Block k) := i.val / width k d
def interval {k : ℕ} (d : ℕ) (i : Block k) : Finset (Block k) :=
  Finset.univ.filter fun j => group d j=group d i

private theorem width_pos (k d : ℕ) : 0<width k d := Nat.two_pow_pos _

/-- Offsets in one interval are distinct. This holds even below the final
depth, where every valid interval is a singleton. -/
theorem interval_card {k : ℕ} (d : ℕ) (i : Block k) : (interval d i).card≤width k d := by
  let offset (j : interval d i) : Fin (width k d) := ⟨j.val.val%width k d, Nat.mod_lt _ (width_pos k d)⟩
  have inject : Function.Injective offset := by
    intro a b h
    apply Subtype.ext
    apply Fin.ext
    have q (x : interval d i) : x.val.val/width k d=i.val/width k d :=
      (Finset.mem_filter.mp x.property).2
    have m := congrArg Fin.val h
    change a.val.val%width k d=b.val.val%width k d at m
    calc
      _ = a.val.val%width k d+width k d*(a.val.val/width k d) := (Nat.mod_add_div _ _).symm
      _ = b.val.val := by rw [m,q a,←q b,Nat.mod_add_div]
  simpa using Fintype.card_le_of_injective offset inject

theorem group_ancestor {k d e : ℕ} (small : d≤e) {x y : Block k} (eq : group e x=group e y) :
    group d x=group d y := by
  have exp : k-d=(k-e)+((k-d)-(k-e)) := by omega
  have factor : width k d=width k e*2^((k-d)-(k-e)) := by
    unfold width
    rw [←pow_add,←exp]
  change x.val/width k e=y.val/width k e at eq
  simp only [group,factor,← Nat.div_div_eq_div_mul,eq]

variable {k : ℕ} {V : Type*}

def mass (load : V → Block k → ℕ) (v : V) (d : ℕ) (x : Block k) :=
  ∑ i ∈ interval d x, load v i

/-- The least closure of overloaded intervals under parent and neighbor ancestry.
Equality of actual interval identifiers makes every split a decision for its
entire interval, even when neighboring marks originate at a different block. -/
inductive Split (load : V → Block k → ℕ) (adj : V → V → Prop) (D cap : ℕ) :
    V → ℕ → Block k → Prop
  | heavy {v d x} (h : cap<mass load v d x) : Split load adj D cap v d x
  | parent {v d x} (h : Split load adj D cap v (d+1) x) : Split load adj D cap v d x
  | neighbor {v z d x} (edge : adj v z) (h : Split load adj D cap v (d+D) x) : Split load adj D cap z d x
  | same {v d x y} (q : group d x=group d y) (h : Split load adj D cap v d x) : Split load adj D cap v d y

variable (load : V → Block k → ℕ) (adj : V → V → Prop) (D a B : ℕ)
variable (limit : ∀ v i, load v i≤B)
include limit

theorem split_shallow {v : V} {d : ℕ} {x : Block k}
    (h : Split load adj D (2^a*B) v d x) : d<k-a := by
  induction h with
  | @heavy v d x h =>
    by_contra! deep
    have wei : width k d≤2^a := Nat.pow_le_pow_right (by decide) (show k-d≤a by omega)
    have bound : mass load v d x ≤ (interval d x).card*B := by
      simpa [mass] using (Finset.sum_le_sum (s:=interval d x) fun i _ => limit v i)
    exact (not_lt_of_ge (bound.trans (Nat.mul_le_mul_right B ((interval_card d x).trans wei)))) h
  | parent h ih => omega
  | neighbor edge h ih => omega
  | same _ _ ih => exact ih

private theorem stop (v : V) (x : Block k) :
    ∃ d, ¬Split load adj D (2^a*B) v d x :=
  ⟨k-a,fun h => (Nat.lt_irrefl _) (split_shallow load adj D a B limit h)⟩

/-- The first unsplit interval containing the actual old block x. -/
def depth (v : V) (x : Block k) :=
  Nat.find (stop load adj D a B limit v x)

theorem depth_le (v : V) (x : Block k) :
    depth load adj D a B limit v x≤k-a := by
  apply Nat.find_min'
  exact fun h => (Nat.lt_irrefl _) (split_shallow load adj D a B limit h)

theorem earlier_split (v : V) (x : Block k) {d : ℕ} (lt : d<depth load adj D a B limit v x) :
    Split load adj D (2^a*B) v d x := by
  by_contra none
  exact (Nat.not_le_of_lt lt) (Nat.find_min' (stop load adj D a B limit v x) none)

theorem leaf_load (v : V) (x : Block k) :
    mass load v (depth load adj D a B limit v x) x ≤2^a*B := by
  apply Nat.le_of_not_gt
  exact fun heavy => Nat.find_spec (stop load adj D a B limit v x) (.heavy heavy)

theorem leaf_width (ha : a≤k) (v : V) (x : Block k) :
    2^a≤width k (depth load adj D a B limit v x) := by
  have h := depth_le load adj D a B limit v x
  apply Nat.pow_le_pow_right (by decide)
  omega

/-- The depth of the leaf is constant on its interval. -/
theorem leaf_constant (v : V) {x y : Block k}
    (same : group (depth load adj D a B limit v x) x=group (depth load adj D a B limit v x) y) :
    depth load adj D a B limit v y=depth load adj D a B limit v x := by
  let dx := depth load adj D a B limit v x
  let dy := depth load adj D a B limit v y
  have first : dy≤dx := Nat.find_min' _ fun split =>
    Nat.find_spec (stop load adj D a B limit v x) (.same same.symm split)
  apply Nat.le_antisymm first
  apply Nat.find_min'
  intro split
  exact Nat.find_spec (stop load adj D a B limit v y) (.same (group_ancestor first same) split)

/-- If leaves at neighboring positions meet at a block, their depths differ
by at most D, hence their lengths have ratio at most 2^D. -/
theorem neighbor_depth {v z : V} (edge : adj v z) (x : Block k) :
    depth load adj D a B limit v x≤depth load adj D a B limit z x+D := by
  apply Nat.find_min'
  intro split
  exact Nat.find_spec (stop load adj D a B limit z x) (.neighbor edge split)

theorem neighbor_width {v z : V} (edge : adj v z) (x : Block k) :
    width k (depth load adj D a B limit z x) ≤ 2^D*width k (depth load adj D a B limit v x) := by
  have h := neighbor_depth load adj D a B limit edge x
  have h' := depth_le load adj D a B limit v x
  rw [width,width,←pow_add]
  apply Nat.pow_le_pow_right (by decide)
  omega

end
end Hierarchy.DescentColonies

end OAI
