import OAI.Computability.VPVNP.GrammarLabels
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Scratch addresses for preorder parsing

One row of the input rectangle belongs to each site in each of the two
groups. After these rows are two planes for pending stack frames, one mark
per position, one word per production, and one word for the stack depth.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

/-- Separate logical locations in the physical scratch interval. -/
abbrev Cell (R n m T : ℕ) :=
  ((Fin 2 × Fin R) × Fin m) ⊕ Fin n ⊕ Fin n ⊕ Fin m ⊕ Fin T ⊕ Fin 1

/-- Number of words in the parser scratch interval, comprising two groups of input rows, two
stack planes, position marks, production counters, and the stack depth. -/
def size (R n m T : ℕ) := 2 * R * m + (n + (n + (m + (T + 1))))

/-- Row-major address of every typed cell, contiguous across the six regions. -/
def cellOffset (R n m T : ℕ) : Cell R n m T ≃ Fin (size R n m T) :=
  let hist := ((Equiv.refl (Fin T)).sumCongr (Equiv.refl (Fin 1))).trans finSumFinEquiv
  let marks := ((Equiv.refl (Fin m)).sumCongr hist).trans finSumFinEquiv
  let states := ((Equiv.refl (Fin n)).sumCongr marks).trans finSumFinEquiv
  let degrees := ((Equiv.refl (Fin n)).sumCongr states).trans finSumFinEquiv
  let rows := (finProdFinEquiv.prodCongr (Equiv.refl (Fin m))).trans finProdFinEquiv
  (rows.sumCongr degrees).trans finSumFinEquiv

variable {R n m T : ℕ}

/-- External word address of a typed parser cell, obtained by adding its offset in the scratch
layout to `base`. -/
def address (base : ℕ) (c : Cell R n m T) := base + (cellOffset R n m T c).val

theorem address_injective (base : ℕ) : Function.Injective (address (R := R) (n := n) (m := m) (T := T) base) :=
  fun _ _ h => (cellOffset R n m T).injective (Fin.ext (Nat.add_left_cancel h))

theorem address_lt {base w : ℕ} (hfit : base + size R n m T ≤ 2 ^ w) (c : Cell R n m T) :
    address base c < 2 ^ w :=
  (Nat.add_lt_add_left (cellOffset R n m T c).isLt base).trans_le hfit

theorem address_input (base : ℕ) (g : Fin 2) (s : Fin R) (j : Fin m) :
    address (n := n) (T := T) base (.inl ((g, s), j)) = base + (g.val * R + s.val) * m + j.val := by
  change base + (j.val + m * (s.val + R * g.val)) = _
  ring

theorem address_degree (base : ℕ) (j : Fin n) :
    address (R := R) (m := m) (T := T) base (.inr (.inl j)) = base + 2*R*m + j.val := by
  change base + (2*R*m + j.val) = _
  omega

theorem address_state (base : ℕ) (j : Fin n) :
    address (R := R) (m := m) (T := T) base (.inr (.inr (.inl j))) = base + 2*R*m + n + j.val := by
  change base + (2*R*m + (n + j.val)) = _
  omega

theorem address_mark (base : ℕ) (j : Fin m) :
    address (R := R) (n := n) (T := T) base (.inr (.inr (.inr (.inl j)))) =
      base + 2*R*m + 2*n + j.val := by
  change base + (2*R*m + (n + (n + j.val))) = _
  omega

theorem address_hist (base : ℕ) (j : Fin T) :
    address (R := R) (n := n) (m := m) base (.inr (.inr (.inr (.inr (.inl j))))) =
      base + 2*R*m + 2*n + m + j.val := by
  change base + (2*R*m + (n + (n + (m + j.val)))) = _
  omega

theorem address_depth (base : ℕ) :
    address (R := R) (n := n) (m := m) (T := T) base (.inr (.inr (.inr (.inr (.inr 0))))) =
      base + 2*R*m + 2*n + m + T := by
  change base + (2*R*m + (n + (n + (m + (T + 0))))) = _
  omega

/-- All legal pairs (degree minus one, split minus one) in triangular order. -/
def splitIndex {n : ℕ} (d : Fin n) (b : Fin d.val) : Fin (n.choose 2) :=
  ⟨d.val.choose 2 + b.val, by
    have hc := Nat.choose_le_choose 2 d.isLt
    rw [Nat.choose_succ_succ d.val 1, Nat.choose_one_right] at hc
    change d.val + d.val.choose 2 ≤ n.choose 2 at hc
    have := b.isLt
    omega⟩

private theorem split_degree_eq {d e : Fin n} {b : Fin d.val} {a : Fin e.val}
    (h : splitIndex d b = splitIndex e a) : d = e := by
  have hv := congrArg Fin.val h
  change d.val.choose 2 + b.val = e.val.choose 2 + a.val at hv
  have upper (i : Fin n) (j : Fin i.val) : i.val.choose 2 + j.val < (i.val + 1).choose 2 := by
    rw [Nat.choose_succ_succ i.val 1, Nat.choose_one_right]
    change i.val.choose 2 + j.val < i.val + i.val.choose 2
    have := j.isLt
    omega
  apply Fin.ext
  rcases lt_trichotomy d.val e.val with hd | hd | hd
  · have := (upper d b).trans_le (Nat.choose_le_choose 2 hd)
    omega
  · exact hd
  · have := (upper e a).trans_le (Nat.choose_le_choose 2 hd)
    omega

private noncomputable def splitEquiv (n : ℕ) : (Σ d : Fin n, Fin d.val) ≃ Fin (n.choose 2) := by
  let f := fun t : Σ d : Fin n, Fin d.val => splitIndex t.1 t.2
  have hinj : Function.Injective f := by
    rintro ⟨d,b⟩ ⟨e,a⟩ he
    obtain rfl := split_degree_eq he
    have hv := congrArg Fin.val he
    change d.val.choose 2 + b.val = d.val.choose 2 + a.val at hv
    obtain rfl := Fin.ext (Nat.add_left_cancel hv)
    rfl
  have hcard : Fintype.card (Σ d : Fin n, Fin d.val) = Fintype.card (Fin (n.choose 2)) := by
    simp only [Fintype.card_sigma, Fintype.card_fin, Nat.choose_two_right]
    exact (Fin.sum_univ_eq_sum_range id n).trans (Finset.sum_range_id n)
  exact Equiv.ofBijective f ⟨hinj, ((Fintype.bijective_iff_injective_and_card f).mpr ⟨hinj, hcard⟩).2⟩

/-- Number of occupied production counter cells. -/
def labelCount (n m H : ℕ) := H * m * 2 + (((n.choose 2 * H) * H) * H)

private def groupBinary (n H : ℕ) :
    (Σ d : Fin n, Fin H × Fin d.val × Fin H × Fin H) ≃
      (((Σ d : Fin n, Fin d.val) × Fin H) × Fin H) × Fin H where
  toFun | ⟨d,h,b,i,j⟩ => (((⟨d,b⟩,h),i),j)
  invFun | (((⟨d,b⟩,h),i),j) => ⟨d,h,b,i,j⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Dense production indexing, using the triangular prefix for the split and
then row-major coordinates for the parent, left child and right child. -/
noncomputable def labelIndex (n m H : ℕ) :
    GrammarLabel (Fin m × Bool) (Fin H) n ≃ Fin (labelCount n m H) :=
  let term := (Equiv.prodAssoc _ _ _).symm.trans
    ((finProdFinEquiv.prodCongr finTwoEquiv.symm).trans finProdFinEquiv)
  let splitParent := (((splitEquiv n).prodCongr (Equiv.refl (Fin H))).trans finProdFinEquiv)
  let left := (splitParent.prodCongr (Equiv.refl (Fin H))).trans finProdFinEquiv
  let binary := (groupBinary n H).trans ((left.prodCongr (Equiv.refl (Fin H))).trans finProdFinEquiv)
  (term.sumCongr binary).trans finSumFinEquiv

theorem labelIndex_terminal {H : ℕ} (h : Fin H) (j : Fin m) (b : Bool) :
    (labelIndex n m H (.inl (h,j,b))).val = (h.val*m + j.val)*2 + b.toNat := by
  cases b
  · change 0 + 2 * (j.val + m * h.val) = (h.val*m + j.val)*2 + 0
    ring
  · change 1 + 2 * (j.val + m * h.val) = (h.val*m + j.val)*2 + 1
    ring

theorem labelIndex_binary {H : ℕ} (d : Fin n) (b : Fin d.val) (h i j : Fin H) :
    (labelIndex n m H (.inr ⟨d,h,b,i,j⟩)).val =
      H*m*2 + (((d.val.choose 2 + b.val)*H + h.val)*H + i.val)*H + j.val := by
  change H*m*2 + (j.val + H * (i.val + H * (h.val + H * (d.val.choose 2 + b.val)))) = _
  ring

end PrimedStackRAM

end VPVNP
end Computability
end OAI
