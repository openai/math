import OAI.LinearAlgebra.MatrixExponent.FunctionNetwork

/-!
# Trivalent realization of arbitrary tables

Give the table one enable bit. Splitting on the next address bit enables
exactly one of two subtables, while a disabled subtable contributes the
factor one. Copying the remaining bits costs their width at each split.
-/

namespace OAI.LinearAlgebra.MatrixExponent
namespace Net

variable {F : Type} [Field F]

/-- A pair of identical bundles with no inputs. -/
theorem cup (F : Type) [Field F] (a : Wire) :
    Net F .unit (.pair a a) (fun _ y => if y.1 = y.2 then 1 else 0) (wd a) := by
  induction a with
  | bit => exact .table _ _ _ (by decide)
  | unit => exact (Net.empty (F := F)).post (.unit _)
  | pair a b ha hb =>
    simpa only [wd, Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul] using
      ((ha.par hb).pre (.unit' _)).post (.middle a b a b)

/-- Turn some inputs into outputs, paying for a pairwise equality test
on the corresponding bits. -/
theorem curry {a b : Wire} {k : Val a → Val b → F} {m : ℕ}
    (h : Net F (.pair a b) .unit (fun x _ => k x.1 x.2) m) :
    Net F a b k (m + wd b) := by
  have g := ((h.par (cup F b)).pre (.unit' _)).post ((Rewire.unit' _).comp (.swap _ _))
  simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    using g.trace

/-- The additive width term pays for copying the unprocessed address bits. -/
private def Enabled (F : Type) [Field F] (a : Wire) : Prop :=
  ∀ k : Val a → F, ∃ m, Net F (.pair .bit a) .unit (fun x _ => if x.1 then k x.2 else 1) m ∧
    m + wd a + 5 ≤ 6 * 2 ^ wd a

private theorem enabled_bit {a : Wire} (h : Enabled F a) : Enabled F (.pair .bit a) := by
  intro k
  obtain ⟨m, lo, hm⟩ := h (fun x => k (false, x))
  obtain ⟨n, hi, hn⟩ := h (fun x => k (true, x))
  have zero := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && !x.2) (by decide)
  have one := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && x.2) (by decide)
  obtain ⟨v, hv, split⟩ :=
    (((zero.pair one).par (DNet.dup F a)).pre (.assoc' .bit .bit a)).post (.middle .bit .bit a a)
  refine ⟨v + (m + n), ?_, ?_⟩
  · have H := (split.comp (lo.par hi)).post (.unit' _)
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] at H
    convert H using 1
    funext ⟨b, c, x⟩ y
    cases b <;> cases c <;> simp
  · simp only [wd, pow_add, pow_one] at hv ⊢
    omega

private theorem enabled_extend (a : Wire) {b : Wire} (h : Enabled F b) :
    Enabled F (.pair a b) := by
  induction a generalizing b with
  | bit => exact enabled_bit h
  | unit =>
    intro k
    obtain ⟨m, H, hm⟩ := h (fun x => k ((), x))
    exact ⟨m, H.pre ((Rewire.id _).par ((Rewire.swap _ _).comp (.unit _))),
      by simpa only [wd, Nat.zero_add] using hm⟩
  | pair a c ha hc =>
    intro k
    obtain ⟨m, H, hm⟩ := ha (hc h) (fun x => k ((x.1, x.2.1), x.2.2))
    exact ⟨m, H.pre ((Rewire.id _).par (.assoc _ _ _)),
      by simpa only [wd, Nat.add_assoc] using hm⟩

private theorem dense_weight (a : Wire) (k : Val a → F) :
    ∃ m, Net F a .unit (fun x _ => k x) m ∧ m ≤ 6 * 2 ^ wd a := by
  have base : Enabled F .unit := fun _ => ⟨1, .table _ _ _ (by decide), by decide⟩
  obtain ⟨m, H, hm⟩ := enabled_extend a base (fun x => k x.1)
  have pin := DNet.table F .unit .bit (fun _ => true) (by decide)
  obtain ⟨v, hv, G⟩ := (pin.par (DNet.id F a)).pre ((Rewire.unit' a).comp (.swap _ _))
  refine ⟨v + m, ?_, by simp only [wd, Nat.add_zero] at hm; omega⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true] using
    G.comp (H.pre ((Rewire.id _).par (.unit' _)))

/-- Any table on `r` exterior bits needs at most `8 * 2 ^ r` trivalent vertices. -/
theorem dense (a b : Wire) (k : Val a → Val b → F) :
    ∃ m, Net F a b k m ∧ m ≤ 8 * 2 ^ (wd a + wd b) := by
  obtain ⟨m, H, hm⟩ := dense_weight (.pair a b) (fun x => k x.1 x.2)
  refine ⟨m + wd b, H.curry, ?_⟩
  have := Nat.lt_two_pow_self (n := wd a + wd b)
  simp only [wd] at hm
  omega

end Net
end OAI.LinearAlgebra.MatrixExponent
