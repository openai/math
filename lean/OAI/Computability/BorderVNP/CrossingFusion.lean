import OAI.Computability.VPVNP.ShiftedCrossing

/-!
# Successively crossing a state wire with fresh equality wires

In §4.2 of *An explicit VNP family requires superpolynomial border circuit
size over every field*, each crossing keeps its orientation and its mode on
the cut. Only the occupation state changes. The two side tables below are
obtained by summing out the old state at each step.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing

open VPVNP.Crossing

/-- A side receives exactly one terminal from each pair, selected by the
orientation of that crossing. Reversing the two inputs gives the other side. -/
def sideInputs {d q : ℕ} (bits : Fin d → Bool) (x y : Fin d → Fin q) :
    Fin d → Fin q := fun i => if bits i then x i else y i

private def localLeft {q s M t : ℕ} (T : IntegralCrossing q s (M*t) (M*t))
    (b : Bool) (a : Fin q) (j : Fin M) (k : Fin t) (i : Fin s) : ℤ :=
  if b then T.leftPlus (finProdFinEquiv (j,k)) a i
  else T.rightMinus (finProdFinEquiv (j,k)) a i

private def localRight {q s M t : ℕ} (T : IntegralCrossing q s (M*t) (M*t))
    (b : Bool) (a : Fin q) (j : Fin M) (k : Fin t) (i : Fin s) : ℤ :=
  if b then T.rightPlus (finProdFinEquiv (j,k)) a i
  else T.leftMinus (finProdFinEquiv (j,k)) a i

private theorem local_identity {q s M t : ℕ} (T : IntegralCrossing q s (M*t) (M*t))
    (x y : Fin q) (i h : Fin s) :
    ∑ b : Bool, ∑ j, ∑ k,
      localLeft T b (if b then x else y) j k i *
      localRight T b (if b then y else x) j k h =
      (if x = y then 1 else 0) * (if i = h then 1 else 0) := by
  have sums (f : Fin (M*t) → ℤ) :
      (∑ j, ∑ k, f (finProdFinEquiv (j,k))) = ∑ u, f u := by
    rw [← Fintype.sum_prod_type']
    exact finProdFinEquiv.sum_comp f
  rw [Fintype.sum_bool]
  simp only [localLeft, localRight, Bool.false_eq_true, ↓reduceIte]
  rw [show (∑ j, ∑ k, T.rightMinus (finProdFinEquiv (j,k)) y i *
    T.leftMinus (finProdFinEquiv (j,k)) x h) =
    ∑ k, T.leftMinus k x h * T.rightMinus k y i by
      simpa only [mul_comm] using sums (fun k => T.rightMinus k y i * T.leftMinus k x h)]
  exact congrArg (fun z => z + _) (sums (fun k => T.leftPlus k x i * T.rightPlus k y h))
    |>.trans (T.identity x y i h)

private theorem weight_contraction {q s M t : ℕ}
    (T : IntegralCrossing q s (M*t) (M*t)) (x y : Fin q) (a e : Fin s → ℤ) :
    ∑ b : Bool, ∑ j, ∑ k,
      (∑ i, a i * localLeft T b (if b then x else y) j k i) *
      (∑ h, e h * localRight T b (if b then y else x) j k h) =
      (if x = y then 1 else 0) * ∑ i, a i * e i := by
  let L b j k i := localLeft T b (if b then x else y) j k i
  let R b j k h := localRight T b (if b then y else x) j k h
  have commute {I J U V W : Type} [Fintype I] [Fintype J] [Fintype U] [Fintype V] [Fintype W]
      (f : I → J → U → V → W → ℤ) :
      (∑ i, ∑ j, ∑ u, ∑ v, ∑ w, f i j u v w) =
      ∑ v, ∑ w, ∑ i, ∑ j, ∑ u, f i j u v w := by
    simpa only [Fintype.sum_prod_type] using
      (Finset.sum_comm (s := Finset.univ) (t := Finset.univ)
        (f := fun (p : I × J × U) (z : V × W) => f p.1 p.2.1 p.2.2 z.1 z.2))
  change (∑ b, ∑ j, ∑ k, (∑ i, a i * L b j k i) * ∑ h, e h * R b j k h) = _
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  rw [commute]
  have aux b j k i h : a i * L b j k i * (e h * R b j k h) =
      (a i * e h) * (L b j k i * R b j k h) := by ring
  simp_rw [aux, ← Finset.mul_sum]
  dsimp only [L,R]
  simp_rw [local_identity]
  by_cases h : x = y <;> simp [h, mul_ite]

/-- Left or right side of an iterated crossing, with all intermediate states
summed internally. The cut exposes one mode per step and one final state. -/
def fusedSide {q M : ℕ} {s : ℕ → ℕ}
    (steps : ∀ d, IntegralCrossing q (s d) (M * s (d+1)) (M * s (d+1)))
    (left : Bool) : (d : ℕ) → (Fin d → Bool) → (Fin d → Fin q) →
      (Fin d → Fin M) → Fin (s d) → ℤ
  | 0, _, _, _, _ => 1
  | d+1, b, x, j, k => ∑ i,
      fusedSide steps left d (Fin.tail b) (Fin.tail x) (Fin.tail j) i *
      (if left then localLeft else localRight) (steps d) (b 0) (x 0) (j 0) k i

private theorem sum_cons {A : Type} [Fintype A] {d : ℕ} (f : (Fin (d+1) → A) → ℤ) :
    (∑ w, f w) = ∑ w : Fin d → A, ∑ a, f (Fin.cons a w) := by
  rw [← (Fin.consEquiv (fun _ : Fin (d+1) => A)).sum_comp f, Fintype.sum_prod_type_right]
  rfl

/-- With the vacuum as initial state, the two side tables give an exact
integer decomposition of the product of all equality tensors. There are
`2^d` choices of sides and `M^d * s d` choices of the cut index. -/
theorem fusedSides_identity {q M : ℕ} {s : ℕ → ℕ} (vacuum : s 0 = 1)
    (steps : ∀ d, IntegralCrossing q (s d) (M * s (d+1)) (M * s (d+1)))
    (d : ℕ) (x y : Fin d → Fin q) :
    (∑ b, ∑ j, ∑ k, fusedSide steps true d b (sideInputs b x y) j k *
      fusedSide steps false d b (sideInputs b y x) j k) =
      ∏ i, if x i = y i then 1 else 0 := by
  induction d with
  | zero => simp [fusedSide, vacuum]
  | succ d ih =>
    rw [sum_cons, Fin.prod_univ_succ]
    simp_rw [sum_cons (A := Fin M)]
    have commute (f : Bool → (Fin d → Fin M) → ℤ) :
        (∑ b, ∑ j, f b j) = ∑ j, ∑ b, f b j := Finset.sum_comm
    simp_rw [commute]
    simp only [fusedSide, ↓reduceIte, Bool.false_eq_true, sideInputs,
      Fin.cons_zero, Fin.tail_def, Fin.cons_succ]
    simp_rw [weight_contraction]
    rw [← ih (fun i => x i.succ) (fun i => y i.succ), Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.mul_sum]
    rfl

/-- The local factor at a single vertex on one side. In the reverse cut the
old left state is paired with the new right terminal. -/
def sideFactor {q s M t : ℕ} (T : IntegralCrossing q s (M*t) (M*t))
    (left b : Bool) (x : Fin q) (j : Fin M) (i : Fin s) (k : Fin t) : ℤ :=
  (if left then localLeft else localRight) T b x j k i

/-- Open the local contraction as a single guess of the intermediate states,
followed by a product of independent single-crossing factors. States are in
order of increasing energy budget. The corresponding terminal indices occur
in reverse order because a new pair is added at the head. -/
theorem fusedSide_paths {q M : ℕ} {s : ℕ → ℕ}
    (steps : ∀ t, IntegralCrossing q (s t) (M * s (t+1)) (M * s (t+1)))
    (left : Bool) (d : ℕ) (b : Fin d → Bool) (x : Fin d → Fin q) (j : Fin d → Fin M)
    (k : Fin (s d)) :
    fusedSide steps left d b x j k =
      ∑ z : (i : Fin d) → Fin (s i.val), ∏ i : Fin d,
        sideFactor (steps i.val) left (b i.rev) (x i.rev) (j i.rev)
          (z i) (Fin.snoc (α := fun i : Fin (d+1) => Fin (s i.val)) z k i.succ) := by
  induction d with
  | zero => simp [fusedSide]
  | succ d ih =>
    rw [fusedSide, ← (Fin.snocEquiv (fun i : Fin (d+1) => Fin (s i.val))).sum_comp,
      Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro old _
    rw [ih, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro z _
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.snocEquiv, Equiv.coe_fn_mk, Fin.snoc_castSucc, Fin.snoc_last,
      Fin.rev_last, Fin.succ_last, Fin.rev_castSucc, Fin.tail_def]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    exact congrArg (sideFactor (steps i.val) left (b i.rev.succ) (x i.rev.succ)
      (j i.rev.succ) (z i)) (Fin.snoc_castSucc (α := fun t : Fin (d+2) => Fin (s t.val)) k
        (fun t => Fin.snoc (α := fun t : Fin (d+1) => Fin (s t.val)) z old t) i.succ).symm

end Crossing

end BorderVNP
end Computability
end OAI
