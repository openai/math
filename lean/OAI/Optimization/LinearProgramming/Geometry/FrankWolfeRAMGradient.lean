import OAI.Optimization.LinearProgramming.RAM.MatVec
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfe

/-! The fixed RAM call that reads the residual projector and builds the complete gradient array. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM RAM.Dense Matrix
open scoped BigOperators Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- All three arrays are disjoint and located above the direct scalar scratch registers. -/
structure Layout (n : ℕ) where
  matrix : ℕ
  point : ℕ
  gradient : ℕ
  reserved : 23 < matrix
  afterMatrix : matrix+n*n ≤ point
  afterPoint : point+n ≤ gradient

/-- Caller-owned scalar registers are exactly those above scratch and outside both writable arrays. -/
def CallerFrame (L : Layout n) (before after : Memory K) : Prop :=
  ∀ d, 23<d → (d<L.point ∨ L.point+n≤d) → (d<L.gradient ∨ L.gradient+n≤d) →
    after.data d=before.data d

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem CallerFrame.refl (L : Layout n) (m : Memory K) : CallerFrame L m m :=
  fun _ _ _ _ => rfl

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem CallerFrame.trans {L : Layout n} {m s t : Memory K} (h : CallerFrame L m s)
    (g : CallerFrame L s t) : CallerFrame L m t :=
  fun j hj hp hg => (g j hj hp hg).trans (h j hj hp hg)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem CallerFrame.putLow {L : Layout n} {m s : Memory K} (h : CallerFrame L m s)
    {k : Nat} (hk : k≤23) (x : K) : CallerFrame L m (s.putData k x) := by
  intro j hj hp hg
  simpa [show j≠k by omega] using h j hj hp hg

/-- Permanent address registers for the geometric test. -/
structure Addresses (L : Layout n) (i : Fin n) (m : Memory K) : Prop where
  dimension : m.index 23=n
  point : m.index 25=L.point
  gradient : m.index 28=L.gradient
  target : m.index 29=i.val
  matrix : m.index 34=L.matrix

/-- A concrete row-major rational or ordered-field representation, with a snapshot of the point. -/
structure View (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (z : Fin n → K) (m : Memory K) : Prop extends Addresses L i m where
  entry : ∀ r j : Fin n, m.data (L.matrix + r.val*n + j.val)=Q r j
  coord : ∀ j : Fin n, m.data (L.point+j.val)=z j

def Gradient (L : Layout n) (g : Fin n → K) (m : Memory K) : Prop :=
  ∀ j : Fin n, m.data (L.gradient+j.val)=g j

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem View.putData {Q : Matrix (Fin n) (Fin n) K} {z : Fin n → K} {L : Layout n}
    {i : Fin n} {m : Memory K} (v : View L i Q z m) {d : ℕ} (hd : d≤23) (x : K) :
    View L i Q z (m.putData d x) := by
  have hA := L.reserved
  have hz := L.afterMatrix
  refine ⟨⟨v.dimension,v.point,v.gradient,v.target,v.matrix⟩,?_,?_⟩
  · intro r j
    simpa [show L.matrix+r.val*n+j.val ≠ d by omega] using v.entry r j
  · intro j
    simpa [show L.point+j.val ≠ d by omega] using v.coord j

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
theorem Gradient.putData {g : Fin n → K} {L : Layout n} {m : Memory K}
    (h : Gradient L g m) {d : ℕ} (hd : d≤23) (x : K) : Gradient L g (m.putData d x) := by
  have hA := L.reserved
  have hz := L.afterMatrix
  have hg := L.afterPoint
  intro j
  simpa [show L.gradient+j.val ≠ d by omega] using h j

/-- Restore the matrix pointer, output pointer and row count before every matvec. -/
def gradientBlock : Block :=
  .seq (.op (.addrCopy 20 34)) (.seq (.op (.addrCopy 26 28))
    (.seq (.op (.addrCopy 27 23)) matVecBlock))

/-- The natural safety assumptions for the fixed matvec: exact products and prefix sums. -/
structure GradientSafe (P : K → Prop) (Q : Matrix (Fin n) (Fin n) K) (z : Fin n → K) : Prop where
  term : ∀ r j : Fin n, P (Q r j * z j)
  «prefix» : ∀ r : Fin n, ∀ p : ℕ, ∀ hp : p≤n,
    P (∑ j : Fin p, Q r (j.castLE hp) * z (j.castLE hp))

theorem gradientBlock_framed (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (z : Fin n → K) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (v : View L i Q z m) (hp : GradientSafe P Q z) :
    ∃ t, Block.Eval (Memory.AllData P) gradientBlock m (n*(9*n+9)+5) t ∧
      View L i Q z t ∧ Gradient L (Q *ᵥ z) t ∧ (∀ d<20, t.data d=m.data d) ∧ CallerFrame L m t := by
  let m1 := m.putIndex 20 (m.index 34)
  let m2 := m1.putIndex 26 (m.index 28)
  let m3 := m2.putIndex 27 (m.index 23)
  have h20 : m3.index 20=L.matrix := by simp [m3,m2,m1,v.matrix]
  have h25 : m3.index 25=L.point := by simp [m3,m2,m1,v.point]
  have h26 : m3.index 26=L.gradient := by simp [m3,m2,m1,v.gradient]
  have h23 : m3.index 23=n := by simp [m3,m2,m1,v.dimension]
  have h27 : m3.index 27=n := by simp [m3,v.dimension]
  have hA := L.reserved
  have hz := L.afterMatrix
  have hg := L.afterPoint
  have hterm (r j : Fin n) : rowTerm m3 n r j=Q r j*z j := by
    change m3.data _ * m3.data _ = _
    rw [h20,h25]
    exact congrArg₂ (·*·) (v.entry r j) (v.coord j)
  have hsum (r : Fin n) (p : ℕ) (hr : p≤n) :
      rowPrefix m3 n r p = ∑ j : Fin p, Q r (j.castLE hr)*z (j.castLE hr) := by
    rw [rowPrefix, ← Fin.sum_univ_eq_sum_range]
    exact Finset.sum_congr rfl fun j _ => hterm r (j.castLE hr)
  obtain ⟨t,e,h⟩ := matVecBlock_correct P m3 n n hm
    (by rwa [h20]) (by rw [h25];omega) (by rw [h20,h26];omega) (by rwa [h25,h26])
    h23 h27 (fun r hr j hj => (hterm ⟨r,hr⟩ ⟨j,hj⟩) ▸ hp.term _ _)
    (fun r hr j hj => (hsum ⟨r,hr⟩ j hj) ▸ hp.prefix _ j hj)
  have prep := (Block.Eval.op_addrCopy m 20 34 hm hm).seq
    ((show Block.Eval (Memory.AllData P) (.op (.addrCopy 26 28)) m1 1 m2 by
      simpa [m1,m2] using Block.Eval.op_addrCopy m1 26 28 hm hm).seq
     ((show Block.Eval (Memory.AllData P) (.op (.addrCopy 27 23)) m2 1 m3 by
       simpa [m3,m2,m1] using Block.Eval.op_addrCopy m2 27 23 hm hm).seq e))
  have hidx (d : ℕ) (hlo : 22<d) (h24 : d≠24) (h26' : d≠26) (h27' : d≠27) :
      t.index d=m.index d := by
    rw [h.indexFrame d (Or.inr hlo) h24 h26']
    simp [m3,m2,m1,h27',h26',show d≠20 by omega]
  have hd (d : ℕ) (hreg : d<20 ∨ 23<d) (hbelow : d<L.gradient) :
      t.data d=m.data d := h.dataFrame d hreg (Or.inl (h26 ▸ hbelow))
  refine ⟨t,?_,?_,?_,?_,?_⟩
  · rw [show n*(9*n+9)+5=1+(1+(1+(n*(9*n+9)+2))) by omega]
    exact prep
  · refine ⟨⟨(hidx 23 (by decide) (by decide) (by decide) (by decide)).trans v.dimension,
      (hidx 25 (by decide) (by decide) (by decide) (by decide)).trans v.point,
      (hidx 28 (by decide) (by decide) (by decide) (by decide)).trans v.gradient,
      (hidx 29 (by decide) (by decide) (by decide) (by decide)).trans v.target,
      (hidx 34 (by decide) (by decide) (by decide) (by decide)).trans v.matrix⟩,?_,?_⟩
    · intro r j
      have h' := Nat.mul_le_mul_right n r.isLt
      rw [Nat.succ_mul] at h'
      rw [hd _ (Or.inr (by omega)) (by have := j.isLt;omega)]
      exact v.entry r j
    · intro j
      rw [hd _ (Or.inr (by omega)) (by have := j.isLt;omega)]
      exact v.coord j
  · intro j
    rw [← h26, h.cells j j.isLt]
    exact hsum j n le_rfl
  · intro d hd'
    exact hd d (Or.inl hd') (by omega)

  · intro d hd _ outside
    apply h.dataFrame d (Or.inr hd)
    rwa [h26]

theorem gradientBlock_spec (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (z : Fin n → K) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (v : View L i Q z m) (hp : GradientSafe P Q z) :
    ∃ t, Block.Eval (Memory.AllData P) gradientBlock m (n*(9*n+9)+5) t ∧
      View L i Q z t ∧ Gradient L (Q *ᵥ z) t ∧ (∀ d<20, t.data d=m.data d) := by
  obtain ⟨t,e,vw,g,lo,_⟩ := gradientBlock_framed L i Q z m P hm v hp
  exact ⟨t,e,vw,g,lo⟩

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
