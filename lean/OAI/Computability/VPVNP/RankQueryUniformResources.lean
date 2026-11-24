import OAI.Computability.VPVNP.RankQueryShapeResources
import OAI.Computability.VPVNP.RankQueryNestedResources
import OAI.Computability.VPVNP.MacaulayReaderWidth

/-!
# Uniform coordinate costs before the field and slice are chosen

Rows, columns, rank, extension degree and limb width can depend on the prime
and affine slice. At each input length these five natural numbers lie in a
finite box fixed by the reader plan. Maximizing the clock and stack height
separately preserves their respective bounds. This also handles the ordinary
determinant's clock without a monotonicity assumption about its recursion.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.ConcreteResources

open PolynomiallyBounded Cost RadicalCertificate.MonomialIndex

/-- Separate maxima of the clock and peak for all possible parameters at
one length. Only the estimates use the maxima. The machine runs the query
at the supplied parameters. -/
def maximum {I : Type*} [Fintype I] (cost : I → Budget) : Budget :=
  ⟨Finset.univ.sup (fun a => (cost a).time), Finset.univ.sup (fun a => (cost a).space)⟩

theorem le_maximum {I : Type*} [Fintype I] (cost : I → Budget) (a : I) :
    (cost a).time ≤ (maximum cost).time ∧ (cost a).space ≤ (maximum cost).space :=
  ⟨Finset.le_sup (f := fun x => (cost x).time) (Finset.mem_univ a),
    Finset.le_sup (f := fun x => (cost x).space) (Finset.mem_univ a)⟩

theorem maximum_feasible {I : ℕ → Type*} [∀ n, Fintype (I n)] [∀ n, Nonempty (I n)]
    (cost : (n : ℕ) → I n → Budget) (h : ∀ a : (n : ℕ) → I n, Feasible (fun n => cost n (a n))) :
    Feasible (fun n => maximum (cost n)) := by
  classical
  have pick (f : (n : ℕ) → I n → ℕ) : ∃ a : (n : ℕ) → I n, ∀ n, Finset.univ.sup (f n) = f n (a n) := by
    have chooseAt (n : ℕ) := Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty (f n)
    choose a _ eq using chooseAt
    exact ⟨a,eq⟩
  obtain ⟨time,ht⟩ := pick fun n a => (cost n a).time
  obtain ⟨space,hs⟩ := pick fun n a => (cost n a).space
  exact ⟨(h time).time.of_le (fun n => (congrArg (Nat.clog 2) (ht n)).le),
    (h space).space.of_le (fun n => (hs n).le)⟩

/-- The natural parameters still undetermined after fixing the input
length. The first three coordinates are the two dimensions and minor order. -/
abbrev Shapes (limit degree limb : ℕ) :=
  (Fin 3 → Fin (limit+1)) × Fin (degree+1) × Fin (limb+1)

/-- Time and stack-height budget for a mounted Cramer coordinate query, including minor
selection, preparation, and the caller's peak stack height. -/
def mountedBudget (H K : Type) [Fintype H] [Fintype K] (rows cols r d w v e B A S E : ℕ)
    (prep : Budget) : Budget :=
  let minor := minorBudget K rows cols d w v e B A S E
  let V := SelectedMinor.space K d w v e A S
  let pair := pairBudget H r w v e V minor prep
  ⟨pair.time, max pair.space (Reader.callerPeak w e v)⟩

/-- The cap includes every ready denominator and numerator bank, as in
`SelectedMinor.den_ready_length` and `SelectedMinor.num_ready_length`. -/
theorem mounted_feasible_of_shape (H K : Type) [Fintype H] [Fintype K]
    {rows cols r d w v e B A S E : ℕ → ℕ} {prep : ℕ → Budget}
    (hr : LB rows) (hc : LB cols) (ho : LB r) (hd : PB d) (hw : PB w) (hv : PB v) (he : PB e)
    (hB : LB B) (hA : PB A) (hS : PB S) (hE : LB E) (hp : Feasible prep) :
    Feasible (fun n => mountedBudget H K (rows n) (cols n) (r n) (d n) (w n) (v n) (e n)
      (B n) (A n) (S n) (E n) (prep n)) := by
  have hm := minor_feasible K hr hc hd hw hv he hA hS hB hE
  have hs := (selected_feasible K hr hc hd hw hv he hA hS hB hE).space
  exact mounted_feasible (pair_feasible H ho hw hv he hs hm hp) hw hv he

/-- Separate worst-case time and space budgets over the bounded matrix dimensions, minor order,
extension degree, and limb width. -/
def uniformBudget (H K : Type) [Fintype H] [Fintype K] (limit d w degree limb B A S E : ℕ) (prep : Budget) :=
  maximum (fun x : Shapes limit degree limb => mountedBudget H K (x.1 0) (x.1 1) (x.1 2)
    d w x.2.2 x.2.1 B A S E prep)

theorem uniformBudget_covers (H K : Type) [Fintype H] [Fintype K]
    {rows cols r e v limit degree limb : ℕ} (hr : rows ≤ limit) (hc : cols ≤ limit) (ho : r ≤ limit)
    (he : e ≤ degree) (hv : v ≤ limb) (d w B A S E : ℕ) (prep : Budget) :
    let cost := mountedBudget H K rows cols r d w v e B A S E prep
    let cap := uniformBudget H K limit d w degree limb B A S E prep
    cost.time ≤ cap.time ∧ cost.space ≤ cap.space := by
  let shape : Shapes limit degree limb :=
    ⟨![⟨rows,Nat.lt_succ_of_le hr⟩,⟨cols,Nat.lt_succ_of_le hc⟩,⟨r,Nat.lt_succ_of_le ho⟩],
      ⟨e,Nat.lt_succ_of_le he⟩,⟨v,Nat.lt_succ_of_le hv⟩⟩
  exact le_maximum (fun x : Shapes limit degree limb => mountedBudget H K (x.1 0) (x.1 1) (x.1 2)
    d w x.2.2 x.2.1 B A S E prep) shape

theorem uniform_feasible (H K : Type) [Fintype H] [Fintype K]
    {limit d w degree limb B A S E : ℕ → ℕ} {prep : ℕ → Budget}
    (hl : LB limit) (hd : PB d) (hw : PB w) (he : PB degree) (hv : PB limb)
    (hB : LB B) (hA : PB A) (hS : PB S) (hE : LB E) (hp : Feasible prep) :
    Feasible (fun n => uniformBudget H K (limit n) (d n) (w n) (degree n) (limb n)
      (B n) (A n) (S n) (E n) (prep n)) := by
  apply maximum_feasible
  intro shape
  have dim (j : Fin 3) : LB (fun n => (shape n).1 j) :=
    hl.of_le fun n => Nat.clog_mono_right _ (Nat.lt_succ_iff.mp ((shape n).1 j).isLt)
  exact mounted_feasible_of_shape H K (dim 0) (dim 1) (dim 2) hd hw
    (hv.of_le fun n => Nat.lt_succ_iff.mp (shape n).2.2.isLt)
    (he.of_le fun n => Nat.lt_succ_iff.mp (shape n).2.1.isLt) hB hA hS hE hp

/-- The full rectangular and graded address kernel both fit one
prime-independent word width. -/
def planDepth (P : ReaderPlan) := shapeBits P.addressLimit P.addressLimit

/-- Word width sufficient for both the Gram rank cursor and the plan's matrix-entry reader. -/
def planWidth (P : ReaderPlan) := max (Cursor.gramWidth (planDepth P)) P.wordWidth

theorem planSizes {P : ℕ → ReaderPlan} (hw : PB (fun n => (P n).wordWidth)) :
    LB (fun n => (P n).addressLimit) ∧ PB (fun n => planDepth (P n)) ∧ PB (fun n => planWidth (P n)) := by
  have lim : LB (fun n => (P n).addressLimit) := hw.of_le fun n => ((P n).dispatchWidth).2.1
  have depth := shapeBits_poly lim lim
  exact ⟨lim,depth,poly_max (gramWidth_poly depth) hw⟩

theorem planWidth_covers (P : ReaderPlan) :
    Cursor.gramWidth (planDepth P) ≤ planWidth P ∧ P.wordWidth ≤ planWidth P :=
  ⟨le_max_left ..,le_max_right ..⟩

theorem plan_dimensions {P : ReaderPlan} {K : Type*} {s : QueryData P.arity (P.equations+P.pins) K}
    (h : P.Covers s) :
    (P.equations+P.pins)*size P.arity s.multiplierDegree + size P.arity s.pointBound ≤ P.addressLimit ∧
    size P.arity s.columnDegree ≤ P.addressLimit := by
  have dense {D L : ℕ} (hle : D ≤ L) : size P.arity D ≤ rawSize P.arity L := by
    rw [size_eq_card]
    exact (RadicalCertificate.card_boundedMonomial_le ..).trans ((Nat.le_mul_of_pos_left _ (Nat.succ_pos _)).trans (ReaderPlan.raw_mono _ hle))
  have row := Nat.add_le_add (Nat.mul_le_mul_left (P.equations+P.pins) (dense h.degrees.2.1)) (dense h.points_le)
  have col := dense h.degrees.2.2
  unfold ReaderPlan.addressLimit
  omega

/-- The matrix-order and both degree-scan inequalities required by the
two orientations and by the ordinary determinant, at the common plan width. -/
theorem plan_query_shapes {P : ReaderPlan} {F : Type} [Field F] [DecidableEq F]
    {s : QueryData P.arity (P.equations+P.pins) F} (h : P.Covers s) :
    let n := (P.equations+P.pins)*size P.arity s.multiplierDegree+size P.arity s.pointBound
    let m := size P.arity s.columnDegree
    let r := rankQuery (appendRows s.equations s.monomials)
    let d := planDepth P
    n ≤ P.addressLimit ∧ m ≤ P.addressLimit ∧ r ≤ P.addressLimit ∧
      n+n+(n+m)*n+m+8 < 2^d ∧ m+m+(m+n)*m+n+8 < 2^d ∧ r+r+0+r+8 < 2^d ∧ r ≤ 2^d := by
  intro n m r d
  obtain ⟨hr,hc⟩ := plan_dimensions h
  have rle : r ≤ n := by
    dsimp only [r]
    rw [rankQuery_eq]
    simpa only [Fintype.card_fin] using (appendRows s.equations s.monomials).rank_le_card_height
  have inBox {z : ℕ} (hz : z ≤ P.addressLimit) : z ≤ max P.addressLimit P.addressLimit := hz.trans (le_max_left ..)
  have horder := rle.trans hr
  exact ⟨hr,hc,horder,shapeBits_rect (inBox hr) (inBox hc),shapeBits_rect (inBox hc) (inBox hr),
    shapeBits_minor (inBox horder)⟩

end RankQuery.Stack.Coordinate.ConcreteResources

end VPVNP
end Computability
end OAI
