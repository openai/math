import OAI.Computability.VPVNP.RankQueryConcreteResources

/-! # Choosing one bit width for both matrix orientations and all Schur roots -/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.ConcreteResources

open PolynomiallyBounded Dispatch RadicalCertificate.MonomialIndex

/-- The largest rectangular prefix in either orientation bounds the
determinant-coefficient scan. The extra unit gives the strict comparison
required when the power of two is attained exactly. -/
def shapeBits (rows cols : ℕ) :=
  let N := max rows cols
  Nat.clog 2 (N+N+(N+N)*N+N+9)

theorem shapeBits_poly {rows cols : ℕ → ℕ} (hr : LB rows) (hc : LB cols) :
    PB (fun n => shapeBits (rows n) (cols n)) := by
  have m := log_max hr hc
  have twice := clog_add m m
  exact clog_add (clog_add (clog_add twice (clog_mul twice m)) m) (log_const 9)

/-- A prefix may be read either as a row prefix or as a column prefix
of the transposed matrix. The same depth bound applies in both cases. -/
theorem shapeBits_rect {rows cols a b : ℕ} (ha : a ≤ max rows cols) (hb : b ≤ max rows cols) :
    a+a+(a+b)*a+b+8 < 2^(shapeBits rows cols) := by
  let N := max rows cols
  have hh : (a+b)*a ≤ (N+N)*N := Nat.mul_le_mul (Nat.add_le_add ha hb) ha
  exact (show a+a+(a+b)*a+b+8 < N+N+(N+N)*N+N+9 by change a ≤ N at ha; change b ≤ N at hb; omega).trans_le
    (Nat.le_pow_clog (by decide) _)

/-- The constant-polynomial determinant specialization uses degree zero
and the same bound for the minor order and the recursion parameter. -/
theorem shapeBits_minor {rows cols r : ℕ} (hr : r ≤ max rows cols) :
    r+r+0+r+8 < 2^(shapeBits rows cols) ∧ r ≤ 2^(shapeBits rows cols) := by
  have h := shapeBits_rect hr hr
  omega

theorem gramWidth_poly {d : ℕ → ℕ} (hd : PB d) : PB (fun i => Cursor.gramWidth (d i)) :=
  ((((const 2).mul hd).add (const 7)).mul (const _)).add (const 3)

/-- These are the three word-fit assumptions shared by the ordinary Schur
root and the weighted Gram descriptor, together with the outer cursor's
width condition. An address kernel can require a larger width. -/
theorem gramWidth_fits {d w : ℕ} (h : Cursor.gramWidth d ≤ w) :
    3 ≤ w ∧ d ≤ w ∧ 2*d+6 ≤ w ∧ (d+1)*widthFactor ≤ w ∧
      (2*d+6+1)*widthFactor ≤ w ∧ (d+1)*Cursor.control.wordFactor ≤ w := by
  let factor := max widthFactor Cursor.control.wordFactor + 1
  have hh : 2*d+7 ≤ (2*d+7)*factor := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
  have hf : widthFactor ≤ factor := (le_max_left ..).trans (Nat.le_succ _)
  have hc : Cursor.control.wordFactor ≤ factor := (le_max_right ..).trans (Nat.le_succ _)
  have full := Nat.mul_le_mul_left (2*d+7) hf
  have descr := Nat.mul_le_mul (show d+1 ≤ 2*d+7 by omega) hf
  have cursor := Nat.mul_le_mul (show d+1 ≤ 2*d+7 by omega) hc
  change (2*d+7)*factor+3 ≤ w at h
  rw [show 2*d+6+1 = 2*d+7 by omega]
  omega

/-- A single address width accommodates the graded-key enumeration as well
as the two orientations of the Schur rank scanner. -/
def sliceAddress {t eqs : ℕ} {F : Type*} (s : QueryData t eqs F) :=
  let rows := eqs*size t s.multiplierDegree+size t s.pointBound
  let cols := size t s.columnDegree
  max (Cursor.gramWidth (shapeBits rows cols))
    (max (scanWidth t s.multiplierDegree) (max (scanWidth t s.columnDegree) (scanWidth t s.pointBound)))

theorem sliceAddress_poly {t eqs : ℕ → ℕ} {K : ℕ → Type*} (s : (n : ℕ) → QueryData (t n) (eqs n) (K n))
    (ht : PB t) (hE : LB eqs) (hQ : LB (fun n => (s n).fieldOrder))
    (hD : LB (fun n => (s n).degreeBound)) (hN : LB (fun n => (s n).pointBound))
    (hq : ∀ n, 2 ≤ (s n).fieldOrder) : PB (fun n => sliceAddress (s n)) := by
  obtain ⟨rows,cols,multiplier,columns,points⟩ := bounded_query_dimensions s ht hE hQ hD hN hq
  exact poly_max (gramWidth_poly (shapeBits_poly rows cols)) (poly_max multiplier (poly_max columns points))

theorem sliceAddress_covers {t eqs : ℕ} {F : Type*} (s : QueryData t eqs F) :
    let rows := eqs*size t s.multiplierDegree+size t s.pointBound
    let cols := size t s.columnDegree
    Cursor.gramWidth (shapeBits rows cols) ≤ sliceAddress s ∧
    scanWidth t s.multiplierDegree ≤ sliceAddress s ∧ scanWidth t s.columnDegree ≤ sliceAddress s ∧
    scanWidth t s.pointBound ≤ sliceAddress s := by
  dsimp only [sliceAddress]
  omega

end RankQuery.Stack.Coordinate.ConcreteResources

end VPVNP
end Computability
end OAI
