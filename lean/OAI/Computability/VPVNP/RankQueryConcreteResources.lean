import OAI.Computability.VPVNP.RankCoordinateCost
import OAI.Computability.VPVNP.RankQueryPlainBounds
import OAI.Computability.VPVNP.RankQueryGramExecution

/-!
# Uniform bounds on the concrete determinant and rank programs

The parameters below vary with the paper's input length. A matrix dimension
and an entry-query clock can be singly exponential in this length. Widths,
field-extension degree, and entry-query peak space are polynomial. The
proofs apply to the clock and storage formulas of the actual finite routines.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.ConcreteResources

open Cost Dispatch

/-- Polynomial boundedness of a resource quantity as a function of the input length. -/
abbrev PB := PolynomiallyBounded
/-- Polynomial boundedness of the ceiling binary logarithm of a resource quantity as a function
of the input length. -/
abbrev LB := LogBound

variable {f g : ℕ → ℕ}

theorem poly_max (hf : PB f) (hg : PB g) : PB (fun i => max (f i) (g i)) :=
  (hf.add hg).of_le fun _ => by omega

theorem log_max (hf : LB f) (hg : LB g) : LB (fun i => max (f i) (g i)) :=
  (PolynomiallyBounded.clog_add hf hg).of_le fun i => Nat.clog_mono_right _ (show max (f i) (g i) ≤ f i + g i by omega)

/-- A constant resource quantity has a polynomially bounded ceiling binary logarithm. -/
theorem log_const (k : ℕ) : LB (fun _ => k) := (PolynomiallyBounded.const k).clog

open PolynomiallyBounded

variable {w v e d r A S B : ℕ → ℕ}

theorem allowance_poly (hw : PB w) (hv : PB v) (he : PB e) :
    PB (fun i => DescribeAdapter.allowance (max (w i) (max (v i) (e i)))) := by
  exact (const _).mul (((poly_max hw (poly_max hv he)).add (const 1)).pow 4)

theorem localBudget_poly (hw : PB w) (he : PB e) (hv : PB v) :
    PB (fun i => Engine.Assembly.localBudget (w i) (e i) (v i)) := by
  have op (a : Operation) : PB (fun i => a.clock (w i)) := by
    exact (const _).mul ((const 100).mul ((hw.add (const 1)).pow 2))
  have hmac : PB (fun i => Engine.MultiplyAdd.callCap (e i) (v i)) := by
    apply PolynomiallyBounded.of_le (g := fun i => 3000*(e i+1)^2*(v i+1)^2+2*(e i*v i+1))
    · exact (((const 3000).mul ((he.add (const 1)).pow 2)).mul ((hv.add (const 1)).pow 2)).add ((const 2).mul ((he.mul hv).add (const 1)))
    · intro i
      exact Nat.add_le_add_right (SliceArithmetic.MultiplyAccumulate.callCap_le ..) _
  have hleft := op .left
  have hright := op .right
  exact ((hleft.add hright).add hmac).add ((const 100).mul ((hw.add (he.mul hv)).add (const 1)))

theorem gram_descriptor_log (hw : PB w) (hv : PB v) (he : PB e) (hB : LB B) :
    LB (fun i => DescribeAdapter.clock (w i) (v i) (e i) (B i)) := by
  have hlocal := allowance_poly hw hv he
  refine PolynomiallyBounded.of_le
    (g := fun i => Nat.clog 2 (2*B i + DescribeAdapter.allowance (max (w i) (max (v i) (e i))))) ?_ ?_
  · exact clog_add (clog_mul (log_const 2) hB) hlocal.clog
  · intro i
    exact Nat.clog_mono_right _ (DescribeAdapter.clock_space_le (w i) (v i) (e i) _ (B i) 0 0
      (le_max_left ..) ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))).1

theorem gram_descriptor_poly (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hS : PB S) :
    PB (fun i => DescribeAdapter.space (w i) (v i) (e i) (A i) (S i)) := by
  have hlocal := allowance_poly hw hv he
  apply PolynomiallyBounded.of_le
    (g := fun i => max (A i) (S i) + DescribeAdapter.allowance (max (w i) (max (v i) (e i))))
  · exact (poly_max hA hS).add hlocal
  · intro i
    exact (DescribeAdapter.clock_space_le (w i) (v i) (e i) _ 0 (A i) (S i)
      (le_max_left ..) ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))).2

theorem plain_descriptor_log (hw : PB w) (hv : PB v) (he : PB e) (hB : LB B) :
    LB (fun i => PlainEngine.descriptorClock (w i) (v i) (e i) (B i)) := by
  have hlocal := allowance_poly hw hv he
  refine PolynomiallyBounded.of_le
    (g := fun i => Nat.clog 2 (B i + DescribeAdapter.allowance (max (w i) (max (v i) (e i))))) ?_ ?_
  · exact clog_add hB hlocal.clog
  · intro i
    exact Nat.clog_mono_right _ (PlainEngine.descriptorClock_le _ _ _ _ _
      (le_max_left ..) ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..)))

theorem plain_descriptor_poly (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hS : PB S) :
    PB (fun i => DescribeAdapter.peakWith (w i) (v i) (e i) (A i) (fun a => PlainScalar.space (w i) (v i) (e i) a (S i))) := by
  have hlocal := allowance_poly hw hv he
  apply PolynomiallyBounded.of_le (g := fun i => max (A i) (S i) + DescribeAdapter.allowance (max (w i) (max (v i) (e i))))
  · exact (poly_max hA hS).add hlocal
  · intro i
    exact PlainEngine.descriptorSpace_le _ _ _ _ _ _
      (le_max_left ..) ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))

theorem step_poly {T : ℕ → ℕ} (hw : PB w) (hv : PB v) (he : PB e) (hT : PB T) :
    PB (fun i => Engine.stepBudget (T i) (w i) (v i) (e i)) := by
  have live := poly_max (const 1) (poly_max hw (he.mul hv))
  exact (const 4).mul ((hT.add ((const 10).mul (((const 3).mul live).add (const 2)))).add (const 5))

theorem step_log {T : ℕ → ℕ} (hw : PB w) (hv : PB v) (he : PB e) (hT : LB T) :
    LB (fun i => Engine.boundedStepTime (T i) (Engine.Assembly.localBudget (w i) (e i) (v i)) (w i) (v i) (e i)) :=
  log_max (clog_add hT (log_const 1)) (step_poly hw hv he (localBudget_poly hw he hv)).clog

theorem entryCap_poly (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hd : PB d) :
    PB (fun i => GramEngine.entryCap (w i) (v i) (e i) (A i) (d i)) := by
  have live := poly_max (const 1) (poly_max hw (he.mul hv))
  have history := hd.mul (((const 2).mul live).add (const 1))
  exact poly_max ((((hw.add hv).add he).add (he.mul hv)).add hA) (poly_max live history)

theorem schurSpace_poly (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hS : PB S) (hd : PB d) :
    PB (fun i => Engine.boundedSpace (S i) (A i) (d i) (Engine.Assembly.localBudget (w i) (e i) (v i))
      (w i) (v i) (e i)) := by
  have live := poly_max (const 1) (poly_max hw (he.mul hv))
  have history := hd.mul (((const 2).mul live).add (const 1))
  exact poly_max (hS.add (const 1))
    ((poly_max hA (poly_max live history)).add (step_poly hw hv he (localBudget_poly hw he hv)))

/-- The full ordinary determinant clock and peak, uniformly for an
arbitrary family of singly exponential square minors. -/
theorem plain_feasible (hr : LB r) (hw : PB w) (hv : PB v) (he : PB e)
    (hA : PB A) (hS : PB S) (hB : LB B) :
    Feasible (fun i => ⟨PlainEngine.queryTime (r i) (w i) (v i) (e i) (B i),
      PlainEngine.querySpace (r i) (w i) (v i) (e i) (A i) (S i)⟩) := by
  let depth := fun i => Nat.clog 2 (r i)+4+Nat.clog 2 (r i)
  have hdepth : PB depth := (hr.add (.const 4)).add hr
  have hrec : LB (fun i => SchurKey.clock (r i) (r i) 0) := by
    refine PolynomiallyBounded.of_le (g := fun i =>
      (2*Nat.clog 2 (r i)+8)*(2*Nat.clog 2 (r i)+5)) ?_ ?_
    · exact (((const 2).mul hr).add (const 8)).mul (((const 2).mul hr).add (const 5))
    · intro i
      have h := Nat.le_pow_clog (by decide : 1 < 2) (r i)
      exact Nat.clog_le_of_le_pow (SchurKey.clock_le_exp _ _ 0 _ h h (Nat.zero_le _))
  have hstep := step_log hw hv he (plain_descriptor_log hw hv he hB)
  let initial := fun i => GramEngine.entryCap (w i) (v i) (e i) (A i) (depth i)
  have hi : PB initial := entryCap_poly hw hv he hA hdepth
  have hpeak := plain_descriptor_poly hw hv he hi hS
  constructor
  · change LB (fun i => SchurKey.clock (r i) (r i) 0 * Engine.boundedStepTime
      (PlainEngine.descriptorClock (w i) (v i) (e i) (B i))
      (Engine.Assembly.localBudget (w i) (e i) (v i)) (w i) (v i) (e i) + 1)
    exact clog_add (clog_mul hrec hstep) (log_const 1)
  · exact schurSpace_poly hw hv he ((((hw.add hv).add he).add (he.mul hv)).add hA) (poly_max hi hpeak) hdepth

/-- The concrete rectangular rank scanner, including root initialization,
scalar zero tests, and every cursor update. The shared bit bound `d` may
vary polynomially with the external length. -/
theorem rank_feasible (hd : PB d) (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hS : PB S) (hB : LB B) :
    Feasible (fun i => ⟨Cursor.gramTime (d i) (w i) (v i) (e i) (B i),
      Cursor.gramSpace (d i) (w i) (v i) (e i) (A i) (S i)⟩) := by
  have hstep := step_log hw hv he (gram_descriptor_log hw hv he hB)
  have startup : PB (fun i => Cursor.startupClock (w i)) := by
    have sq := (hw.add (const 1)).pow 2
    exact ((((const 5).mul hw).add (const 2)).add ((const 12).mul sq)).add ((const 5).mul ((const 100).mul sq))
  have load : PB (fun i => Cursor.loadClock (w i)) :=
    ((const 6).mul (((const 5).mul hw).add (const 2))).add (const 1)
  have check : PB (fun i => Cursor.checkClock (w i) (v i) (e i)) := by
    simp only [Cursor.checkClock,Cursor.Registers.clock_eq]
    exact (((const 5).mul (he.mul hv)).add (const 4)).add (((((const 7300).mul ((hw.add (const 1)).pow 2)).add ((const 20).mul hw)).add (const 13)))
  have depth : PB (fun i => 2*d i+4) := ((PolynomiallyBounded.const 2).mul hd).add (.const 4)
  have initial := entryCap_poly hw hv he hA depth
  have hds := poly_max initial (gram_descriptor_poly hw hv he initial hS)
  have aux := (((hw.add hv).add he).add (he.mul hv)).add hA
  have schur := schurSpace_poly hw hv he aux hds depth
  constructor
  · change LB (fun i => Cursor.startupClock (w i) + ((2^(d i)+1)*(2^(d i)+1)*
      (Cursor.loadClock (w i) + (2^((2*d i+8)*(2*d i+5))*Engine.boundedStepTime
        (DescribeAdapter.clock (w i) (v i) (e i) (B i)) (Engine.Assembly.localBudget (w i) (e i) (v i))
        (w i) (v i) (e i) + 1) + Cursor.checkClock (w i) (v i) (e i) + 1)+2))
    have dim := clog_add (clog_pow (log_const 2) hd) (log_const 1)
    have count := clog_pow (log_const 2) ((((const 2).mul hd).add (const 8)).mul (((const 2).mul hd).add (const 5)))
    have query := clog_add load.clog (clog_add (clog_mul count hstep) (log_const 1))
    exact clog_add startup.clog (clog_add (clog_mul (clog_mul dim dim) (clog_add (clog_add query check.clog) (log_const 1))) (log_const 2))
  · exact poly_max ((poly_max (poly_max hw (const 1)) aux).add startup)
      (poly_max (poly_max ((poly_max hw aux).add load) schur) ((((aux.add hw).add (he.mul hv)).add (const 1)).add check))

/-- An eventual power of the input length bounds both the bit exponent of
the clock and the number of bits on any stack. -/
theorem eventual_power {f : ℕ → Budget} (hf : Feasible f) :
    ∃ c N : ℕ, ∀ n ≥ N, (f n).time ≤ 2^(n^c) ∧ (f n).space ≤ n^c := by
  obtain ⟨T,t,Nt,ht⟩ := hf.time
  obtain ⟨S,s,Ns,hs⟩ := hf.space
  refine ⟨max t s+1,max (max Nt Ns) (max 1 (max T S)),fun n hn => ?_⟩
  have hn1 : 1 ≤ n := by omega
  have ts := Nat.pow_le_pow_right hn1 (Nat.le_max_left t s)
  have ss := Nat.pow_le_pow_right hn1 (Nat.le_max_right t s)
  have ht' := (ht n (by omega)).trans (Nat.mul_le_mul (by omega : T ≤ n) ts)
  have hs' := (hs n (by omega)).trans (Nat.mul_le_mul (by omega : S ≤ n) ss)
  rw [pow_succ']
  exact ⟨(Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) ht'), hs'⟩

end RankQuery.Stack.Coordinate.ConcreteResources

end VPVNP
end Computability
end OAI
