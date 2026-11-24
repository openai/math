import OAI.Computability.VPVNP.RankQueryConcreteResources
import OAI.Computability.VPVNP.RankCoordinateSelectedMinor
import OAI.Computability.VPVNP.RankCoordinatePairReader
import OAI.Computability.VPVNP.RankCoordinateDynamic
import OAI.Computability.VPVNP.RankCoordinateLabelWord
import OAI.Computability.VPVNP.RankCoordinateRootInit
import OAI.Computability.VPVNP.RankCoordinateReaderSpace

/-!
# Bounds for the installed coordinate readers of Appendix D.2

Each index selector may scan exponentially many prefixes. Each prefix runs
the full rectangular rank machine, and a determinant repeatedly calls both
selectors. These routines have fixed port types. The height of the suspended
caller is charged at each level, independently of the number of loop iterations.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.ConcreteResources

open PolynomiallyBounded Cost

variable {d w v e A S B E rows cols r : ℕ → ℕ}

theorem ordinal_overhead_poly (hw : PB w) : PB (fun i => OrdinalABI.overhead (w i)) := by
  have copy := ((const 5).mul hw).add (const 2)
  exact (((hw.add (const 1)).add copy).add copy).add ((const _).mul ((const 100).mul ((hw.add (const 1)).pow 2)))

theorem dynamic_overhead_poly (hw : PB w) : PB (fun i => Dynamic.overhead (w i)) := by
  have sq := (const 100).mul ((hw.add (const 1)).pow 2)
  exact (((const _).mul sq).add (hw.add (const 1))).add ((const _).mul sq)

theorem label_feasible {label : ℕ → ℕ} (hl : PB label) (hw : PB w) :
    Feasible (fun i => ⟨LabelWord.clock (label i) (w i), max (label i) (w i) + LabelWord.clock (label i) (w i)⟩) := by
  have clock := ((((const 5).mul hl).add (const 2)).add (const 1)).add
    (((hl.add (const 1)).mul (((const 4).mul hw).add (const 3))).add (const 1))
  exact ⟨clock.clog,(poly_max hl hw).add clock⟩

theorem selector_feasible (K : Type) [Fintype K] (hr : LB rows)
    (hd : PB d) (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hS : PB S) (hB : LB B) :
    Feasible (fun i => ⟨Select.scanTime K (rows i) (d i) (w i) (v i) (e i) (B i) (A i) (S i) + OrdinalABI.overhead (w i),
      Select.scanSpace K (d i) (w i) (v i) (e i) (A i) (S i) + OrdinalABI.overhead (w i)⟩) := by
  let rank := rank_feasible hd hw hv he hA hS hB
  have cap : PB (fun i => Select.workCap (d i) (w i) (v i) (e i) (A i) (S i)) :=
    poly_max (((((hw.add hv).add he).add (he.mul hv)).add hA).add (const 1)) rank.space
  let card := Fintype.card (Cursor.PrefixPort K)
  have copy := ((const card).mul (((const 5).mul cap).add (const 2))).add (const 1)
  have ret := ((hw.add (const 1)).add (((const 5).mul hw).add (const 2))).add
    (((const card).mul (cap.add (const 1))).add (const 1))
  have rankCall := clog_add (clog_add copy.clog rank.time) ret.clog
  have arith := (const 2).mul ((const 100).mul ((hw.add (const 1)).pow 2))
  have cmp := ((const 20).mul hw).add (const 10)
  have perPrefix := clog_add (clog_add (clog_add (clog_add arith.clog rankCall) cmp.clog) (log_const 1)) arith.clog
  have space := poly_max (hw.add arith) (cap.add (poly_max copy ret))
  have extra := ordinal_overhead_poly hw
  exact ⟨clog_add (clog_mul hr perPrefix) extra.clog,space.add extra⟩

/-- The query-dependent replacement ordinal and source monomial are obtained
by a register routine around the same row selector. -/
theorem dynamic_feasible {selector : ℕ → Budget} (hs : Feasible selector) (hw : PB w) :
    Feasible (fun i => ⟨(selector i).time + Dynamic.overhead (w i), (selector i).space + Dynamic.overhead (w i)⟩) :=
  ⟨clog_add hs.time (dynamic_overhead_poly hw).clog, hs.space.add (dynamic_overhead_poly hw)⟩

theorem selected_feasible (K : Type) [Fintype K] (hr : LB rows) (hc : LB cols)
    (hd : PB d) (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hS : PB S) (hB : LB B) (hE : LB E) :
    Feasible (fun i => ⟨SelectedMinor.time K (rows i) (cols i) (d i) (w i) (v i) (e i) (B i) (A i) (S i) (E i),
      SelectedMinor.space K (d i) (w i) (v i) (e i) (A i) (S i)⟩) := by
  have row := selector_feasible K hr hd hw hv he hA hS hB
  have col := selector_feasible K hc hd hw hv he hA hS hB
  have clear := (const 2).mul (hw.add (const 1))
  exact ⟨clog_add (clog_add (clog_add row.time col.time) hE) clear.clog, poly_max row.space (poly_max hS hA)⟩

/-- A common budget for both determinants' matrix entry readers. The
comparison and choice of target occur at each entry of the numerator. -/
def minorBudget (K : Type) [Fintype K] (rows cols d w v e B A S E : ℕ) : Budget :=
  ⟨20*w+10+(max (SelectedMinor.time K rows cols d w v e B A S B) (SelectedMinor.time K rows cols d w v e B A S E)+1),
   max (SelectedMinor.space K d w v e A S) (w+(20*w+10))⟩

theorem minor_den_covers (K : Type) [Fintype K] (rows cols d w v e B A S E : ℕ) :
    SelectedMinor.time K rows cols d w v e B A S B ≤ (minorBudget K rows cols d w v e B A S E).time ∧
    SelectedMinor.space K d w v e A S ≤ (minorBudget K rows cols d w v e B A S E).space := by
  dsimp only [minorBudget]
  omega

theorem minor_feasible (K : Type) [Fintype K] (hr : LB rows) (hc : LB cols)
    (hd : PB d) (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hS : PB S) (hB : LB B) (hE : LB E) :
    Feasible (fun i => minorBudget K (rows i) (cols i) (d i) (w i) (v i) (e i) (B i) (A i) (S i) (E i)) := by
  have den := selected_feasible K hr hc hd hw hv he hA hS hB hB
  have target := selected_feasible K hr hc hd hw hv he hA hS hB hE
  have cmp := ((const 20).mul hw).add (const 10)
  exact ⟨clog_add cmp.clog (clog_add (log_max den.time target.time) (log_const 1)),poly_max den.space (hw.add cmp)⟩

theorem templateCap_poly (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) :
    PB (fun i => RootInit.templateCap (w i) (v i) (e i) (A i)) := by
  have live := (((hw.add hv).add he).add (he.mul hv)).add hA
  exact poly_max (poly_max live (poly_max (const 1) (poly_max hw (he.mul hv)))) ((he.add (const 1)).mul (hv.add (const 1)))

theorem loadClock_poly (H : Type) [Fintype H] {M : ℕ → ℕ} (hM : PB M) : PB (fun i => RootInit.loadClock H (M i)) :=
  ((const (Fintype.card H)).mul (((const 5).mul hM).add (const 2))).add (const 1)

theorem divideClock_poly (he : PB e) (hv : PB v) : PB (fun i => Cramer.divideClock (e i) (v i)) :=
  (((const 7100).mul ((he.add (const 1)).pow 3)).mul ((hv.add (const 1)).pow 3)).of_le fun _ => Cramer.divideClock_le ..

/-- Reserve space for the preparation, both determinant evaluations, and
packed finite-field inversion and multiplication. -/
def pairPeak (r w v e A S preparation : ℕ) :=
  max preparation (max (PlainEngine.querySpace r w v e A S) ((e+1)*(v+1)+Cramer.divideClock e v))

theorem pairPeak_covers (r w v e A S preparation : ℕ) :
    preparation ≤ pairPeak r w v e A S preparation ∧
    PlainEngine.querySpace r w v e A S ≤ pairPeak r w v e A S preparation ∧
    (e+1)*(v+1)+Cramer.divideClock e v ≤ pairPeak r w v e A S preparation :=
  ⟨le_max_left ..,(le_max_left ..).trans (le_max_right ..),(le_max_right ..).trans (le_max_right ..)⟩

/-- The clock and peak from the two-determinant machine, including the
determinant-independent field division and all return-workspace clearing. -/
def pairBudget (H : Type) [Fintype H] (r w v e A : ℕ) (minor prep : Budget) : Budget :=
  let peak := pairPeak r w v e A minor.space prep.space
  ⟨NativeReader.pairTime H prep.time r w v e minor.time peak, peak + NativeReader.returnClock H peak⟩

theorem pair_feasible (H : Type) [Fintype H] {minor prep : ℕ → Budget}
    (hr : LB r) (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A)
    (hm : Feasible minor) (hp : Feasible prep) :
    Feasible (fun i => pairBudget H (r i) (w i) (v i) (e i) (A i) (minor i) (prep i)) := by
  have det := plain_feasible hr hw hv he hA hm.space hm.time
  have divide := divideClock_poly he hv
  have peak := poly_max hp.space (poly_max det.space (((he.add (const 1)).mul (hv.add (const 1))).add divide))
  have ret := (((const 5).mul peak).add (const 2)).add (((const (Fintype.card H)).mul (peak.add (const 1))).add (const 1))
  exact ⟨clog_add (clog_add (clog_add hp.time (clog_mul (log_const 2) det.time)) divide.clog) ret.clog,peak.add ret⟩

/-- Mount the physical reader on the evaluator. The caller's untouched index
and field registers coexist with the scalar query's own workspace. -/
theorem mounted_feasible {native : ℕ → Budget} (hn : Feasible native) (hw : PB w) (hv : PB v) (he : PB e) :
    Feasible (fun i => ⟨(native i).time, max (native i).space (Reader.callerPeak (w i) (e i) (v i))⟩) :=
  ⟨hn.time, poly_max hn.space (poly_max hw (poly_max hv (poly_max he (he.mul hv))))⟩

/-- One exponent and one threshold work for every dense entry at an input
length. Only the base coefficient accesses, the shape, and the staging of
the current query occur in the hypotheses. -/
theorem mounted_pair_time_space (H K : Type) [Fintype H] [Fintype K] {prep : ℕ → Budget} {V : ℕ → ℕ}
    (hr : LB rows) (hc : LB cols) (horder : LB r)
    (hd : PB d) (hw : PB w) (hv : PB v) (he : PB e) (hA : PB A) (hS : PB S)
    (hB : LB B) (hE : LB E) (hV : PB V) (hp : Feasible prep) :
    let minors := fun i => minorBudget K (rows i) (cols i) (d i) (w i) (v i) (e i) (B i) (A i) (S i) (E i)
    let pair := fun i => pairBudget H (r i) (w i) (v i) (e i) (V i) (minors i) (prep i)
    ∃ c N : ℕ, ∀ i ≥ N, (pair i).time ≤ 2^(i^c) ∧
      max (pair i).space (Reader.callerPeak (w i) (e i) (v i)) ≤ i^c := by
  let hm := minor_feasible K hr hc hd hw hv he hA hS hB hE
  exact eventual_power (mounted_feasible (pair_feasible H horder hw hv he hV hm hp) hw hv he)

end RankQuery.Stack.Coordinate.ConcreteResources

end VPVNP
end Computability
end OAI
