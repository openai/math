import OAI.Computability.VPVNP.RankQueryResourceBounds
import OAI.Computability.VPVNP.RankQueryBoundedExecution
import OAI.Computability.VPVNP.RankCoordinateCramer
import OAI.Computability.VPVNP.MacaulayQueryBounds
import OAI.Computability.VPVNP.RankQueryDescribeBounds
import OAI.Computability.VPVNP.RankQueryStackGramSpace

/-!
# Fixed-depth resource bounds for Appendix D coordinate queries

The augmented row count, its column count and its rank fit under a common
binary size bound. The base scalar reader can have a singly exponential
clock and polynomial stack height. The two prefix scans in a minor entry
access the original matrix and its transpose. The determinant caller visits
these entries one at a time. Repeated calls multiply clocks and share the
maximum of their stack bounds.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.Coordinate.Cost

/-- Time and peak height of a physical stack subroutine. -/
structure Budget where
  /-- Upper bound on the number of stack-machine instructions in the subroutine. -/
  time : ℕ
  /-- Upper bound on the peak height of its stacks during execution. -/
  space : ℕ

/-- The two subroutines use the same named bank and return at their boundaries. -/
def Budget.thenRun (a b : Budget) : Budget := ⟨a.time+b.time, max a.space b.space⟩

/-- A loop bound multiplies only the time. -/
def Budget.repeated (a : Budget) (count : ℕ) : Budget := ⟨count*a.time, a.space⟩

/-- Parameters common to the original rectangular matrix and its Cramer minors.
`bits` bounds the logarithms of both original dimensions. `local` covers the
short Schur actions and the fixed input/output adapters of each scalar read.
`aux` is the maximum initial stack height at those boundaries. -/
structure Parameters where
  /-- Common bound on the binary logarithms of the original matrix dimensions. -/
  bits : ℕ
  /-- Bit width of addresses used for matrix entries and suspended frames. -/
  addr : ℕ
  /-- Bit width of one base-field coefficient in the packed scalar representation. -/
  limb : ℕ
  /-- Extension degree, hence the number of base-field coefficients in a scalar. -/
  degree : ℕ
  /-- Allowance for short Schur actions and the entry reader's setup and return steps. -/
  localWork : ℕ
  /-- Maximum initial height of auxiliary stacks at the reader's call boundaries. -/
  aux : ℕ

/-- Running a bounded number of sequential scalar reads within a descriptor,
with short setup and teardown. The caller's suspended frames are included in
its initial height. -/
def descriptor (p : Parameters) (number : ℕ) (base : Budget) : Budget :=
  let live := max 1 (max p.addr (p.degree*p.limb))
  let frames := (p.bits+4+p.bits)*(2*live+1)
  let initial := max (p.addr+p.limb+p.degree+p.degree*p.limb+p.aux) (max live frames)
  ⟨number*base.time+p.localWork, max base.space initial + p.localWork⟩

/-- A Gram entry requires at most two underlying rectangular entry reads. -/
def gramDescriptor (p : Parameters) (base : Budget) := descriptor p 2 base

/-- The actual weighted-Gram descriptor and all saved stack frames fit this
budget whenever the short-action allowance covers its register overhead. -/
theorem gramDescriptor_covers (p : Parameters) (base : Budget)
    (hlocal : DescribeAdapter.clock p.addr p.limb p.degree 0 ≤ p.localWork) :
    let start := GramEngine.entryCap p.addr p.limb p.degree p.aux (p.bits+4+p.bits)
    DescribeAdapter.clock p.addr p.limb p.degree base.time ≤ (gramDescriptor p base).time ∧
      max start (DescribeAdapter.space p.addr p.limb p.degree start base.space) ≤
        (gramDescriptor p base).space := by
  intro start
  change _ ≤ 2*base.time+p.localWork ∧ _ ≤ max base.space start + p.localWork
  rw [DescribeAdapter.clock_eq]
  refine ⟨Nat.add_le_add_left hlocal _, max_le (by omega) ?_⟩
  have h := DescribeAdapter.space_le_clock p.addr p.limb p.degree start base.space
  omega

/-- A constant-matrix descriptor reads one selected entry. Its signed-entry
adapter may spend a short additional allowance. This checks the time and
peak-height formulas of the actual Schur description routine. -/
theorem singleDescriptor_covers (p : Parameters) (base : Budget) (extra : ℕ)
    (hlocal : DescribeAdapter.timeWith p.addr p.limb p.degree extra ≤ p.localWork) :
    let start := GramEngine.entryCap p.addr p.limb p.degree p.aux (p.bits+4+p.bits)
    DescribeAdapter.timeWith p.addr p.limb p.degree (base.time+extra) ≤ (descriptor p 1 base).time ∧
      max start (DescribeAdapter.peakWith p.addr p.limb p.degree start (fun a ↦ max a base.space+extra)) ≤
        (descriptor p 1 base).space := by
  intro start
  change _ ≤ 1*base.time+p.localWork ∧ _ ≤ max base.space start + p.localWork
  unfold DescribeAdapter.timeWith at hlocal ⊢
  unfold DescribeAdapter.peakWith
  dsimp only
  rw [one_mul]
  constructor
  · omega
  · apply max_le (by omega)
    have h : max (start+Dispatch.Operation.describe.clock p.addr) base.space ≤
        max base.space start + Dispatch.Operation.describe.clock p.addr := by omega
    omega

/-- Sum the dimension bit bound, the ceiling binary logarithm of descriptor time, the local
work allowance, the address and limb widths, and the field extension degree to bound
rank-query time. -/
def rankScale (p : Parameters) (desc : Budget) :=
  p.bits + Nat.clog 2 desc.time + p.localWork + p.addr + p.limb + p.degree

/-- Common envelope for every rectangular prefix in either orientation. -/
def rank (p : Parameters) (desc : Budget) : Budget :=
  let s := rankScale p desc
  ⟨2^((4*s+10)*(4*s+7)+5*s+20),
    max (desc.space+1) (32768*(p.bits+p.aux+p.localWork+p.addr+p.limb+p.degree+1)^3)⟩

/-- The actual clock and cap from the rectangular rank control fit the envelope. -/
theorem rank_covers (p : Parameters) (desc : Budget) (rows cols : ℕ)
    (hr : rows ≤ 2^p.bits) (hc : cols ≤ 2^p.bits) :
    Cursor.boundedRankTime rows cols desc.time p.localWork p.addr p.limb p.degree ≤ (rank p desc).time ∧
    Cursor.boundedRankSpace rows desc.space p.aux p.localWork p.addr p.limb p.degree ≤ (rank p desc).space := by
  let s := rankScale p desc
  have hpow {x : ℕ} (hx : x ≤ s) : x ≤ 2^s :=
    Nat.lt_two_pow_self.le.trans (Nat.pow_le_pow_right (by decide) hx)
  have hbits : 2^p.bits ≤ 2^s := Nat.pow_le_pow_right (by decide) (by dsimp [s, rankScale]; omega)
  have hd : desc.time ≤ 2^s := (Nat.le_pow_clog (by decide) _).trans
    (Nat.pow_le_pow_right (by decide) (by dsimp [s, rankScale]; omega))
  refine ⟨Cursor.rankReadTime_le_exp _ _ _ _ _ _ _ s (hr.trans hbits) (hc.trans hbits) hd ?_ ?_ ?_ ?_,
    Cursor.rankReadSpace_le rows _ _ _ _ _ _ _ hr⟩
  all_goals apply hpow; dsimp [s, rankScale]; omega

/-- Bound for one arithmetic register operation, with its initial word already in place. -/
def arithmetic (p : Parameters) : Budget :=
  ⟨arithmeticClock p.addr, p.addr+arithmeticClock p.addr⟩

/-- The prefix tester computes the next length, requests its rank, compares with
the ordinal, then advances its cursor. This is the clock of `PrefixWords.machine_runs`
at the largest permitted prefix. -/
def prefixScan (p : Parameters) (rankCall : Budget) : Budget :=
  ⟨2^p.bits * ((arithmeticClock p.addr + rankCall.time + (20*p.addr+10)) + 1 + arithmeticClock p.addr),
    max rankCall.space (arithmetic p).space⟩

theorem prefixScan_covers (p : Parameters) (rankCall : Budget) (rows time : ℕ)
    (hr : rows ≤ 2^p.bits) (ht : time ≤ rankCall.time) :
    rows*((arithmeticClock p.addr+time+(20*p.addr+10))+1+arithmeticClock p.addr) ≤
      (prefixScan p rankCall).time ∧ p.addr+arithmeticClock p.addr ≤ (prefixScan p rankCall).space := by
  refine ⟨?_, le_max_right ..⟩
  change rows*_ ≤ 2^p.bits*((arithmeticClock p.addr+rankCall.time+(20*p.addr+10))+1+arithmeticClock p.addr)
  gcongr

/-- Two independent rank calls followed by subtraction. -/
def dimension (p : Parameters) (rankCall : Budget) : Budget :=
  (rankCall.repeated 2).thenRun (arithmetic p)

/-- Compute the combined ordinal, perform the row scan and remove the equation prefix. -/
def suffix (p : Parameters) (rankCall : Budget) : Budget :=
  ((rankCall.thenRun (arithmetic p)).thenRun (prefixScan p rankCall)).thenRun (arithmetic p)

/-- Recompute the row and column indices independently, then read either
the original entry or the replacement entry of the target row. -/
def minorEntry (p : Parameters) (rankCall base : Budget) : Budget :=
  ((prefixScan p rankCall).repeated 2).thenRun
    ⟨(20*p.addr+10)+(base.time+1), max base.space (p.addr+(20*p.addr+10))⟩

/-- A Schur determinant call on a minor, charging entry time and space separately. -/
def determinant (p : Parameters) (desc : Budget) : Budget :=
  let step := Engine.boundedStepTime desc.time p.localWork p.addr p.limb p.degree
  ⟨2^((2*p.bits+8)*(2*p.bits+5))*step + 1,
    Engine.boundedSpace desc.space p.aux (p.bits+4+p.bits) p.localWork p.addr p.limb p.degree⟩

theorem determinant_covers (p : Parameters) (desc : Budget) (r : ℕ) (hr : r ≤ 2^p.bits) :
    Cramer.SchurPair.clock r p.addr p.limb p.degree p.localWork desc.time ≤ (determinant p desc).time ∧
    Cramer.SchurPair.space r p.addr p.limb p.degree p.localWork p.aux desc.space ≤ (determinant p desc).space := by
  have hrec := SchurKey.clock_le_exp r r 0 p.bits hr hr (Nat.zero_le _)
  have hd := Nat.clog_le_of_le_pow hr
  refine ⟨Nat.add_le_add_right (Nat.mul_le_mul_right _ hrec) _, ?_⟩
  dsimp [Cramer.SchurPair.space, Cramer.SchurPair.depth, determinant, Engine.boundedSpace, Engine.runSpace]
  gcongr

/-- The inverse and multiplication stage has polynomial clock and can pay this
entire clock in space on top of its small input bank. -/
def divide (p : Parameters) : Budget :=
  let cost := Cramer.divideClock p.degree p.limb
  ⟨cost, (p.degree+1)*(p.limb+1)+cost⟩

/-- Reserve the quotient workspace already in the determinant contract. This
makes the post-determinant room hypothesis of `Cramer.SchurPair.native_runs`
hold even for a one-dimensional minor. -/
def cramerDescriptor (p : Parameters) (desc : Budget) : Budget :=
  ⟨desc.time, max desc.space (divide p).space⟩

theorem cramer_room (p : Parameters) (desc : Budget) (r : ℕ) :
    (p.degree+1)*(p.limb+1)+Cramer.divideClock p.degree p.limb ≤
      Cramer.SchurPair.space r p.addr p.limb p.degree p.localWork p.aux (cramerDescriptor p desc).space := by
  change (divide p).space ≤ max (max desc.space (divide p).space+1) _
  exact ((le_max_right ..).trans (Nat.le_succ _)).trans (le_max_left ..)

/-- Complete fixed-depth scalar query. The suffix lookup locates the input
monomial. Its offset and the two prefix ranks also supply the output ordinal
and dimension. Both determinant subcalls use the same per-entry envelope. -/
def coordinate (p : Parameters) (base : Budget) : Budget :=
  let rankCall := rank p (gramDescriptor p base)
  let entries := minorEntry p rankCall base
  let det := determinant p (cramerDescriptor p (descriptor p 1 entries))
  let indices := ((dimension p rankCall).thenRun (suffix p rankCall)).thenRun (arithmetic p)
  (indices.thenRun (det.repeated 2)).thenRun (divide p)

/-- The joint determinant and division cost in the native Cramer theorem.
The common cap also supplies room for division after both engines return. -/
theorem cramer_covers (p : Parameters) (desc : Budget) (r : ℕ) (hr : r ≤ 2^p.bits) :
    let bound := ((determinant p desc).repeated 2).thenRun (divide p)
    2*Cramer.SchurPair.clock r p.addr p.limb p.degree p.localWork desc.time +
      Cramer.divideClock p.degree p.limb ≤ bound.time ∧
      Cramer.SchurPair.space r p.addr p.limb p.degree p.localWork p.aux desc.space ≤ bound.space ∧
      (p.degree+1)*(p.limb+1)+Cramer.divideClock p.degree p.limb ≤ bound.space := by
  have ⟨ht, hs⟩ := determinant_covers p desc r hr
  exact ⟨Nat.add_le_add_right (Nat.mul_le_mul_left _ ht) _,
    hs.trans (le_max_left ..), le_max_right ..⟩

/-- The ceiling of the base-two logarithm of the budget is eventually bounded by a polynomial
in the input size. -/
abbrev LogBound (f : ℕ → ℕ) := PolynomiallyBounded (fun n ↦ Nat.clog 2 (f n))

/-- Any concrete matrix with these dimensions fits the common shape.
The allowance includes the cost of formatting a weighted Gram entry. -/
def forShape (rows cols addr limb degree other aux : ℕ) : Parameters :=
  ⟨max (Nat.clog 2 rows) (Nat.clog 2 cols), addr, limb, degree,
    max other (DescribeAdapter.allowance (max addr (max limb degree))), aux⟩

theorem forShape_sizes (rows cols addr limb degree other aux : ℕ) :
    let p := forShape rows cols addr limb degree other aux
    rows ≤ 2^p.bits ∧ cols ≤ 2^p.bits ∧ DescribeAdapter.clock addr limb degree 0 ≤ p.localWork := by
  refine ⟨(Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_left ..)),
    (Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_right ..)), ?_⟩
  exact (DescribeAdapter.overhead_le addr limb degree _ (le_max_left ..)
    ((le_max_left ..).trans (le_max_right ..)) ((le_max_right ..).trans (le_max_right ..))).trans (le_max_right ..)

/-- Feasible clocks and caps are measured on different scales. -/
structure Feasible (f : ℕ → Budget) : Prop where
  time : LogBound (fun n ↦ (f n).time)
  space : PolynomiallyBounded (fun n ↦ (f n).space)

/-- The word widths, logarithmic matrix shape, and short-action allowance
are polynomially bounded in the input length. -/
structure Small (p : ℕ → Parameters) : Prop where
  bits : PolynomiallyBounded (fun n ↦ (p n).bits)
  addr : PolynomiallyBounded (fun n ↦ (p n).addr)
  limb : PolynomiallyBounded (fun n ↦ (p n).limb)
  degree : PolynomiallyBounded (fun n ↦ (p n).degree)
  localWork : PolynomiallyBounded (fun n ↦ (p n).localWork)
  aux : PolynomiallyBounded (fun n ↦ (p n).aux)

private theorem polyMax {f g : ℕ → ℕ} (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n ↦ max (f n) (g n)) :=
  (hf.add hg).of_le fun n ↦ by omega

private theorem logMax {f g : ℕ → ℕ} (hf : LogBound f) (hg : LogBound g) :
    LogBound (fun n ↦ max (f n) (g n)) :=
  (PolynomiallyBounded.clog_add hf hg).of_le fun n ↦ Nat.clog_mono_right _ (by change max (f n) (g n) ≤ f n + g n; omega)

private theorem logConst (k : ℕ) : LogBound (fun _ ↦ k) := (PolynomiallyBounded.const k).clog

variable {p : ℕ → Parameters} {a b : ℕ → Budget}

theorem Feasible.thenRun (ha : Feasible a) (hb : Feasible b) :
    Feasible (fun n ↦ (a n).thenRun (b n)) :=
  ⟨PolynomiallyBounded.clog_add ha.time hb.time, polyMax ha.space hb.space⟩

theorem Feasible.repeated (ha : Feasible a) {f : ℕ → ℕ} (hf : LogBound f) :
    Feasible (fun n ↦ (a n).repeated (f n)) :=
  ⟨PolynomiallyBounded.clog_mul hf ha.time, ha.space⟩

-- Close bounds formed by arithmetic on the supplied polynomial-size quantities.
local macro "poly_bound" : tactic => `(tactic| repeat' first
  | assumption
  | exact PolynomiallyBounded.const _
  | apply polyMax
  | apply PolynomiallyBounded.add
  | apply PolynomiallyBounded.mul
  | apply PolynomiallyBounded.pow)

theorem Feasible.of_exponent {f : ℕ → Budget} {e : ℕ → ℕ}
    (he : PolynomiallyBounded e) (ht : ∀ n, (f n).time ≤ 2^(e n))
    (hs : PolynomiallyBounded (fun n ↦ (f n).space)) : Feasible f :=
  ⟨he.of_le (fun n ↦ Nat.clog_le_of_le_pow (ht n)), hs⟩

theorem small_forShape {rows cols addr limb degree other aux : ℕ → ℕ} (hr : LogBound rows)
    (hc : LogBound cols) (hw : PolynomiallyBounded addr) (hv : PolynomiallyBounded limb)
    (he : PolynomiallyBounded degree) (hb : PolynomiallyBounded other) (ha : PolynomiallyBounded aux) :
    Small (fun n ↦ forShape (rows n) (cols n) (addr n) (limb n) (degree n) (other n) (aux n)) := by
  let x := polyMax hw (polyMax hv he)
  have allowance := (PolynomiallyBounded.const
    (DescribeAdapter.codeCost .describe + DescribeAdapter.codeCost .gram + 4000)).mul
    ((x.add (.const 1)).pow 4)
  exact ⟨polyMax hr hc, hw, hv, he, polyMax hb allowance, ha⟩

theorem feasible_descriptor (hp : Small p) (ha : Feasible a) (number : ℕ) :
    Feasible (fun n ↦ descriptor (p n) number (a n)) := by
  obtain ⟨hi, hw, hv, he, hB, hA⟩ := hp
  obtain ⟨ht, hs⟩ := ha
  let live := polyMax (PolynomiallyBounded.const 1) (polyMax hw (he.mul hv))
  let depth := (hi.add (.const 4)).add hi
  let history := depth.mul (((PolynomiallyBounded.const 2).mul live).add (.const 1))
  let initial := polyMax ((((hw.add hv).add he).add (he.mul hv)).add hA) (polyMax live history)
  exact ⟨PolynomiallyBounded.clog_add (PolynomiallyBounded.clog_mul (logConst number) ht) hB.clog,
    (polyMax hs initial).add hB⟩

private theorem poly_rankScale (hp : Small p) (ha : Feasible a) :
    PolynomiallyBounded (fun n ↦ rankScale (p n) (a n)) := by
  obtain ⟨hi, hw, hv, he, hB, hA⟩ := hp
  obtain ⟨ht, hs⟩ := ha
  dsimp only [rankScale]
  poly_bound

theorem feasible_rank (hp : Small p) (ha : Feasible a) : Feasible (fun n ↦ rank (p n) (a n)) := by
  have scale := poly_rankScale hp ha
  obtain ⟨hi, hw, hv, he, hB, hA⟩ := hp
  obtain ⟨ht, hs⟩ := ha
  constructor
  · apply PolynomiallyBounded.clog_pow (logConst 2)
    poly_bound
  · dsimp only [rank]
    poly_bound

private theorem feasible_arithmetic (hp : Small p) : Feasible (fun n ↦ arithmetic (p n)) := by
  have hw := hp.addr
  have ht : PolynomiallyBounded (fun n ↦ arithmeticClock (p n).addr) := by
    dsimp only [arithmeticClock]
    poly_bound
  exact ⟨ht.clog, hw.add ht⟩

theorem feasible_prefixScan (hp : Small p) (ha : Feasible a) :
    Feasible (fun n ↦ prefixScan (p n) (a n)) := by
  have shape := PolynomiallyBounded.clog_pow (logConst 2) hp.bits
  have localTime := (feasible_arithmetic hp).time
  have cmp := (((PolynomiallyBounded.const 20).mul hp.addr).add (.const 10)).clog
  have ht := ha.time
  refine ⟨?_, polyMax ha.space (feasible_arithmetic hp).space⟩
  open PolynomiallyBounded in
    exact clog_mul shape (clog_add (clog_add (clog_add (clog_add localTime ht) cmp) (logConst 1)) localTime)

theorem feasible_minorEntry (hp : Small p) (ha : Feasible a) (hb : Feasible b) :
    Feasible (fun n ↦ minorEntry (p n) (a n) (b n)) := by
  apply ((feasible_prefixScan hp ha).repeated (logConst 2)).thenRun
  let cmp := ((PolynomiallyBounded.const 20).mul hp.addr).add (.const 10)
  exact ⟨PolynomiallyBounded.clog_add cmp.clog (PolynomiallyBounded.clog_add hb.time (logConst 1)),
    polyMax hb.space (hp.addr.add cmp)⟩

theorem feasible_determinant (hp : Small p) (ha : Feasible a) :
    Feasible (fun n ↦ determinant (p n) (a n)) := by
  obtain ⟨hi, hw, hv, he, hB, hA⟩ := hp
  obtain ⟨ht, hs⟩ := ha
  have count : LogBound (fun n ↦ 2^((2*(p n).bits+8)*(2*(p n).bits+5))) := by
    apply PolynomiallyBounded.clog_pow (logConst 2)
    poly_bound
  let live := polyMax (PolynomiallyBounded.const 1) (polyMax hw (he.mul hv))
  have short : PolynomiallyBounded (fun n ↦ Engine.stepBudget (p n).localWork (p n).addr (p n).limb (p n).degree) :=
    (PolynomiallyBounded.const 4).mul ((hB.add ((PolynomiallyBounded.const 10).mul
      (((PolynomiallyBounded.const 3).mul live).add (.const 2)))).add (.const 5))
  constructor
  · exact PolynomiallyBounded.clog_add (PolynomiallyBounded.clog_mul count
      (logMax (PolynomiallyBounded.clog_add ht (logConst 1)) short.clog)) (logConst 1)
  · let depth := (hi.add (.const 4)).add hi
    let history := depth.mul (((PolynomiallyBounded.const 2).mul live).add (.const 1))
    exact polyMax (hs.add (.const 1)) ((polyMax hA (polyMax live history)).add short)

theorem feasible_divide (hp : Small p) : Feasible (fun n ↦ divide (p n)) := by
  have he := hp.degree
  have hv := hp.limb
  have h : PolynomiallyBounded (fun n ↦ Cramer.divideClock (p n).degree (p n).limb) := by
    refine (PolynomiallyBounded.of_le (g := fun n ↦ 7100*((p n).degree+1)^3*((p n).limb+1)^3) ?_
      fun n ↦ Cramer.divideClock_le ..)
    poly_bound
  exact ⟨h.clog, (((he.add (.const 1)).mul (hv.add (.const 1))).add h)⟩

/-- Composition covers both expensive scans in each minor without placing any
exponential clock in a space bound. -/
theorem feasible_coordinate (hp : Small p) (hb : Feasible b) :
    Feasible (fun n ↦ coordinate (p n) (b n)) := by
  have hr := feasible_rank hp (feasible_descriptor hp hb 2)
  have hs := feasible_prefixScan hp hr
  have har := feasible_arithmetic hp
  have hdim := (hr.repeated (logConst 2)).thenRun har
  have hsuf := ((hr.thenRun har).thenRun hs).thenRun har
  have hentry := feasible_minorEntry hp hr hb
  have hd := feasible_descriptor hp hentry 1
  have hd' : Feasible (fun n ↦ cramerDescriptor (p n) (descriptor (p n) 1
      (minorEntry (p n) (rank (p n) (gramDescriptor (p n) (b n))) (b n)))) :=
    ⟨hd.time, polyMax hd.space (feasible_divide hp).space⟩
  have hdet := feasible_determinant hp hd'
  exact (((hdim.thenRun hsuf).thenRun har).thenRun (hdet.repeated (logConst 2))).thenRun (feasible_divide hp)

/-- A single polynomial exponent bounds the complete clock, and a separate
polynomial bounds the peak space. Both hold uniformly at every length. -/
theorem coordinate_time_space (hp : Small p) (hb : Feasible b) :
    ∃ exponent : ℕ → ℕ, PolynomiallyBounded exponent ∧
      (∀ n, (coordinate (p n) (b n)).time ≤ 2^(exponent n)) ∧
      PolynomiallyBounded (fun n ↦ (coordinate (p n) (b n)).space) := by
  have h := feasible_coordinate hp hb
  exact ⟨_, h.time, fun n ↦ Nat.le_pow_clog (by decide) _, h.space⟩

open RadicalCertificate.MonomialIndex

/-- Instantiate the two matrix dimensions from the actual graded Macaulay
enumeration. The row count includes the equation prefix and the monomial suffix. -/
def forSlice {t e : ℕ} {K : Type*} (S : QueryData t e K) (addr limb degree other aux : ℕ) :=
  forShape (e * size t S.multiplierDegree + size t S.pointBound) (size t S.columnDegree)
    addr limb degree other aux

theorem small_forSlice {t e : ℕ → ℕ} {K : ℕ → Type*} (S : (n : ℕ) → QueryData (t n) (e n) (K n))
    {addr limb degree other aux : ℕ → ℕ} (ht : PolynomiallyBounded t) (he : LogBound e)
    (hQ : LogBound (fun n ↦ (S n).fieldOrder)) (hd : LogBound (fun n ↦ (S n).degreeBound))
    (hN : LogBound (fun n ↦ (S n).pointBound)) (hQpos : ∀ n, 2 ≤ (S n).fieldOrder)
    (hw : PolynomiallyBounded addr) (hv : PolynomiallyBounded limb) (hf : PolynomiallyBounded degree)
    (hb : PolynomiallyBounded other) (ha : PolynomiallyBounded aux) :
    Small (fun n ↦ forSlice (S n) (addr n) (limb n) (degree n) (other n) (aux n)) := by
  obtain ⟨hrows, hcols, _⟩ := bounded_query_dimensions S ht he hQ hd hN hQpos
  exact small_forShape hrows hcols hw hv hf hb ha

end RankQuery.Stack.Coordinate.Cost

end VPVNP
end Computability
end OAI
