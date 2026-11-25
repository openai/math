import OAI.Optimization.LinearProgramming.Lattice.BitProbe
import OAI.Optimization.LinearProgramming.Lattice.DyadicEntrySize

/-! Invariants for all sign answers in the finite residual probe. The current dyadic
numerator stays strictly between the two signed endpoints of its positive denominator. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver
namespace Probe

structure RowBound (p M : ℕ) (a : Row) : Prop where
  length : a.length ≤ p
  entry : ∀ v ∈ a, v.natAbs ≤ M

structure TableBound (p M : ℕ) (a : IntMatrix) : Prop where
  length : a.length ≤ p
  row : ∀ r ∈ a, RowBound p M r

structure ParamBound (p k M : ℕ) (z : Params) : Prop where
  dimension : z.1.1 ≤ p
  precision : z.1.2 ≤ k
  rows : TableBound p M z.2

structure MaxBound (p k M : ℕ) (s : MaxState) : Prop where
  params : ParamBound p k M s.1.1
  remaining : TableBound p M s.1.2
  candidate : RowBound p M s.2.1
  best : RowBound p M s.2.2

structure PivotBound (p k M : ℕ) (s : Pivot) : Prop where
  params : ParamBound p k M s.1
  row : RowBound p M s.2

structure RatBound (k : ℕ) (q : ℚ) : Prop where
  numerator : q.num.natAbs.size ≤ k+1
  denominator : q.den.size ≤ k+1

def ValueBound (k : ℕ) (xs : List ℚ) := ∀ v ∈ xs, RatBound k v

def CounterBound (precision : ℕ) (a : ℤ) (d left : ℕ) : Prop :=
  ∃ t, d = 2^t ∧ a.natAbs < d ∧ t+left+1 ≤ precision

structure RatioBound (p k M : ℕ) (s : Ratio) : Prop where
  pivot : PivotBound p k M s.1.1
  row : RowBound p M s.1.2.1
  remaining : TableBound p M s.1.2.2
  count : s.2.2.2.length+s.1.2.2.length+1 ≤ p
  values : ValueBound k s.2.2.2
  counter : CounterBound s.1.1.1.1.2 s.2.1.1 s.2.1.2 s.2.2.1

def CarryBound (p k M : ℕ) : Carry → Prop
  | .inl (.inl s) | .inl (.inr s) => MaxBound p k M s
  | .inr (.inl s) => PivotBound p k M s
  | .inr (.inr s) => RatioBound p k M s

def queryMagnitude (k M : ℕ) := 2*2^k*M

def ActionBound (p k M : ℕ) : Action → Prop
  | .inl r => r.2.length ≤ p ∧ ValueBound k r.2
  | .inr (a,c) => RowBound p (queryMagnitude k M) a ∧ CarryBound p k M c

private theorem RowBound.widen {p M : ℕ} {a : Row} (h : RowBound p M a) (k : ℕ) :
    RowBound p (queryMagnitude k M) a := by
  have hM : M ≤ queryMagnitude k M := by
    unfold queryMagnitude
    exact Nat.le_mul_of_pos_left M (by positivity)
  exact ⟨h.length,fun v hv => (h.entry v hv).trans hM⟩

private theorem RowBound.negate {p M : ℕ} {a : Row} (h : RowBound p M a) :
    RowBound p M (a.map Neg.neg) := by
  refine ⟨by simpa using h.length,?_⟩
  intro z hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  simpa using h.entry v hv

private theorem RowBound.read {p M : ℕ} {a : Row} (h : RowBound p M a) (i : ℕ) :
    (readAt 0 a i).natAbs ≤ M := by
  unfold readAt
  cases he : a.drop i with
  | nil => simp
  | cons x xs =>
    apply h.entry x
    exact List.mem_of_mem_drop (he ▸ List.mem_cons_self)

private theorem RowBound.combine {p k M : ℕ} {a b : Row} (ha : RowBound p M a)
    (hb : RowBound p M b) (u v : ℤ) (hu : u.natAbs ≤ 2^k) (hv : v.natAbs ≤ 2^k) :
    RowBound p (queryMagnitude k M) (combineRows ((u,v),a,b)) := by
  refine ⟨by simpa [combineRows] using ha.length,?_⟩
  intro x hx
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hx
  change (u*readAt 0 a j - v*readAt 0 b j).natAbs ≤ _
  calc
    _ ≤ (u*readAt 0 a j).natAbs + (v*readAt 0 b j).natAbs := Int.natAbs_sub_le ..
    _ ≤ 2^k*M + 2^k*M := by
      simp only [Int.natAbs_mul]
      exact Nat.add_le_add (Nat.mul_le_mul hu (ha.read j)) (Nat.mul_le_mul hv (hb.read j))
    _ = queryMagnitude k M := by unfold queryMagnitude; ring

private theorem TableBound.tail {p M : ℕ} {a : Row} {xs : IntMatrix} (h : TableBound p M (a::xs)) :
    TableBound p M xs := ⟨Nat.le_of_succ_le h.length,fun x hx => h.row x (List.mem_cons_of_mem _ hx)⟩

private theorem nextMax_bounded {p k M : ℕ} {z : Params} {todo : IntMatrix} {best : Row}
    (hz : ParamBound p k M z) (ht : TableBound p M todo) (hb : RowBound p M best) :
    ActionBound p k M (nextMax z todo best) := by
  cases todo with
  | nil => exact ⟨hb.negate.widen k, ⟨hz,hb⟩⟩
  | cons a tail =>
    have ha := ht.row a List.mem_cons_self
    exact ⟨ha.widen k, ⟨hz,ht.tail,ha,hb⟩⟩

theorem start_bounded {p k M : ℕ} {z : Params} (hz : ParamBound p k M z) : ActionBound p k M (start z) := by
  apply nextMax_bounded hz
  · exact ⟨by simpa using hz.rows.length,fun r hr => hz.rows.row r (by simpa using hr)⟩
  · refine ⟨by simpa using hz.dimension,?_⟩
    intro i hi
    obtain rfl : i = 0 := (List.mem_replicate.mp hi).2
    simp

private theorem orient_bounded {p k M : ℕ} (answer : Bool) {s : MaxState} (hs : MaxBound p k M s) :
    ActionBound p k M (orient answer s) := by
  let a := if answer then s.2.1 else s.2.1.map Neg.neg
  have ha : RowBound p M a := by
    cases answer
    · exact hs.candidate.negate
    · exact hs.candidate
  have hone : (1:ℤ).natAbs ≤ 2^k := Nat.succ_le_of_lt (by positivity : 0 < (2:ℕ)^k)
  exact ⟨ha.combine hs.best 1 1 hone hone, ⟨hs.params,hs.remaining,ha,hs.best⟩⟩

private theorem compare_bounded {p k M : ℕ} (answer : Bool) {s : MaxState} (hs : MaxBound p k M s) :
    ActionBound p k M (compare answer s) := by
  apply nextMax_bounded hs.params hs.remaining
  cases answer
  · exact hs.best
  · exact hs.candidate

private theorem emitRatio_bounded {p k M : ℕ} {s : Ratio} (hs : RatioBound p k M s) :
    ActionBound p k M (emitRatio s) := by
  obtain ⟨t,hd,hn,ht⟩ := hs.counter
  have hp := hs.pivot.params.precision
  have hden : s.2.1.2 ≤ 2^k := hd.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨hs.row.combine hs.pivot.row _ _ (by simpa using hden) (hn.le.trans hden),hs⟩

theorem nextRow_bounded {p k M : ℕ} {pivot : Pivot} {rs : IntMatrix} {values : List ℚ}
    (hp : PivotBound p k M pivot) (hk : 0 < pivot.1.1.2) (hr : TableBound p M rs)
    (hc : values.length+rs.length ≤ p) (hv : ValueBound k values) :
    ActionBound p k M (nextRow pivot rs values) := by
  cases rs with
  | nil => exact ⟨by simpa using hc, fun x hx => hv x (by simpa using hx)⟩
  | cons a tail =>
    apply emitRatio_bounded
    refine ⟨hp,hr.row a List.mem_cons_self,hr.tail,?_,hv,?_⟩
    · simpa [Nat.add_assoc] using hc
    · exact ⟨0,by simp,by change (0:ℤ).natAbs < (1:ℕ); decide,by dsimp; omega⟩

theorem nextRow_single_bounded {p k M : ℕ} {pivot : Pivot} {lhs : Row}
    (hp : PivotBound p k M pivot) (hk : 0 < pivot.1.1.2)
    (hr : RowBound p M lhs) (hpos : 1 ≤ p) :
    ActionBound p k M (nextRow pivot [lhs] []) := by
  apply nextRow_bounded hp hk
  · exact ⟨hpos,fun r h => (List.mem_singleton.mp h) ▸ hr⟩
  · simpa using hpos
  · simp [ValueBound]

private theorem zeroReply_bounded {p k M : ℕ} (answer : Bool) {s : Pivot} (hs : PivotBound p k M s) :
    ActionBound p k M (zeroReply answer s) := by
  unfold zeroReply
  split
  · exact ⟨Nat.zero_le _,by simp [ValueBound]⟩
  · split
    · refine ⟨by simpa using hs.params.rows.length,?_⟩
      intro q hq
      obtain rfl : q = 0 := (List.mem_replicate.mp hq).2
      exact ⟨by simp,by simp⟩
    · rename_i hk
      exact nextRow_bounded hs (Nat.pos_of_ne_zero hk) hs.params.rows
        (by simpa using hs.params.rows.length) (by simp [ValueBound])

private theorem counter_step {a : ℤ} {d left precision k : ℕ}
    (hc : CounterBound precision a d left) (hk : precision ≤ k) (answer : Bool) :
    let u := 2*a + if answer then 1 else -1
    let v := 2*d
    RatBound k ((u:ℚ)/(v:ℚ)) ∧ 0 < precision ∧
      (left ≠ 0 → CounterBound precision u v (left-1)) := by
  obtain ⟨t,hd,ha,ht⟩ := hc
  let u := 2*a + if answer then 1 else -1
  let v := 2*d
  have hsign : (if answer then (1:ℤ) else -1).natAbs = 1 := by cases answer <;> decide
  have hu : u.natAbs < v := calc
    _ ≤ (2*a).natAbs+(if answer then (1:ℤ) else -1).natAbs := Int.natAbs_add_le ..
    _ = 2*a.natAbs+1 := by rw [Int.natAbs_mul,hsign]; rfl
    _ < v := by dsimp [v]; omega
  have hv : v = 2^(t+1) := by simp [v,hd,pow_succ,Nat.mul_comm]
  have hmag : |u| ≤ (2:ℤ)^(t+1) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast (hu.le.trans_eq hv)
  have hs := OAI.Optimization.LinearProgramming.Lattice.dyadic_entry_size u (t+1) hmag
  have hvq : (v:ℚ) = (2:ℚ)^(t+1) := by exact_mod_cast hv
  change RatBound k ((u:ℚ)/(v:ℚ)) ∧ _
  rw [hvq]
  refine ⟨⟨hs.1.trans (by omega),hs.2.trans (by omega)⟩,by omega,?_⟩
  intro hl
  exact ⟨t+1,hv,hu,by omega⟩

private theorem ratioReply_bounded {p k M : ℕ} (answer : Bool) {s : Ratio} (hs : RatioBound p k M s) :
    ActionBound p k M (ratioReply answer s) := by
  let u := 2*s.2.1.1 + if answer then 1 else -1
  let v := 2*s.2.1.2
  obtain ⟨hq,hpos,hnext⟩ := counter_step hs.counter hs.pivot.params.precision answer
  unfold ratioReply
  dsimp only
  split
  · apply nextRow_bounded hs.pivot hpos hs.remaining
    · simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hs.count
    · intro z hz
      rcases List.mem_cons.mp hz with rfl | h
      · exact hq
      · exact hs.values z h
  · rename_i hnonzero
    exact emitRatio_bounded ⟨hs.pivot,hs.row,hs.remaining,hs.count,hs.values,hnext hnonzero⟩

/-- Every one of the possible sign answers preserves the bounds. -/
theorem advance_bounded {p k M : ℕ} (answer : Bool) {c : Carry} (hc : CarryBound p k M c) :
    ActionBound p k M (advance answer c) := by
  rcases c with (s|s)|(s|s)
  · exact orient_bounded answer hc
  · exact compare_bounded answer hc
  · exact zeroReply_bounded answer hc
  · exact ratioReply_bounded answer hc

theorem bounded_along {p k M : ℕ} {a b : Action} (hstart : ActionBound p k M a)
    (reach : Reaches a b) : ActionBound p k M b := by
  induction reach with
  | refl => exact hstart
  | step _ answer ih => exact advance_bounded answer ih.2

theorem bounded_of_reaches {p k M : ℕ} {z : Params} (hz : ParamBound p k M z) {a : Action}
    (reach : Reaches (start z) a) : ActionBound p k M a :=
  bounded_along (start_bounded hz) reach

/-- Physical input rows written in finite coordinate order satisfy the invariant
immediately, including the empty-dimensional case. -/
theorem bounded_square_params {p k B : ℕ} (R : Fin p → Fin p → ℤ)
    (h : ∀ i j, (R i j).natAbs ≤ 2^B) :
    ParamBound p k (2^B) ((p,k),List.ofFn fun i => List.ofFn (R i)) := by
  refine ⟨le_rfl,le_rfl,⟨by simp,?_⟩⟩
  intro r hr
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
  refine ⟨by simp,?_⟩
  intro v hv
  obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hv
  exact h i j

end Probe
end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
