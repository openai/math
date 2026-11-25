import OAI.Optimization.LinearProgramming.Compression.PowerTapeEncoder
import OAI.Optimization.LinearProgramming.RAM.Array

/-! Scan consecutive integer scalar exponents and materialize their concatenated literal
signed bits. The single-word emitter is called once per input, on reusable digit scratch. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open OAI.Optimization.LinearProgramming.RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The single-word routine's interface, including its exact frame outside temporary
registers, scratch digits, and the appended token interval. -/
def PowerTokenEmitterSpec (word : Block) (w : ℕ) (P : K → Prop) : Prop :=
  ∀ (m : Memory K) (x : ℤ) (base out : ℕ), m.AllData P → m.data 0 = (x : K) →
    m.index 2 = base → m.index 34 = out → 41 < base → 42 < out → x.natAbs < 2^w →
    ∃ s k, k ≤ w*(16*w+32)+32 ∧ Block.Eval (Memory.AllData P) word m k s ∧
      s.index 2 = base ∧ s.index 34 = out + (exponentTokens x).length ∧
      (∀ i : Fin (exponentTokens x).length, s.index (out+i.val) = ((exponentTokens x)[i.val]).code) ∧
      (∀ i, 6 ≤ i → i ≠ 40 → i ≠ 41 → (i < base ∨ base+w ≤ i) → s.data i = m.data i) ∧
      (∀ i, 3 < i → i ≠ 34 → i ≠ 37 → i ≠ 39 → i ≠ 42 →
        (i < out ∨ out+(exponentTokens x).length ≤ i) → s.index i = m.index i)

private def exponentPackingBody (word : Block) : Block :=
  .seq (.op (.load 0 52)) (.seq (.op (.incr 52 52)) (.seq word (.op (.incr 54 54))))

/-- Address 50 holds the row count, 52 points at its first scalar exponent, 34 at
the output, and 2 at the reusable digit workspace. Address 54 is the loop counter. -/
def packPowerExponentsBlock (word : Block) : Block :=
  .seq (.op (.addrConst 54 0)) (.loop (.addrLT 54 50) (exponentPackingBody word))

/-- Exact products of one or more emitter calls. Bounds deliberately describe all
unaffected addresses, so the caller can store its sources and work pages beside them. -/
structure PowerExponentPost (w base src out row count : ℕ) (es : List ℤ)
    (m s : Memory K) : Prop where
  scratch : s.index 2 = base
  limit : s.index 50 = count
  rowCursor : s.index 54 = row + es.length
  exponentCursor : s.index 52 = src + es.length
  tokenCursor : s.index 34 = out + (signedBitTape es).length
  tokens : ∀ i, ∀ hi : i < (signedBitTape es).length,
    s.index (out+i) = ((signedBitTape es)[i]).code
  dataFrame : ∀ i, 6 ≤ i → i ≠ 40 → i ≠ 41 → (i < base ∨ base+w ≤ i) → s.data i = m.data i
  indexFrame : ∀ i, 3 < i → i ≠ 34 → i ≠ 37 → i ≠ 39 → i ≠ 42 → i ≠ 52 → i ≠ 54 →
    (i < out ∨ out + (signedBitTape es).length ≤ i) → s.index i = m.index i

private theorem signed_append (xs ys : List ℤ) :
    signedBitTape (xs++ys) = signedBitTape xs ++ signedBitTape ys := by simp [signedBitTape]

private theorem signed_single (x : ℤ) : signedBitTape [x] = exponentTokens x := by simp [signedBitTape]

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem PowerExponentPost.append {w base src out row count : ℕ} {xs ys : List ℤ}
    {m a b : Memory K} (hx : PowerExponentPost w base src out row count xs m a)
    (hy : PowerExponentPost w base (src+xs.length) (out+(signedBitTape xs).length)
      (row+xs.length) count ys a b) (hout : 64 ≤ out) :
    PowerExponentPost w base src out row count (xs++ys) m b := by
  refine ⟨hy.scratch,hy.limit,?_,?_,?_,?_,?_,?_⟩
  · simpa only [List.length_append, Nat.add_assoc] using hy.rowCursor
  · simpa only [List.length_append, Nat.add_assoc] using hy.exponentCursor
  · simpa only [signed_append, List.length_append, Nat.add_assoc] using hy.tokenCursor
  · simp only [signed_append]
    intro i hi
    by_cases h : i < (signedBitTape xs).length
    · rw [List.getElem_append_left h]
      exact (hy.indexFrame _ (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (Or.inl (by omega))).trans (hx.tokens i h)
    · have hh : i - (signedBitTape xs).length < (signedBitTape ys).length := by
        simp only [List.length_append] at hi
        omega
      have he : out + (signedBitTape xs).length + (i-(signedBitTape xs).length) = out+i := by omega
      rw [List.getElem_append_right (by omega)]
      simpa only [he] using hy.tokens (i-(signedBitTape xs).length) hh
  · intro j hj h40 h41 hfree
    exact (hy.dataFrame j hj h40 h41 hfree).trans (hx.dataFrame j hj h40 h41 hfree)
  · intro j hj h34 h37 h39 h42 h52 h54 hfree
    simp only [signed_append,List.length_append] at hfree
    exact (hy.indexFrame j hj h34 h37 h39 h42 h52 h54 (by omega)).trans
      (hx.indexFrame j hj h34 h37 h39 h42 h52 h54 (by omega))

private theorem one_exponent {word : Block} {w base src out row count : ℕ} {P : K → Prop}
    (spec : PowerTokenEmitterSpec word w P) (m : Memory K) (x : ℤ) (hm : m.AllData P)
    (hx : m.data src = (x : K)) (hw : x.natAbs < 2^w) (hb : 41 < base) (ho : 64 ≤ out)
    (h2 : m.index 2 = base) (h34 : m.index 34 = out) (h50 : m.index 50 = count)
    (h52 : m.index 52 = src) (h54 : m.index 54 = row) :
    ∃ s k, k ≤ w*(16*w+32)+35 ∧ Block.Eval (Memory.AllData P) (exponentPackingBody word) m k s ∧
      PowerExponentPost w base src out row count [x] m s := by
  let a := m.putData 0 (m.data (m.index 52))
  let b := a.putIndex 52 (src+1)
  have ha : a.AllData P := hm.putData 0 (hm _)
  have hb' : b.AllData P := ha
  have ea : Block.Eval (Memory.AllData P) (.op (.load 0 52)) m 1 a :=
    Block.Eval.op_load _ _ _ hm ha
  have eb : Block.Eval (Memory.AllData P) (.op (.incr 52 52)) a 1 b := by
    simpa only [a, b, Memory.putData, h52] using Block.Eval.op_incr (safe := Memory.AllData P)
      a 52 52 ha (ha.putIndex 52 (a.index 52+1))
  have bx : b.data 0 = (x : K) := by simp [a,b,h52,hx]
  have bin (i : ℕ) (hi : i ≠ 52) : b.index i = m.index i := by simp [a,b,hi]
  obtain ⟨t,k,hk,ex,t2,t34,tok,df,ifr⟩ := spec b x base out hb' bx
    ((bin 2 (by decide)).trans h2) ((bin 34 (by decide)).trans h34) hb (by omega) hw
  have known (i : ℕ) (hi : 3 < i) (h034 : i ≠ 34) (h037 : i ≠ 37) (h039 : i ≠ 39)
      (h042 : i ≠ 42) (hlo : i < out) : t.index i = b.index i :=
    ifr i hi h034 h037 h039 h042 (Or.inl hlo)
  have trow : t.index 54 = row :=
    (known 54 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)).trans
      ((bin 54 (by decide)).trans h54)
  let v := t.putIndex 54 (t.index 54+1)
  have ev : Block.Eval (Memory.AllData P) (.op (.incr 54 54)) t 1 v :=
    Block.Eval.op_incr _ _ _ ex.safe_end ex.safe_end
  have vind (i : ℕ) (hi : i ≠ 54) : v.index i = t.index i := by simp [v,hi]
  refine ⟨v,1+(1+(k+1)),by omega,ea.seq (eb.seq (ex.seq ev)),?_⟩
  refine ⟨(vind 2 (by decide)).trans t2,?_,?_,?_,?_,?_,?_,?_⟩
  · exact (vind 50 (by decide)).trans ((known 50 (by decide) (by decide) (by decide) (by decide)
      (by decide) (by omega)).trans ((bin 50 (by decide)).trans h50))
  · simp [v,trow]
  · have h := known 52 (by decide) (by decide) (by decide) (by decide) (by decide) (by omega)
    rw [vind 52 (by decide),h]
    simp [b]
  · simpa only [signed_single] using (vind 34 (by decide)).trans t34
  · simp only [signed_single]
    intro i hi
    exact (vind _ (by omega)).trans (tok ⟨i,hi⟩)
  · intro i hi h40 h41 hfree
    change t.data i = m.data i
    rw [df i hi h40 h41 hfree]
    simp [b,a,show i ≠ 0 by omega]
  · intro i hi h034 h037 h039 h042 h052 h054 hfree
    rw [signed_single] at hfree
    exact (vind i h054).trans ((ifr i hi h034 h037 h039 h042 hfree).trans (bin i h052))


private theorem exponent_loop {word : Block} {P : K → Prop} {w : ℕ}
    (spec : PowerTokenEmitterSpec word w P) (es : List ℤ) (m : Memory K)
    (base src out row count : ℕ) (hm : m.AllData P) (hrange : row+es.length=count)
    (hb : 41 < base) (hs : 64 ≤ src) (ho : 64 ≤ out)
    (hsep : src+es.length ≤ base ∨ base+w ≤ src)
    (h2 : m.index 2=base) (h34 : m.index 34=out) (h50 : m.index 50=count)
    (h52 : m.index 52=src) (h54 : m.index 54=row)
    (values : ∀ i, ∀ hi : i < es.length, m.data (src+i) = (es[i] : K))
    (width : ∀ x ∈ es, x.natAbs < 2^w) :
    ∃ s time, time ≤ (w*(16*w+32)+37)*es.length+1 ∧
      Block.Eval (Memory.AllData P) (.loop (.addrLT 54 50) (exponentPackingBody word)) m time s ∧
      PowerExponentPost w base src out row count es m s := by
  induction es generalizing m src out row with
  | nil =>
    have he : row = count := by simpa using hrange
    have guard : (Cond.addrLT 54 50).test m = false := by simp [Cond.test,h54,h50,he]
    refine ⟨m,1,by simp,.loopFalse guard hm,h2,h50,?_,?_,?_,?_,?_,?_⟩
    · simpa using h54
    · simpa using h52
    · simpa [signedBitTape] using h34
    · simp [signedBitTape]
    · intros; rfl
    · intros; rfl
  | cons x xs ih =>
    have hx : m.data src = (x : K) := by
      have eqn := values 0 (by simp)
      change m.data (src+0) = (x : K) at eqn
      simpa using eqn
    obtain ⟨t,c,hc,one,hfirst⟩ := one_exponent spec m x hm hx (width x (by simp))
      hb ho h2 h34 h50 h52 h54
    have ht (j : ℕ) (hj : j < xs.length) : t.data (src+1+j) = (xs[j] : K) := by
      rw [hfirst.dataFrame _ (by omega) (by omega) (by omega) (by
        simp only [List.length_cons] at hsep
        omega)]
      have eqn := values (j+1) (by simpa using hj)
      simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using eqn
    have hse : src+1+xs.length ≤ base ∨ base+w ≤ src+1 := by
      simp only [List.length_cons] at hsep
      omega
    obtain ⟨s,k,hk,rest,hlast⟩ := ih t (src+1) (out+(signedBitTape [x]).length) (row+1)
      one.safe_end (by simp only [List.length_cons] at hrange; omega)
      (by omega) (by omega) hse hfirst.scratch hfirst.tokenCursor hfirst.limit
      hfirst.exponentCursor hfirst.rowCursor ht (fun y hy => width y (by simp [hy]))
    have guard : (Cond.addrLT 54 50).test m = true := by
      have hlt : row<count := by simp only [List.length_cons] at hrange; omega
      simp [Cond.test,h54,h50,hlt]
    refine ⟨s,1+c+1+k,?_,.loopTrue guard one rest,?_⟩
    · let W := w*(16*w+32)+37
      change 1+c+1+k ≤ W*(xs.length+1)+1
      rw [Nat.mul_succ W xs.length]
      change k ≤ W*xs.length+1 at hk
      have hcost : 1+c+1 ≤ W := by dsimp [W]; omega
      omega
    · exact hfirst.append hlast ho


/-- The exponent-only scan is independent of the bases. Its source array and remote
caller cells survive. A caller can therefore isolate the rational exponent pass and
retain arbitrary ordered-field bases until the scalar-tape copy. -/
theorem packPowerExponentsBlock_spec {word : Block} {P : K → Prop} {w : ℕ}
    (spec : PowerTokenEmitterSpec word w P) (es : List ℤ) (m : Memory K)
    (base src out : ℕ) (hm : m.AllData P) (hb : 41 < base) (hs : 64 ≤ src) (ho : 64 ≤ out)
    (hsep : src+es.length ≤ base ∨ base+w ≤ src) (h2 : m.index 2=base)
    (h34 : m.index 34=out) (h50 : m.index 50=es.length) (h52 : m.index 52=src)
    (values : ∀ i, ∀ hi : i < es.length, m.data (src+i) = (es[i] : K))
    (width : ∀ x ∈ es, x.natAbs < 2^w) :
    ∃ s time, time ≤ (w*(16*w+32)+37)*es.length+2 ∧
      Block.Eval (Memory.AllData P) (packPowerExponentsBlock word) m time s ∧
      PowerExponentPost w base src out 0 es.length es m s := by
  let start := m.putIndex 54 0
  have hs' : start.AllData P := hm
  have hinit : Block.Eval (Memory.AllData P) (.op (.addrConst 54 0)) m 1 start :=
    Block.Eval.op_addrConst _ _ _ hm hs'
  obtain ⟨s,k,hk,run,post⟩ := exponent_loop spec es start base src out 0 es.length hs' (by simp)
    hb hs ho hsep (by simpa [start] using h2) (by simpa [start] using h34)
    (by simpa [start] using h50) (by simpa [start] using h52) (by simp [start]) values width
  refine ⟨s,1+k,by omega,hinit.seq run, { post with indexFrame := ?_ }⟩
  intro i hi h034 h037 h039 h042 h052 h054 hfree
  simpa [start,h054] using post.indexFrame i hi h034 h037 h039 h042 h052 h054 hfree
