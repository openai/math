import OAI.Optimization.LinearProgramming.FieldTransfer.ProxyPackingPrimitives
import OAI.Optimization.LinearProgramming.FieldTransfer.ProxyPackingLayout
import Mathlib.Data.Nat.Size
import Mathlib.Tactic.Positivity.Basic

/-! One input row of the compacted symbolic operand tape. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace ProxyPacking

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def scanRow : Block :=
  .seq (.op (.addrLoad 51 72)) (.seq (.branch (.addrLT 62 51) emitRow .skip) advance)

structure Scanned (m t : Memory K) (picked : Bool) : Prop where
  magCursor : t.index 71 = m.index 71 + 1
  flagCursor : t.index 72 = m.index 72 + 1
  rowCursor : t.index 73 = m.index 73 + 1
  count : t.index 50 = m.index 50 + picked.toNat
  bases : t.index 74 = m.index 74 + picked.toNat
  exponents : t.index 75 = m.index 75 + picked.toNat
  base : picked=true → t.data (m.index 74) = m.data (m.index 71)
  exponent : picked=true → t.data (m.index 75) = m.data 23 * m.data (m.index 73)
  dataFrame : ∀ i, i ≠ 20 → i ≠ 21 → i ≠ 22 → (picked=true → i ≠ m.index 74) →
    (picked=true → i ≠ m.index 75) → t.data i=m.data i
  indexFrame : ∀ i, i ≠ 50 → i ≠ 51 → i ≠ 71 → i ≠ 72 → i ≠ 73 → i ≠ 74 →
    i ≠ 75 → t.index i=m.index i

theorem scanRow_correct (m : Memory K) {P : K → Prop} (hm : m.AllData P)
    (picked : Bool) (flag : m.index (m.index 72) = picked.toNat) (zero : m.index 62 = 0)
    (hr : 128 ≤ m.index 73) (hb : 128 ≤ m.index 74) (he : 128 ≤ m.index 75)
    (hne : m.index 74 ≠ m.index 75)
    (hp : picked=true → P (m.data 23 * m.data (m.index 73))) :
    ∃ t c, c ≤ 14 ∧ Block.Eval (Memory.AllData P) scanRow m c t ∧ Scanned m t picked := by
  let q := m.putIndex 51 (m.index (m.index 72))
  have hq : q.AllData P := hm
  have e₀ := Block.Eval.op_addrLoad m 51 72 hm hq
  cases picked with
  | false =>
    have guard : (Cond.addrLT 62 51).test q = false := by simp [Cond.test,q,zero,flag]
    obtain ⟨t,ea,hdat,h71,h72,h73,hindex⟩ := advance_correct q hq
    refine ⟨t,5,by decide,e₀.seq ((Block.Eval.branchFalse (k:=0) guard (.skip hq)).seq ea),
      ?_,?_,?_,?_,?_,?_,by simp,by simp,?_,?_⟩
    · simpa [q] using h71
    · simpa [q] using h72
    · simpa [q] using h73
    · simpa [q] using hindex 50 (by decide) (by decide) (by decide)
    · simpa [q] using hindex 74 (by decide) (by decide) (by decide)
    · simpa [q] using hindex 75 (by decide) (by decide) (by decide)
    · intro i _ _ _ _ _
      exact congrFun hdat i
    · intro i _ h51 ha hb' hc _ _
      simpa [q,h51] using hindex i ha hb' hc
  | true =>
    have guard : (Cond.addrLT 62 51).test q = true := by simp [Cond.test,q,zero,flag]
    obtain ⟨u,eu,post⟩ := emitRow_correct q hq
      (by simpa [q] using hr) (by simpa [q] using hb) (by simpa [q] using he)
      (by simpa [q] using hne) (by simpa [q] using hp rfl)
    obtain ⟨t,ea,hdat,h71,h72,h73,hindex⟩ := advance_correct u eu.safe_end
    have unchanged (i : Nat) (h50 : i ≠ 50) (h51 : i ≠ 51) (h74 : i ≠ 74) (h75 : i ≠ 75) :
        u.index i = m.index i := by simpa [q,h51] using post.indexFrame i h50 h74 h75
    refine ⟨t,14,le_rfl,e₀.seq ((Block.Eval.branchTrue guard eu).seq ea),?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · rw [h71,unchanged 71 (by decide) (by decide) (by decide) (by decide)]
    · rw [h72,unchanged 72 (by decide) (by decide) (by decide) (by decide)]
    · rw [h73,unchanged 73 (by decide) (by decide) (by decide) (by decide)]
    · simpa [q] using (hindex 50 (by decide) (by decide) (by decide)).trans post.count
    · simpa [q] using (hindex 74 (by decide) (by decide) (by decide)).trans post.bases
    · simpa [q] using (hindex 75 (by decide) (by decide) (by decide)).trans post.exponents
    · intro _
      rw [hdat]
      simpa [q] using post.base
    · intro _
      rw [hdat]
      simpa [q] using post.exponent
    · intro i h20 h21 h22 h74 h75
      rw [hdat]
      exact post.dataFrame i h20 h21 h22 (by simpa [q] using h74 rfl) (by simpa [q] using h75 rfl)
    · intro i h50 h51 ha hb' hc h74 h75
      exact (hindex _ ha hb' hc).trans (unchanged i h50 h51 h74 h75)

end ProxyPacking
end FieldTransfer
end LinearProgramming
end Optimization
end OAI

/-! One full iteration of the filtered operand scan, including the exact prefix order. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace ProxyPacking

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem scan_iter {l : Layout} {m s : Memory K} {P : K → Prop} {pick : Nat → Bool}
    {mag : Nat → K} {a : Nat → ℤ} {offset : ℤ} {D j : Nat}
    (hl : l.Valid) (input : Inputs l m pick mag a offset D) (hj : j < l.n)
    (stepSafe : pick j=true → P (((D:ℤ)*a j:ℤ):K))
    (cur : Stage l m P D (operandPrefix pick mag a offset D j) j s) :
    ∃ t k, k ≤ 14 ∧ Block.Eval (Memory.AllData P) scanRow s k t ∧
      Stage l m P D (operandPrefix pick mag a offset D (j+1)) (j+1)
        (t.putIndex 70 (t.index 70+1)) := by
  let ps := operandPrefix pick mag a offset D j
  let next := ps ++ (if pick j then [(mag j,(D:ℤ)*a j)] else [])
  have hlen : ps.length ≤ j+1 := operandPrefix_length ..
  have ln : next.length = ps.length+(pick j).toNat := by cases h : pick j <;> simp [next,h]
  have magHigh := hl.magHigh
  have flagHigh := hl.flagsHigh
  have rowHigh := hl.rowHigh
  have baseHigh := hl.baseHigh
  have expHigh := hl.expHigh
  have readMag : s.data (s.index 71) = mag j := by
    rw [cur.magCursor,cur.dataFrame _ (by omega)
      (fun k hk => hl.magBase.ne hj (by change k < ps.length at hk; omega))
      (fun k hk => hl.magExp.ne hj (by change k < ps.length at hk; omega))]
    exact input.magnitude j hj
  have readRow : s.data (s.index 73) = (a j:K) := by
    rw [cur.rowCursor,cur.dataFrame _ (by omega)
      (fun k hk => hl.rowBase.ne hj (by change k < ps.length at hk; omega))
      (fun k hk => hl.rowExp.ne hj (by change k < ps.length at hk; omega))]
    exact input.coefficient j hj
  have prodval : s.data 23 * s.data (s.index 73) = (((D:ℤ)*a j:ℤ):K) := by
    rw [cur.scale,readRow]; simp
  have readFlag : s.index (s.index 72) = (pick j).toNat := by
    rw [cur.flagCursor,cur.indexFrame _ (by omega) (by omega),input.selected j hj]
  have hb : s.index 74 = l.bases + ps.length := cur.baseCursor
  have he : s.index 75 = l.exponents + ps.length := cur.expCursor
  obtain ⟨t,k,hk,ex,post⟩ := scanRow_correct s cur.safe (pick j) readFlag
    ((cur.indexFrame 62 (by omega) (by omega)).trans input.zero)
    (by rw [cur.rowCursor];omega) (by rw [hb];omega) (by rw [he];omega)
    (by rw [hb,he];exact hl.outputsApart.ne (by omega) (by omega))
    (fun h => prodval ▸ stepSafe h)
  let z := t.putIndex 70 (t.index 70+1)
  have zi (i : Nat) (hi : i ≠ 70) : z.index i=t.index i := by simp [z,hi]
  have newWords (i : Nat) (hi : i < ps.length) :
      t.data (l.bases+i)=ps[i].1 ∧ t.data (l.exponents+i)=(ps[i].2:K) := by
    have old := cur.contents i hi
    constructor
    · exact (post.dataFrame _ (by omega) (by omega) (by omega)
        (fun _ => by rw [hb];omega) (fun _ => by rw [he];exact hl.outputsApart.ne (by omega) (by omega))).trans old.1
    · exact (post.dataFrame _ (by omega) (by omega) (by omega)
        (fun _ => by rw [hb];exact Ne.symm (hl.outputsApart.ne (by omega) (by omega)))
        (fun _ => by rw [he];omega)).trans old.2
  have copied : Contains l z next := by
    change Contains l t next
    cases hpick : pick j with
    | false =>
      simpa [Contains,next,hpick] using newWords
    | true =>
      have hnext : next = ps ++ [(mag j,(D:ℤ)*a j)] := by simp [next,hpick]
      rw [hnext]
      intro i hi
      by_cases old : i < ps.length
      · simpa only [List.getElem_append_left old] using newWords i old
      · have eqi : i=ps.length := by simp only [List.length_append,List.length_singleton] at hi;omega
        subst i
        have xb := post.base hpick
        have xe := post.exponent hpick
        rw [hb,readMag] at xb
        rw [he,prodval] at xe
        simpa using And.intro xb xe
  refine ⟨t,k,hk,ex,?_⟩
  rw [operandPrefix_succ]
  change Stage l m P D next (j+1) z
  refine ⟨ex.safe_end,?_,?_,?_,?_,?_,?_,?_,?_,copied,?_,?_⟩
  · have h70 := post.indexFrame 70 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)
    simp [z,h70,cur.iter]
  · rw [zi 71 (by decide),post.magCursor,cur.magCursor];omega
  · rw [zi 72 (by decide),post.flagCursor,cur.flagCursor];omega
  · rw [zi 73 (by decide),post.rowCursor,cur.rowCursor];omega
  · rw [zi 74 (by decide),post.bases,hb,ln];omega
  · rw [zi 75 (by decide),post.exponents,he,ln];omega
  · exact (zi 50 (by decide)).trans (post.count.trans ((congrArg (·+(pick j).toNat) cur.count).trans ln.symm))
  · change t.data 23=(D:K)
    exact (post.dataFrame 23 (by decide) (by decide) (by decide)
      (fun _ => by rw [hb];omega) (fun _ => by rw [he];omega)).trans cur.scale
  · intro i hs hbfree hefree
    change t.data i = m.data i
    have gain (h : pick j=true) : ps.length < next.length := by rw [ln,h];simp
    exact (post.dataFrame i (by omega) (by omega) (by omega)
      (fun h => hb ▸ hbfree _ (gain h)) (fun h => he ▸ hefree _ (gain h))).trans
      (cur.dataFrame i hs (fun u hu => hbfree u (by change u < ps.length at hu;omega))
        (fun u hu => hefree u (by change u < ps.length at hu;omega)))
  · intro i h₁ h₂
    exact (zi i (by omega)).trans ((post.indexFrame i (by omega) (by omega) (by omega)
      (by omega) (by omega) (by omega) (by omega)).trans (cur.indexFrame i h₁ h₂))

end ProxyPacking
end FieldTransfer
end LinearProgramming
end Optimization
end OAI

/-! Prepare the cached operand pointers and emit the base-two factor. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace ProxyPacking

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def «initialize» : Block :=
  .seq (.straight [.addrCopy 71 80,.addrCopy 72 82,.addrCopy 73 67,.addrCopy 74 68,
    .addrCopy 75 69,.addrConst 50 0,.load 23 86,.const 20 2,.copy 22 45]) storePair

theorem initialize_correct {l : Layout} {m : Memory K} {P : K → Prop} {pick : Nat → Bool}
    {mag : Nat → K} {a : Nat → ℤ} {offset : ℤ} {D : Nat}
    (hl : l.Valid) (input : Inputs l m pick mag a offset D) (hm : m.AllData P) (h2 : P 2) :
    ∃ u, Block.Eval (Memory.AllData P) «initialize» m 14 u ∧
      Stage l m P D [(2,offset)] 0 (u.putIndex 70 0) := by
  let b₁ := m.putIndex 71 (m.index 80)
  let b₂ := b₁.putIndex 72 (b₁.index 82)
  let b₃ := b₂.putIndex 73 (b₂.index 67)
  let b₄ := b₃.putIndex 74 (b₃.index 68)
  let b₅ := b₄.putIndex 75 (b₄.index 69)
  let b₆ := b₅.putIndex 50 0
  let b₇ := b₆.putData 23 (b₆.data (b₆.index 86))
  let b₈ := b₇.putData 20 (2:K)
  let z := b₈.putData 22 (b₈.data 45)
  have e₁ := Block.Eval.op_addrCopy (safe:=Memory.AllData P) m 71 80 hm hm
  have e₂ := Block.Eval.op_addrCopy (safe:=Memory.AllData P) b₁ 72 82 hm hm
  have e₃ := Block.Eval.op_addrCopy (safe:=Memory.AllData P) b₂ 73 67 hm hm
  have e₄ := Block.Eval.op_addrCopy (safe:=Memory.AllData P) b₃ 74 68 hm hm
  have e₅ := Block.Eval.op_addrCopy (safe:=Memory.AllData P) b₄ 75 69 hm hm
  have e₆ := Block.Eval.op_addrConst (safe:=Memory.AllData P) b₅ 50 0 hm hm
  have h₇ : b₇.AllData P := (show b₆.AllData P from hm).putData _ (hm _)
  have h₈ : b₈.AllData P := h₇.putData _ h2
  have hz : z.AllData P := h₈.putData _ (h₈ _)
  have e₇ := Block.Eval.op_load b₆ 23 86 hm h₇
  have e₈ : Block.Eval (Memory.AllData P) (.op (.const 20 2)) b₇ 1 b₈ := by
    simpa [b₈] using Block.Eval.op_const (safe:=Memory.AllData P) b₇ 20 2 h₇ (by simpa using h₈)
  have ez := Block.Eval.op_copy b₈ 22 45 h₈ hz
  have hb : z.index 74=l.bases := input.bases
  have he : z.index 75=l.exponents := input.exponents
  have hmag : z.index 71=l.magnitudes := input.magnitudes
  have hflag : z.index 72=l.flags := input.flags
  have hrow : z.index 73=l.coefficients := input.row
  have hscale : z.data 23=(D:K) := input.scale
  have hoff : z.data 22=(offset:K) := input.constant
  have hbase := hl.baseHigh
  have hexp := hl.expHigh
  obtain ⟨u,ep,post⟩ := storePair_correct z hz (hb ▸ hbase) (he ▸ hexp) (by
    rw [hb,he]
    simpa using hl.outputsApart.ne (i:=0) (j:=0) (Nat.zero_lt_succ _) (Nat.zero_lt_succ _))
  have ind (i : Nat) (a₁ : i < 50 ∨ 52 < i) (a₂ : i < 70 ∨ 75 < i) : z.index i=m.index i := by
    simp [z,b₈,b₇,b₆,b₅,b₄,b₃,b₂,b₁,show i ≠ 50 by omega,show i ≠ 71 by omega,
      show i ≠ 72 by omega,show i ≠ 73 by omega,show i ≠ 74 by omega,show i ≠ 75 by omega]
  let v := u.putIndex 70 0
  have vi (i : Nat) (h : i ≠ 70) : v.index i = u.index i := by simp [v,h]
  refine ⟨u,(e₁.seq (e₂.seq (e₃.seq (e₄.seq (e₅.seq (e₆.seq (e₇.seq (e₈.seq
    (ez.seq (.skip hz)))))))))).seq ep,?_⟩
  change Stage l m P D [(2,offset)] 0 v
  refine ⟨ep.safe_end,by simp [v],?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa using (vi 71 (by decide)).trans ((post.indexFrame 71 (by decide) (by decide) (by decide)).trans hmag)
  · simpa using (vi 72 (by decide)).trans ((post.indexFrame 72 (by decide) (by decide) (by decide)).trans hflag)
  · simpa using (vi 73 (by decide)).trans ((post.indexFrame 73 (by decide) (by decide) (by decide)).trans hrow)
  · simpa [hb] using (vi 74 (by decide)).trans post.bases
  · simpa [he] using (vi 75 (by decide)).trans post.exponents
  · simpa [z,b₈,b₇,b₆] using (vi 50 (by decide)).trans post.count
  · exact (post.dataFrame 23 (by decide) (by decide) (by decide)
      (by rw [hb];omega) (by rw [he];omega)).trans hscale
  · intro i hi
    have eqi : i=0 := by simpa using hi
    subst i
    have bx := post.base
    have ex := post.exponent
    rw [hb] at bx
    rw [he,hoff] at ex
    simpa [v,z,b₈] using And.intro bx ex
  · intro i hstat hf hg
    have fn₁ : i ≠ z.index 74 := by rw [hb];simpa using hf 0 (by simp)
    have fn₂ : i ≠ z.index 75 := by rw [he];simpa using hg 0 (by simp)
    change u.data i=m.data i
    rw [post.dataFrame i (by omega) (by omega) (by omega) fn₁ fn₂]
    simp [z,b₈,b₇,b₆,b₅,b₄,b₃,b₂,b₁,show i ≠ 22 by omega,show i ≠ 20 by omega,show i ≠ 23 by omega]
  · intro i hstat hctrl
    exact (vi i (by omega)).trans ((post.indexFrame i (by omega) (by omega) (by omega)).trans (ind i hstat hctrl))

end ProxyPacking
end FieldTransfer
end LinearProgramming
end Optimization
end OAI

/-! Compact the symbolic product operands from cached flags and a live affine query row.
Every branch, scalar multiplication, and pointer increment belongs to one fixed block. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace FieldTransfer
namespace ProxyPacking

open RAM

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def compactOperands : Block :=
  .seq «initialize» (.seq (.forRange 70 83 scanRow) (.straight [.addrCopy 51 68,.addrCopy 52 69]))

structure Packed (l : Layout) (orig t : Memory K) (ps : List (K × ℤ)) : Prop where
  count : t.index 50 = ps.length
  bases : t.index 51 = l.bases
  exponents : t.index 52 = l.exponents
  contents : Contains l t ps
  dataFrame : ∀ i, (i < 20 ∨ 23 < i) → (∀ k < ps.length, i ≠ l.bases+k) →
    (∀ k < ps.length, i ≠ l.exponents+k) → t.data i=orig.data i
  indexFrame : ∀ i, (i < 50 ∨ 52 < i) → (i < 70 ∨ 75 < i) → t.index i=orig.index i

/-- On arbitrary ordered-field magnitudes the scan emits the base-two offset first,
then precisely the flagged powers in source order. The result is ready for the
integer-scalar exponent serializer and the native base-array packer. -/
theorem compactOperands_correct {l : Layout} {m : Memory K} {P : K → Prop} {pick : Nat → Bool}
    {mag : Nat → K} {a : Nat → ℤ} {offset : ℤ} {D : Nat}
    (hl : l.Valid) (input : Inputs l m pick mag a offset D) (hm : m.AllData P) (h2 : P 2)
    (hP : ∀ j < l.n, pick j=true → P (((D:ℤ)*a j:ℤ):K)) :
    ∃ t k, k ≤ 17*l.n+18 ∧ Block.Eval (Memory.AllData P) compactOperands m k t ∧
      Packed l m t (operandPrefix pick mag a offset D l.n) := by
  obtain ⟨u,init,initial⟩ := initialize_correct hl input hm h2
  let I (j : Nat) := Stage l m P D (operandPrefix pick mag a offset D j) j
  have h₀ : I 0 (u.putIndex 70 0) := initial
  obtain ⟨v,k,hk,run,done⟩ := Block.Eval.forRange_invariant (safe:=Memory.AllData P)
    (body:=scanRow) 70 83 l.n 14 I u init.safe_end h₀
    (fun _ _ cur => ⟨cur.safe,cur.iter,(cur.indexFrame 83 (by omega) (by omega)).trans input.size⟩)
    (fun j hj s cur => scan_iter hl input hj (hP j hj) cur)
  let y := v.putIndex 51 (v.index 68)
  let t := y.putIndex 52 (y.index 69)
  have ey := Block.Eval.op_addrCopy (safe:=Memory.AllData P) v 51 68 done.safe done.safe
  have et := Block.Eval.op_addrCopy (safe:=Memory.AllData P) y 52 69 done.safe done.safe
  have pbase := (done.indexFrame 68 (by omega) (by omega)).trans input.bases
  have pexp := (done.indexFrame 69 (by omega) (by omega)).trans input.exponents
  refine ⟨t,14+(k+2),by omega,init.seq (run.seq (ey.seq (et.seq (.skip done.safe)))),
    ?_,?_,?_,done.contents,done.dataFrame,?_⟩
  · simpa [t,y] using done.count
  · simpa [t,y] using pbase
  · simpa [t,y] using pexp
  · intro i hstat hctrl
    simpa [t,y,show i ≠ 51 by omega,show i ≠ 52 by omega] using done.indexFrame i hstat hctrl

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- Reindex the physical ascending scan by the finite coordinate type used in the
mathematical compression argument. -/
theorem finite_operandPrefix (n : Nat) (pick : Nat → Bool) (mag : Nat → K)
    (a : Nat → ℤ) (offset : ℤ) (D : Nat) :
    operandPrefix pick mag a offset D n =
      (2,offset) :: ((List.finRange n).filter fun i => pick i.val).map
        (fun i => (mag i.val,(D:ℤ)*a i.val)) := by
  have allRows : (List.finRange n).map Fin.val = List.range n := by
    apply List.ext_getElem <;> simp
  unfold operandPrefix
  rw [← allRows,List.filter_map,List.map_map]
  rfl

/-- The actual multiplier writes integer coefficients whose bit widths add. -/
theorem scaledCoefficient_size (D w : Nat) (a : ℤ) (hw : a.natAbs.size ≤ w) :
    ((D:ℤ)*a).natAbs.size ≤ D.size+w := by
  apply Nat.size_le.mpr
  simpa only [Int.natAbs_mul,Int.natAbs_natCast,pow_add] using
    (Nat.mul_le_mul_left D (Nat.size_le.mp hw).le).trans_lt
      (Nat.mul_lt_mul_of_pos_right (Nat.lt_size_self D) (show 0 < 2^w by positivity))

omit [LinearOrder K] [IsStrictOrderedRing K] in
/-- One width accounts for the leading constant exponent and every emitted
coefficient. It supplies the actual serializer precondition for the compacted array. -/
theorem operandPrefix_width (pick : Nat → Bool) (mag : Nat → K) (a : Nat → ℤ)
    (offset : ℤ) (D n w : Nat) (coeff : ∀ j < n, pick j=true → (a j).natAbs.size ≤ w)
    {e : ℤ} (he : e ∈ (operandPrefix pick mag a offset D n).map Prod.snd) :
    e.natAbs < 2^(max offset.natAbs.size (D.size+w)) := by
  apply Nat.size_le.mp
  obtain ⟨p,hp,rfl⟩ := List.mem_map.mp he
  rcases List.mem_cons.mp hp with rfl | hx
  · exact Nat.le_max_left ..
  · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp hx
    obtain ⟨hindex,hflag⟩ := List.mem_filter.mp hi
    exact (scaledCoefficient_size D w (a i) (coeff i (List.mem_range.mp hindex) hflag)).trans (Nat.le_max_right ..)

end ProxyPacking
end FieldTransfer
end LinearProgramming
end Optimization
end OAI
