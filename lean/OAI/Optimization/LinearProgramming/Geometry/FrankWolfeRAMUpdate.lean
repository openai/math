import OAI.Optimization.LinearProgramming.RAM.Loops
import Mathlib.Data.Rat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! In-place Frank–Wolfe coordinate update on rational or ordered-field RAM registers. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM RAM.Block

universe u
variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- At a negative gradient the minimizing corner is one. Otherwise only the distinguished
coordinate has a nonzero lower endpoint. -/
def cellCorner (target j : Nat) (g : K) : K :=
  if g < 0 then 1 else if j = target then 1/4 else 0

def cellValue (target j : Nat) (a g z : K) : K :=
  z + a * (cellCorner target j g - z)

/-- Select the corner in scalar register 3, with the gradient in 2 and zero in 0. -/
def cornerBlock : Block :=
  .branch (.scalarLT 2 0) (.op (.const 3 1))
    (.branch (.addrLT 30 29) (.op (.const 3 0))
      (.branch (.addrLT 29 30) (.op (.const 3 0)) (.op (.const 3 (1/4)))))

def updateBody : Block :=
  .seq (.op (.load 1 31)) <| .seq (.op (.load 2 32)) <| .seq cornerBlock <|
    .straight [.sub 4 3 1, .mul 4 10 4, .add 4 1 4, .store 31 4, .incr 31 31, .incr 32 32]

/-- Address registers 25, 28, 23, and 29 hold the start of `z`, the start of `g`,
the dimension, and the target. Scalar register 10 holds the step size. The block changes
only scalar scratch registers 0–4, the array `z`, and address registers 30–32. -/
def updateBlock : Block :=
  .seq (.op (.const 0 0)) <| .seq (.op (.addrCopy 31 25)) <|
    .seq (.op (.addrCopy 32 28)) (.forRange 30 23 updateBody)

private abbrev Safe (P : K → Prop) (s : Memory K) := ∀ r, P (s.data r)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
private theorem safe_data {P : K → Prop} {s : Memory K} (hs : Safe P s)
    (dst : Nat) {v : K} (hv : P v) : Safe P (s.putData dst v) := by
  intro r
  by_cases h : r = dst
  · simpa [h] using hv
  · simpa [h] using hs r

private theorem corner_eval (s : Memory K) (P : K → Prop) (hs : Safe P s)
    (hzero : s.data 0 = 0) (p0 : P 0) (p1 : P 1) (pquarter : P (1/4)) :
    let v := cellCorner (s.index 29) (s.index 30) (s.data 2)
    ∃ k ≤ 5, Eval (Safe P) cornerBlock s k (s.putData 3 v) := by
  dsimp only
  unfold cornerBlock
  by_cases hg : s.data 2 < 0
  · have run := Eval.op_const s 3 (1 : ℚ) hs (by simpa using safe_data hs 3 p1)
    refine ⟨3, by decide, ?_⟩
    apply Eval.branchTrue (k := 1) (c := .scalarLT 2 0) (by simp [Cond.test,hzero,hg])
    simpa [cellCorner,hg] using run
  · have guard : (Cond.scalarLT 2 0).test s = false := by simp [Cond.test,hzero,hg]
    by_cases hlt : s.index 30 < s.index 29
    · have run := Eval.op_const s 3 (0 : ℚ) hs (by simpa using safe_data hs 3 p0)
      refine ⟨4, by decide, Eval.branchFalse (k := 3) guard ?_⟩
      apply Eval.branchTrue (k := 1) (c := .addrLT 30 29) (by simp [Cond.test,hlt])
      simpa [cellCorner,hg,Nat.ne_of_lt hlt] using run
    · have left : (Cond.addrLT 30 29).test s = false := by simp [Cond.test,hlt]
      by_cases hgt : s.index 29 < s.index 30
      · have run := Eval.op_const s 3 (0 : ℚ) hs (by simpa using safe_data hs 3 p0)
        refine ⟨5, by decide, Eval.branchFalse (k := 4) guard (Eval.branchFalse (k := 3) left ?_)⟩
        apply Eval.branchTrue (k := 1) (c := .addrLT 29 30) (by simp [Cond.test,hgt])
        simpa [cellCorner,hg,Nat.ne_of_gt hgt] using run
      · have eq : s.index 30 = s.index 29 := by omega
        have run := Eval.op_const s 3 (1/4 : ℚ) hs (by simpa using safe_data hs 3 pquarter)
        refine ⟨4, by decide, Eval.branchFalse (k := 3) guard (Eval.branchFalse (k := 2) left ?_)⟩
        apply Eval.branchFalse (k := 1) (c := .addrLT 29 30) (by simp [Cond.test,hgt])
        simpa [cellCorner,hg,eq] using run

private def next (m : Memory K) (j : Nat) : K :=
  cellValue (m.index 29) j (m.data 10) (m.data (m.index 28+j)) (m.data (m.index 25+j))

private structure Inv (P : K → Prop) (m : Memory K) (j : Nat) (s : Memory K) : Prop where
  safe : Safe P s
  counter : s.index 30 = j
  zptr : s.index 31 = m.index 25 + j
  gptr : s.index 32 = m.index 28 + j
  addrs : ∀ r, r ≠ 30 → r ≠ 31 → r ≠ 32 → s.index r = m.index r
  zero : s.data 0 = 0
  stepSize : s.data 10 = m.data 10
  cells : ∀ r, 5 ≤ r → s.data r =
    if m.index 25 ≤ r ∧ r < m.index 25+j then next m (r-m.index 25) else m.data r

private theorem body_eval (m : Memory K) (P : K → Prop) (p0 : P 0) (p1 : P 1)
    (pquarter : P (1/4)) (hzbase : 11 ≤ m.index 25) (hgbase : 11 ≤ m.index 28)
    (hsep : m.index 25+m.index 23 ≤ m.index 28 ∨ m.index 28+m.index 23 ≤ m.index 25)
    (j : Nat) (hj : j < m.index 23) (s : Memory K) (hi : Inv P m j s)
    (hvalues :
      let d := cellCorner (m.index 29) j (m.data (m.index 28+j)) - m.data (m.index 25+j)
      P d ∧ P (m.data 10*d) ∧ P (next m j)) :
    ∃ t k, k ≤ 13 ∧ Eval (Safe P) updateBody s k t ∧
      Inv P m (j+1) (t.putIndex 30 (t.index 30+1)) := by
  let z := m.data (m.index 25+j)
  let g := m.data (m.index 28+j)
  let c := cellCorner (m.index 29) j g
  let d := c-z
  let u := m.data 10*d
  let v := next m j
  have hzz : s.data (s.index 31) = z := by
    rw [hi.zptr, hi.cells _ (by omega)]
    simp [z]
  have hgg : s.data (s.index 32) = g := by
    rw [hi.gptr, hi.cells _ (by omega)]
    have e : ¬ (m.index 25 ≤ m.index 28+j ∧ m.index 28+j < m.index 25+j) := by omega
    split
    · exact (e ‹_›).elim
    · rfl
  obtain ⟨hd,hu,hv⟩ := hvalues
  let s1 := s.putData 1 z
  let s2 := s1.putData 2 g
  let s3 := s2.putData 3 c
  let s4 := s3.putData 4 d
  let s5 := s4.putData 4 u
  let s6 := s5.putData 4 v
  let s7 := s6.putData (m.index 25+j) v
  let s8 := s7.putIndex 31 (m.index 25+j+1)
  let s9 := s8.putIndex 32 (m.index 28+j+1)
  have ps1 : Safe P s1 := safe_data hi.safe 1 (by rw [← hzz]; exact hi.safe _)
  have ps2 : Safe P s2 := safe_data ps1 2 (by rw [← hgg]; exact hi.safe _)
  have t1 : Eval (Safe P) (.op (.load 1 31)) s 1 s1 := by
    change Eval _ _ _ _ (s.putData 1 z)
    rw [← hzz]
    exact Eval.op_load s 1 31 hi.safe (safe_data hi.safe 1 (hi.safe _))
  have hg2 : s1.data (s1.index 32) = g := by
    have ne : s.index 32 ≠ 1 := by rw [hi.gptr]; omega
    simpa [s1,ne] using hgg
  have t2 : Eval (Safe P) (.op (.load 2 32)) s1 1 s2 :=
    by
    change Eval _ _ _ _ (s1.putData 2 g)
    rw [← hg2]
    exact Eval.op_load s1 2 32 ps1 (safe_data ps1 2 (ps1 _))
  have hc : cellCorner (s2.index 29) (s2.index 30) (s2.data 2) = c := by
    simp [c,s2,s1,hi.counter,hi.addrs 29 (by decide) (by decide) (by decide)]
  obtain ⟨k,hk,t3⟩ := corner_eval s2 P ps2 (by simpa [s2,s1] using hi.zero) p0 p1 pquarter
  rw [hc] at t3
  have ps3 : Safe P s3 := t3.safe_end
  have hs4 : s3.data 3 - s3.data 1 = d := by simp [d,s3,s2,s1]
  have ps4 : Safe P s4 := safe_data ps3 4 hd
  have t4 : Eval (Safe P) (.op (.sub 4 3 1)) s3 1 s4 :=
    by
    change Eval _ _ _ _ (s3.putData 4 d)
    rw [← hs4]
    exact Eval.op_sub s3 4 3 1 ps3 (by rw [hs4]; exact ps4)
  have hs5 : s4.data 10 * s4.data 4 = u := by simp [u,s4,s3,s2,s1,hi.stepSize]
  have ps5 : Safe P s5 := safe_data ps4 4 hu
  have t5 : Eval (Safe P) (.op (.mul 4 10 4)) s4 1 s5 :=
    by
    change Eval _ _ _ _ (s4.putData 4 u)
    rw [← hs5]
    exact Eval.op_mul s4 4 10 4 ps4 (by rw [hs5]; exact ps5)
  have hs6 : s5.data 1 + s5.data 4 = v := by simp [v,next,cellValue,u,d,c,z,g,s5,s4,s3,s2,s1]
  have ps6 : Safe P s6 := safe_data ps5 4 hv
  have t6 : Eval (Safe P) (.op (.add 4 1 4)) s5 1 s6 :=
    by
    change Eval _ _ _ _ (s5.putData 4 v)
    rw [← hs6]
    exact Eval.op_add s5 4 1 4 ps5 (by rw [hs6]; exact ps6)
  have ps7 : Safe P s7 := safe_data ps6 _ hv
  have tar : s6.index 31 = m.index 25+j := by simpa [s6,s5,s4,s3,s2,s1] using hi.zptr
  have val : s6.data 4 = v := by simp [s6]
  have t7 : Eval (Safe P) (.op (.store 31 4)) s6 1 s7 := by
    simpa only [tar,val,s7] using Eval.op_store s6 31 4 ps6 (by simpa only [tar,val] using ps7)
  have zaddr : s7.index 31 + 1 = m.index 25+j+1 := by simp [s7,tar]
  have t8 : Eval (Safe P) (.op (.incr 31 31)) s7 1 s8 := by
    simpa only [zaddr,s8] using Eval.op_incr s7 31 31 ps7 ps7
  have gaddr : s8.index 32 + 1 = m.index 28+j+1 := by
    simp [s8,s7,s6,s5,s4,s3,s2,s1,hi.gptr]
  have t9 : Eval (Safe P) (.op (.incr 32 32)) s8 1 s9 := by
    simpa only [gaddr,s9] using Eval.op_incr s8 32 32 t8.safe_end t8.safe_end
  have tail : Eval (Safe P)
      (.straight [.sub 4 3 1,.mul 4 10 4,.add 4 1 4,.store 31 4,.incr 31 31,.incr 32 32])
      s3 6 s9 := t4.seq (t5.seq (t6.seq (t7.seq (t8.seq (t9.seq (.skip t9.safe_end))))))
  refine ⟨s9,1+(1+(k+6)),by omega,t1.seq (t2.seq (t3.seq tail)),?_⟩
  have olddata (r : Nat) (hr : 5 ≤ r) : s6.data r = s.data r := by
    simp [s6,s5,s4,s3,s2,s1,show r ≠ 1 by omega,show r ≠ 2 by omega,
      show r ≠ 3 by omega,show r ≠ 4 by omega]
  refine ⟨t9.safe_end, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [s9,s8,s7,s6,s5,s4,s3,s2,s1,hi.counter]
  · simp [s9,s8,Nat.add_assoc]
  · simp [s9,Nat.add_assoc]
  · intro r r30 r31 r32
    simpa [s9,s8,s7,s6,s5,s4,s3,s2,s1,r30,r31,r32] using hi.addrs r r30 r31 r32
  · simpa [s9,s8,s7,s6,s5,s4,s3,s2,s1, show 0 ≠ m.index 25+j by omega] using hi.zero
  · simpa [s9,s8,s7,s6,s5,s4,s3,s2,s1, show 10 ≠ m.index 25+j by omega] using hi.stepSize
  · intro r hr
    by_cases e : r = m.index 25+j
    · subst r
      simp [s9,s8,s7,v,Nat.add_assoc]
    · have eq : m.index 25 ≤ r ∧ r < m.index 25+(j+1) ↔ m.index 25 ≤ r ∧ r < m.index 25+j := by omega
      simpa [s9,s8,s7,e,olddata r hr,eq] using hi.cells r hr

/-- The fixed RAM block performs one coordinatewise Frank–Wolfe update in place. Bounds on
the three scalar intermediates suffice for a register predicate to hold at every instruction. -/
theorem updateBlock_spec (m : Memory K) (P : K → Prop) (hs : ∀ r, P (m.data r))
    (p0 : P 0) (p1 : P 1) (pquarter : P (1/4))
    (hzbase : 11 ≤ m.index 25) (hgbase : 11 ≤ m.index 28)
    (hsep : m.index 25+m.index 23 ≤ m.index 28 ∨ m.index 28+m.index 23 ≤ m.index 25)
    (hvalues : ∀ j < m.index 23,
      let z := m.data (m.index 25+j)
      let d := cellCorner (m.index 29) j (m.data (m.index 28+j)) - z
      P d ∧ P (m.data 10*d) ∧ P (z+m.data 10*d)) :
    ∃ t k, k ≤ 16*(m.index 23)+5 ∧
      Eval (fun s => ∀ r, P (s.data r)) updateBlock m k t ∧
      (∀ j < m.index 23, t.data (m.index 25+j) =
        cellValue (m.index 29) j (m.data 10) (m.data (m.index 28+j)) (m.data (m.index 25+j))) ∧
      (∀ r, 5 ≤ r → (r < m.index 25 ∨ m.index 25+m.index 23 ≤ r) → t.data r = m.data r) ∧
      (∀ r, r ≠ 30 → r ≠ 31 → r ≠ 32 → t.index r = m.index r) ∧
      t.index 30 = m.index 23 ∧ t.index 31 = m.index 25+m.index 23 ∧
      t.index 32 = m.index 28+m.index 23 := by
  let s0 := m.putData 0 0
  let s1 := s0.putIndex 31 (m.index 25)
  let s2 := s1.putIndex 32 (m.index 28)
  have ps0 : Safe P s0 := safe_data hs 0 p0
  have e0 : Eval (Safe P) (.op (.const 0 0)) m 1 s0 := by
    simpa [s0] using Eval.op_const m 0 0 hs (by simpa using ps0)
  have e1 : Eval (Safe P) (.op (.addrCopy 31 25)) s0 1 s1 :=
    Eval.op_addrCopy s0 31 25 ps0 ps0
  have e2 : Eval (Safe P) (.op (.addrCopy 32 28)) s1 1 s2 := by
    simpa [s2,s1,s0] using Eval.op_addrCopy s1 32 28 ps0 ps0
  have init : Inv P m 0 (s2.putIndex 30 0) := by
    refine ⟨ps0,?_,?_,?_,?_,?_,?_,?_⟩
    · simp
    · simp [s2,s1]
    · simp [s2]
    · intro r h30 h31 h32
      simp [s2,s1,s0,h30,h31,h32]
    · simp [s2,s1,s0]
    · simp [s2,s1,s0]
    · intro r hr
      simp [s2,s1,s0, show r ≠ 0 by omega]
  obtain ⟨t,k,hk,run,last⟩ := Eval.forRange_invariant (safe := Safe P) (body := updateBody)
    30 23 (m.index 23) 13 (Inv P m) s2 ps0 init
    (fun j s h => ⟨h.safe, h.counter, h.addrs 23 (by decide) (by decide) (by decide)⟩)
    (fun j hj s h => body_eval m P p0 p1 pquarter hzbase hgbase hsep j hj s h (hvalues j hj))
  refine ⟨t,1+(1+(1+k)),by omega, e0.seq (e1.seq (e2.seq run)), ?_, ?_,
    last.addrs, last.counter, last.zptr, last.gptr⟩
  · intro j hj
    rw [last.cells _ (by omega)]
    simp [next,hj]
  · intro r hr hout
    rw [last.cells r hr]
    have h : ¬(m.index 25 ≤ r ∧ r < m.index 25+m.index 23) := by omega
    simp [h]

/-- A register-width envelope for one rational coordinate update. `A` and `Z`
bound the reduced denominators of the step and the incoming coordinate. -/
def updateWidth (A Z : Nat) : Nat := 3 + 2 * (4 * (A+1) * (Z+1)^2)

theorem ratBits_of_unit {q : ℚ} {D : Nat} (ha : |q| ≤ 1) (hd : q.den ≤ D) :
    RAM.ratBits q ≤ 3 + 2*D := by
  obtain ⟨h₀,h₁⟩ := abs_le.mp ha
  have l : -(q.den : ℤ) ≤ q.num := by simpa using (Rat.le_iff _ _).mp h₀
  have u : q.num ≤ (q.den : ℤ) := by simpa using (Rat.le_iff _ _).mp h₁
  have hn : q.num.natAbs ≤ q.den := by omega
  have hnum := Nat.log2_le_self q.num.natAbs
  have hden := Nat.log2_le_self q.den
  unfold RAM.ratBits
  omega

private theorem corner_box (target j : Nat) (g : K) : 0 ≤ cellCorner target j g ∧
    cellCorner target j g ≤ 1 := by
  unfold cellCorner
  split
  · simp
  · split <;> norm_num

theorem quarter_den_le : (1/4:ℚ).den ≤ 4 := by
  have h : (Rat.divInt 1 4).den ∣ (4 : ℕ) := by exact_mod_cast Rat.den_dvd 1 4
  have e : (1 / 4 : ℚ) = Rat.divInt 1 4 := by simp [Rat.divInt_eq_div]
  calc
    (1 / 4 : ℚ).den = (Rat.divInt 1 4).den := congrArg Rat.den e
    _ ≤ 4 := Nat.le_of_dvd (by decide) h

private theorem corner_den (target j : Nat) (g : ℚ) : (cellCorner target j g).den ≤ 4 := by
  unfold cellCorner
  split
  · decide
  · split
    · exact quarter_den_le
    · decide

/-- Exact bit bounds for every arithmetic result in the fixed coordinate-update block.
No bound on the magnitude or denominator of the gradient is needed for these computations. -/
theorem updateCell_bits (target j : Nat) (a g z : ℚ) (A Z : Nat)
    (ha : 0 ≤ a ∧ a ≤ 1) (hz : 0 ≤ z ∧ z ≤ 1) (hA : a.den ≤ A) (hZ : z.den ≤ Z) :
    let d := cellCorner target j g-z
    RAM.ratBits d ≤ updateWidth A Z ∧ RAM.ratBits (a*d) ≤ updateWidth A Z ∧
      RAM.ratBits (cellValue target j a g z) ≤ updateWidth A Z := by
  let c := cellCorner target j g
  let d := c-z
  let u := a*d
  have hcb : 0 ≤ c ∧ c ≤ 1 := corner_box _ _ _
  have hcd : c.den ≤ 4 := corner_den _ _ _
  have hdabs : |d| ≤ 1 := by
    apply abs_le.mpr
    dsimp [d]
    constructor <;> linarith [hcb.1,hcb.2,hz.1,hz.2]
  have huabs : |u| ≤ 1 := by
    rw [show u = a*d from rfl, abs_mul, abs_of_nonneg ha.1]
    simpa using mul_le_mul ha.2 hdabs (abs_nonneg _) zero_le_one
  have hvabs : |z+u| ≤ 1 := by
    apply abs_le.mpr
    dsimp [u,d]
    constructor
    · nlinarith [mul_nonneg ha.1 hcb.1, mul_nonneg (sub_nonneg.mpr ha.2) hz.1]
    · nlinarith [mul_nonneg ha.1 (sub_nonneg.mpr hcb.2),
        mul_nonneg (sub_nonneg.mpr ha.2) (sub_nonneg.mpr hz.2)]
  have hde : d.den ≤ 4*Z :=
    (Nat.le_of_dvd (Nat.mul_pos c.pos z.pos) (Rat.sub_den_dvd c z)).trans
      (Nat.mul_le_mul hcd hZ)
  have hue : u.den ≤ A*(4*Z) :=
    (Nat.le_of_dvd (Nat.mul_pos a.pos d.pos) (Rat.mul_den_dvd a d)).trans
      (Nat.mul_le_mul hA hde)
  have hve : (z+u).den ≤ Z*(A*(4*Z)) :=
    (Nat.le_of_dvd (Nat.mul_pos z.pos u.pos) (Rat.add_den_dvd z u)).trans
      (Nat.mul_le_mul hZ hue)
  have h₁ : 4*Z ≤ 4*(A+1)*(Z+1)^2 := by ring_nf; omega
  have h₂ : A*(4*Z) ≤ 4*(A+1)*(Z+1)^2 := by ring_nf; omega
  have h₃ : Z*(A*(4*Z)) ≤ 4*(A+1)*(Z+1)^2 := by ring_nf; omega
  exact ⟨ratBits_of_unit hdabs (hde.trans h₁), ratBits_of_unit huabs (hue.trans h₂),
    ratBits_of_unit hvabs (hve.trans h₃)⟩

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
