import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMGradient
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMIO

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM Matrix
open scoped BigOperators Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- Scalar control registers survive the matrix and coordinate operations in each round. -/
structure RoundControl (n p : ℕ) (m : Memory K) : Prop where
  dimension : m.data 11 = (n : K)
  count : m.data 12 = (p : K)
  limit : m.data 13 = (fwRounds n : K)

/-- The values that can occur in the one-round program beyond its gradient dot products. -/
structure RoundSafe (P : K → Prop) (Q : Matrix (Fin n) (Fin n) K) (i : Fin n)
    (p : ℕ) : Prop where
  zero : P 0
  quarter : P (1/4)
  one : P 1
  two : P 2
  denominator : P ((p : K)+2)
  fraction : P (2/((p : K)+2))
  successor : P ((p+1 : ℕ) : K)
  gradient : GradientSafe P Q (fwIterate Q i p)
  move : ∀ j : Fin n,
    let z := fwIterate Q i p
    let a : K := 2/(p+2 : K)
    let d := cellCorner i j ((Q *ᵥ z) j) - z j
    P d ∧ P (a*d) ∧ P (z j+a*d)

/-- One round, including the actual arithmetic computation of the step size and the increment
of the scalar loop counter. -/
def roundBlock : Block :=
  .seq gradientBlock <| .seq (.op (.const 0 2)) <| .seq (.op (.add 1 12 0)) <|
    .seq (.op (.div 10 0 1)) <| .seq updateBlock <|
      .seq (.op (.const 0 1)) (.op (.add 12 12 0))

theorem roundBlock_framed (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (p : ℕ) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (hview : View L i Q (fwIterate Q i p) m) (hc : RoundControl n p m) (hp : RoundSafe P Q i p) :
    ∃ t k, k ≤ n*(9*n+9)+16*n+15 ∧ Block.Eval (Memory.AllData P) roundBlock m k t ∧
      View L i Q (fwIterate Q i (p+1)) t ∧ RoundControl n (p+1) t ∧ CallerFrame L m t := by
  let z := fwIterate Q i p
  let a : K := 2/((p:K)+2)
  obtain ⟨s,eg,vs,gs,low,fg⟩ := gradientBlock_framed L i Q z m P hm hview hp.gradient
  have hsafety := eg.safe_end
  have hs12 : s.data 12 = (p:K) := (low _ (by decide)).trans hc.count
  let s0 := s.putData 0 2
  let s1 := s0.putData 1 ((p:K)+2)
  let s2 := s1.putData 10 a
  have h0 : s0.AllData P := hsafety.putData _ hp.two
  have h1 : s1.AllData P := h0.putData _ hp.denominator
  have h2 : s2.AllData P := h1.putData _ hp.fraction
  have e0 : Block.Eval (Memory.AllData P) (.op (.const 0 2)) s 1 s0 := by
    simpa [s0] using Block.Eval.op_const s 0 2 hsafety (by simpa using h0)
  have e1 : Block.Eval (Memory.AllData P) (.op (.add 1 12 0)) s0 1 s1 := by
    have eq : s0.data 12 + s0.data 0=(p:K)+2 := by simp [s0,hs12]
    simpa only [eq] using Block.Eval.op_add s0 1 12 0 h0 (by simpa only [eq] using h1)
  have e2 : Block.Eval (Memory.AllData P) (.op (.div 10 0 1)) s1 1 s2 := by
    have eq : s1.data 0/s1.data 1=a := by simp [s1,s0,a]
    have hnz : s1.data 1≠0 := by simp [s1];positivity
    simpa only [eq] using Block.Eval.op_div s1 10 0 1 hnz h1 (by simpa only [eq] using h2)
  have v2 : View L i Q z s2 := ((vs.putData (d:=0) (by decide) _).putData (d:=1) (by decide) _).putData
    (d:=10) (by decide) _
  have g2 : Gradient L (Q *ᵥ z) s2 := ((gs.putData (d:=0) (by decide) _).putData (d:=1) (by decide) _).putData
    (d:=10) (by decide) _
  have va := L.reserved
  have vz := L.afterMatrix
  have vg := L.afterPoint
  have sc : s2.data 10=a := by simp [s2]
  obtain ⟨u,k,hk,eu,unew,uframe,uaddr,_⟩ := updateBlock_spec s2 P h2 hp.zero hp.one hp.quarter
    (by rw [v2.point];omega) (by rw [v2.gradient];omega)
    (Or.inl (by rw [v2.point,v2.gradient,v2.dimension];exact vg))
    (fun j hj => by
      have hj' : j<n := v2.dimension ▸ hj
      let k : Fin n := ⟨j,hj'⟩
      have hx := v2.coord k
      have hg := g2 k
      change s2.data (L.point+j)=z k at hx
      change s2.data (L.gradient+j)=(Q *ᵥ z) k at hg
      dsimp only
      rw [v2.point,v2.gradient,v2.target,hx,hg,sc]
      exact hp.move k)
  have usafe : u.AllData P := eu.safe_end
  have uLow (r : ℕ) (h₁ : 10<r) (h₂ : r<20) : u.data r=m.data r := by
    have h := uframe r (by omega) (Or.inl (by rw [v2.point];omega))
    have hr0 : r ≠ 0 := by omega
    have hr1 : r ≠ 1 := by omega
    have hr10 : r ≠ 10 := by omega
    rw [h]
    simpa [s2,s1,s0,hr10,hr1,hr0] using low r h₂
  have ua : Addresses L i u := ⟨(uaddr 23 (by decide) (by decide) (by decide)).trans v2.dimension,
    (uaddr 25 (by decide) (by decide) (by decide)).trans v2.point,
    (uaddr 28 (by decide) (by decide) (by decide)).trans v2.gradient,
    (uaddr 29 (by decide) (by decide) (by decide)).trans v2.target,
    (uaddr 34 (by decide) (by decide) (by decide)).trans v2.matrix⟩
  have uv : View L i Q (fwIterate Q i (p+1)) u := by
    refine ⟨ua,?_,?_⟩
    · intro r j
      have h' := Nat.mul_le_mul_right n r.isLt
      rw [Nat.succ_mul] at h'
      rw [uframe _ (by omega) (Or.inl (by rw [v2.point];have := j.isLt;omega))]
      exact v2.entry r j
    · intro j
      have h := unew j (v2.dimension ▸ j.isLt)
      rw [v2.point,v2.gradient,v2.target,sc,v2.coord j,g2 j] at h
      exact h.trans (cellValue_eq_fwStep Q hs he i j z a)
  let u0 := u.putData 0 1
  let t := u0.putData 12 ((p+1 : ℕ) : K)
  have hu0 : u0.AllData P := usafe.putData _ hp.one
  have ht : t.AllData P := hu0.putData _ hp.successor
  have ef : Block.Eval (Memory.AllData P) (.op (.const 0 1)) u 1 u0 := by
    simpa [u0] using Block.Eval.op_const u 0 1 usafe (by simpa using hu0)
  have ec : Block.Eval (Memory.AllData P) (.op (.add 12 12 0)) u0 1 t := by
    have eq : u0.data 12+u0.data 0=((p+1:ℕ):K) := by simp [u0,uLow 12 (by decide) (by decide),hc.count]
    simpa only [eq] using Block.Eval.op_add u0 12 12 0 hu0 (by simpa only [eq] using ht)
  have f2 : CallerFrame L m s2 := ((fg.putLow (k:=0) (by decide) _).putLow
    (k:=1) (by decide) _).putLow (k:=10) (by decide) _
  have fu : CallerFrame L s2 u := by
    intro d hd outside _
    apply uframe d (by omega)
    rwa [v2.point,v2.dimension]
  have ft : CallerFrame L m t :=
    ((f2.trans fu).putLow (k:=0) (by decide) _).putLow (k:=12) (by decide) _
  refine ⟨t,_,?_,eg.seq (e0.seq (e1.seq (e2.seq (eu.seq (ef.seq ec))))),
    (uv.putData (d:=0) (by decide) _).putData (d:=12) (by decide) _,⟨?_,?_,?_⟩,ft⟩
  · rw [v2.dimension] at hk
    omega
  · simpa [t,u0,uLow 11 (by decide) (by decide)] using hc.dimension
  · simp [t]
  · simpa [t,u0,uLow 13 (by decide) (by decide)] using hc.limit

theorem roundBlock_spec (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (p : ℕ) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (hview : View L i Q (fwIterate Q i p) m) (hc : RoundControl n p m) (hp : RoundSafe P Q i p) :
    ∃ t k, k ≤ n*(9*n+9)+16*n+15 ∧ Block.Eval (Memory.AllData P) roundBlock m k t ∧
      View L i Q (fwIterate Q i (p+1)) t ∧ RoundControl n (p+1) t := by
  obtain ⟨t,k,hk,e,v,c,_⟩ := roundBlock_framed L i Q hs he p m P hm hview hc hp
  exact ⟨t,k,hk,e,v,c⟩

/-- The outer loop terminates on arbitrary projector entries satisfying the semantic
preconditions of the geometric test. The bounds cover every branch and control step. -/
def roundsBlock : Block := .loop (.scalarLT 12 13) roundBlock

theorem roundsBlock_framed (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (v : View L i Q (fwLower i) m) (ctl : RoundControl n 0 m)
    (hp : ∀ p<fwRounds n, RoundSafe P Q i p) :
    ∃ t k, k ≤ fwRounds n*(n*(9*n+9)+16*n+17)+1 ∧
      Block.Eval (Memory.AllData P) roundsBlock m k t ∧ View L i Q (fwIterate Q i (fwRounds n)) t ∧
      RoundControl n (fwRounds n) t ∧ CallerFrame L m t := by
  let I (p : ℕ) (s : Memory K) := s.AllData P ∧ View L i Q (fwIterate Q i p) s ∧ RoundControl n p s ∧ CallerFrame L m s
  obtain ⟨t,k,hk,et,_,vt,ct,ft⟩ := Block.Eval.loop_invariant (c:=.scalarLT 12 13) (body:=roundBlock)
    I m (fwRounds n) (n*(9*n+9)+16*n+15) ⟨hm,v,ctl,CallerFrame.refl L m⟩
    (fun p hlt s ⟨sh,vs,cs,fs⟩ => by
      obtain ⟨u,k,hk,eu,vu,cu,fu⟩ := roundBlock_framed L i Q hs he p s P sh vs cs (hp p hlt)
      refine ⟨?_,u,k,hk,eu,eu.safe_end,vu,cu,fs.trans fu⟩
      simp [Cond.test,cs.count,cs.limit,hlt])
    (fun s ⟨hsafe,_,c,_⟩ => ⟨by simp [Cond.test,c.count,c.limit],hsafe⟩)
  exact ⟨t,k,hk,et,vt,ct,ft⟩

theorem roundsBlock_spec (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (v : View L i Q (fwLower i) m) (ctl : RoundControl n 0 m)
    (hp : ∀ p<fwRounds n, RoundSafe P Q i p) :
    ∃ t k, k ≤ fwRounds n*(n*(9*n+9)+16*n+17)+1 ∧
      Block.Eval (Memory.AllData P) roundsBlock m k t ∧ View L i Q (fwIterate Q i (fwRounds n)) t ∧
      RoundControl n (fwRounds n) t := by
  obtain ⟨t,k,hk,e,w,c,_⟩ := roundsBlock_framed L i Q hs he m P hm v ctl hp
  exact ⟨t,k,hk,e,w,c⟩

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
