import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMRounds
import OAI.Optimization.LinearProgramming.Geometry.FrankWolfeRAMSetup

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace FWRAM

open RAM Matrix
open scoped BigOperators Matrix

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- The complete fixed RAM block: choose the initial corner, execute the rounds, test the residual. -/
def labelBlock : Block :=
  .seq setupBlock (.seq initBlock (.seq roundsBlock (.seq gradientBlock energyBlock)))

/-- This immutable sequence contains only primitive instructions of the paper's machine. -/
def labelProgram : Program := labelBlock.compile 0 ++ [.halt 0]

def labelTime (n : ℕ) : ℕ :=
  fwRounds n*(n*(9*n+9)+16*n+17)+n*(9*n+9)+22*n+38

theorem labelTime_polynomial (n : ℕ) : labelTime n ≤ RAM.polyBound 500000000 5 n := by
  unfold labelTime fwRounds RAM.polyBound
  ring_nf
  omega

/-- A scalar predicate can be carried through every instruction by bounding just these
initial constants, partial sums, and one-round arithmetic terms. -/
structure LabelSafe (Q : Matrix (Fin n) (Fin n) K) (i : Fin n) (P : K → Prop) : Prop where
  zero : P 0
  one : P 1
  quarter : P (1/4)
  natural : ∀ j≤n, P (j:K)
  cap : ∀ j : Fin 4, P (8000000*(n:K)^j.val)
  rounds : ∀ p<fwRounds n, RoundSafe P Q i p
  finalGradient : GradientSafe P Q (fwIterate Q i (fwRounds n))
  thousand : P 1000
  scale : P (1000*(n:K))
  scaleSq : P ((1000*(n:K))^2)
  threshold : P (energyThreshold n)
  term : ∀ j : Fin n, P (((Q *ᵥ fwIterate Q i (fwRounds n)) j)^2)
  «prefix» : ∀ k : ℕ, ∀ hk : k≤n,
    P (∑ j : Fin k, ((Q *ᵥ fwIterate Q i (fwRounds n)) (j.castLE hk))^2)

theorem labelBlock_framed (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (a : Addresses L i m) (hQ : ∀ r j : Fin n, m.data (L.matrix+r.val*n+j.val)=Q r j)
    (hP : LabelSafe Q i P) :
    ∃ t k, k+1 ≤ labelTime n ∧ Block.Eval (Memory.AllData P) labelBlock m k t ∧
      t.data 19=(if fwEnergy Q (fwIterate Q i (fwRounds n)) ≤ energyThreshold n then 1 else 0) ∧
      CallerFrame L m t := by
  have lo := L.reserved
  have hz := L.afterMatrix
  have hg := L.afterPoint
  obtain ⟨s,es,sdim,scount,slimit,sidx,sdata⟩ :=
    setupBlock_spec P m n a.dimension hm hP.one hP.natural hP.cap
  have sa : Addresses L i s := ⟨(sidx _ (by decide)).trans a.dimension,
    (sidx _ (by decide)).trans a.point,(sidx _ (by decide)).trans a.gradient,
    (sidx _ (by decide)).trans a.target,(sidx _ (by decide)).trans a.matrix⟩
  obtain ⟨u,ei,points,iframe,iaddr⟩ := initBlock_spec s P es.safe_end hP.zero hP.quarter
    (by rw [sa.point];omega) (by rw [sa.target,sa.dimension];exact i.isLt)
  have ua : Addresses L i u := ⟨(iaddr _ (by decide) (by decide)).trans sa.dimension,
    (iaddr _ (by decide) (by decide)).trans sa.point,(iaddr _ (by decide) (by decide)).trans sa.gradient,
    (iaddr _ (by decide) (by decide)).trans sa.target,(iaddr _ (by decide) (by decide)).trans sa.matrix⟩
  have uv : View L i Q (fwLower i) u := by
    refine ⟨ua,?_,?_⟩
    · intro r j
      have h' := Nat.mul_le_mul_right n r.isLt
      rw [Nat.succ_mul] at h'
      rw [iframe _ (by omega) (Or.inl (by rw [sa.point];have := j.isLt;omega)),
        sdata _ (by omega)]
      exact hQ r j
    · intro j
      have h := points j (sa.dimension ▸ j.isLt)
      simpa only [sa.point,sa.target,fwLower,Fin.val_inj] using h
  have ilo (d : ℕ) (hd : 2≤d) (hd' : d<20) : u.data d=s.data d :=
    iframe d hd (Or.inl (by rw [sa.point];omega))
  have uc : RoundControl n 0 u := ⟨(ilo _ (by decide) (by decide)).trans sdim,
    by simpa using (ilo 12 (by decide) (by decide)).trans scount,
    (ilo _ (by decide) (by decide)).trans slimit⟩
  obtain ⟨v,k,hk,er,vv,vc,fr⟩ := roundsBlock_framed L i Q hs he u P ei.safe_end uv uc hP.rounds
  obtain ⟨w,em,vw,gw,wlow,fg⟩ :=
    gradientBlock_framed L i Q _ v P er.safe_end vv hP.finalGradient
  have epre (r : ℕ) (hr : r≤n) :
      energyPrefix w r = ∑ j : Fin r, ((Q *ᵥ fwIterate Q i (fwRounds n)) (j.castLE hr))^2 := by
    rw [energyPrefix, ← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [vw.gradient]
    exact congrArg (·^2) (gw (j.castLE hr))
  obtain ⟨t,l,hl,ee,hout,eframe,_⟩ := energyBlock_spec w P em.safe_end
    (vw.dimension ▸ i.pos) (by rw [vw.gradient];omega)
    ((wlow _ (by decide)).trans (vc.dimension.trans (congrArg Nat.cast vw.dimension.symm)))
    hP.zero hP.one hP.thousand (vw.dimension ▸ hP.scale) (vw.dimension ▸ hP.scaleSq)
    (vw.dimension ▸ hP.threshold)
    (fun j hj => by
      let k : Fin n := ⟨j,vw.dimension ▸ hj⟩
      have q := gw k
      change w.data (L.gradient+j)=_ at q
      rw [vw.gradient,q]
      exact hP.term k)
    (fun j hj => (epre j (vw.dimension ▸ hj)) ▸ hP.prefix _ _)
  have fsetup : CallerFrame L m s := fun d hd _ _ => sdata d hd
  have finit : CallerFrame L s u := by
    intro d hd outside _
    apply iframe d (by omega)
    rwa [sa.point,sa.dimension]
  have fend : CallerFrame L w t := fun d hd _ _ => eframe d (by omega) (Or.inr hd)
  refine ⟨t,_,?_,es.seq (ei.seq (er.seq (em.seq ee))),?_,
    (((fsetup.trans finit).trans fr).trans fg).trans fend⟩
  · unfold labelTime
    rw [sa.dimension,sa.target] at *
    rw [vw.dimension] at hl
    have := i.isLt
    omega
  · have res := energyPrefix_eq_fwEnergy w Q (fwIterate Q i (fwRounds n))
      (fun j => by rw [vw.gradient]; exact gw j)
    rw [vw.dimension,res] at hout
    exact hout

theorem labelBlock_spec (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (a : Addresses L i m) (hQ : ∀ r j : Fin n, m.data (L.matrix+r.val*n+j.val)=Q r j)
    (hP : LabelSafe Q i P) :
    ∃ t k, k+1 ≤ labelTime n ∧ Block.Eval (Memory.AllData P) labelBlock m k t ∧
      t.data 19=(if fwEnergy Q (fwIterate Q i (fwRounds n)) ≤ energyThreshold n then 1 else 0) := by
  obtain ⟨t,k,hk,e,out,_⟩ := labelBlock_framed L i Q hs he m P hm a hQ hP
  exact ⟨t,k,hk,e,out⟩

/-- An actual complete primitive-instruction trace, including halt. Scalar register 19 encodes the
Boolean label. The fixed program works on every dimension and every symmetric idempotent residual. -/
theorem labelProgram_trace (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) K)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (m : Memory K) (P : K → Prop) (hm : m.AllData P)
    (a : Addresses L i m) (hQ : ∀ r j : Fin n, m.data (L.matrix+r.val*n+j.val)=Q r j)
    (hP : LabelSafe Q i P) :
    ∃ k ≤ labelTime n, ∃ t : Fin (k+1) → State K,
      Trace labelProgram (m.atPC 0) k t ∧ (t (Fin.last k)).output=some 0 ∧
      (t (Fin.last k)).data 19=(if fwEnergy Q (fwIterate Q i (fwRounds n)) ≤ energyThreshold n then 1 else 0) ∧
      ∀ j, (t j).memory.AllData P := by
  obtain ⟨z,k,hk,ez,out⟩ := labelBlock_spec L i Q hs he m P hm a hQ hP
  obtain ⟨t,ht,halt,hend,hsafe⟩ := ez.halted_trace (tag:=0)
  refine ⟨k+1,hk,t,ht,halt,?_,hsafe⟩
  exact (congrArg (fun s : Memory K => s.data 19) hend).trans out

/-- Correct polynomial-time rational output, independent of scalar magnitudes. -/
theorem labelProgram_rational (L : Layout n) (i : Fin n) (Q : Matrix (Fin n) (Fin n) ℚ)
    (hs : Qᵀ=Q) (he : Q*Q=Q) (m : Memory ℚ) (a : Addresses L i m)
    (hQ : ∀ r j : Fin n, m.data (L.matrix+r.val*n+j.val)=Q r j) :
    ∃ k ≤ RAM.polyBound 500000000 5 n, ∃ t : Fin (k+1) → State ℚ,
      Trace labelProgram (m.atPC 0) k t ∧ (t (Fin.last k)).output=some 0 ∧
      (t (Fin.last k)).data 19=(if fwLabel Q i then 1 else 0) := by
  have grad (z : Fin n → ℚ) : GradientSafe (fun _ => True) Q z :=
    ⟨fun _ _ => True.intro,fun _ _ _ => True.intro⟩
  have rounds (p : ℕ) : RoundSafe (fun _ => True) Q i p :=
    ⟨True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,True.intro,
      grad _,fun _ => ⟨True.intro,True.intro,True.intro⟩⟩
  have hP : LabelSafe Q i (fun _ => True) :=
    ⟨True.intro,True.intro,True.intro,fun _ _ => True.intro,fun _ => True.intro,
      fun p _ => rounds p,grad _,True.intro,True.intro,True.intro,True.intro,
      fun _ => True.intro,fun _ _ => True.intro⟩
  obtain ⟨k,hk,t,ht,ho,hd,_⟩ := labelProgram_trace L i Q hs he m (fun _ => True)
    (fun _ => True.intro) a hQ hP
  refine ⟨k,hk.trans (labelTime_polynomial n),t,ht,ho,?_⟩
  simpa [fwLabel,fwArray_correct,fwTolerance,energyThreshold] using hd

end FWRAM
end Geometry
end LinearProgramming
end Optimization
end OAI
