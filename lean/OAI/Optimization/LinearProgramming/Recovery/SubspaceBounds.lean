import OAI.Optimization.LinearProgramming.Recovery.SubspaceKernel
import OAI.Optimization.LinearProgramming.Geometry.OracleBounds
import OAI.Optimization.LinearProgramming.RAM.RAMPolynomial

/-! Fixed polynomial bounds for the actual nested price/geometry/LLL machine. The
learner input contains the length-B binary exponent, rather than an address of size 2^B. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Recovery
namespace PackedPCG
open RAM OracleSpec BitRAM Geometry Polynomial
open _root_.OAI.Optimization.LinearProgramming.Geometry.BorderBatch
open _root_.OAI.Optimization.LinearProgramming.Geometry.MinorInstall
open _root_.OAI.Optimization.LinearProgramming.Recovery.OracleInline

theorem poly_mono (p : Polynomial ℕ) {a b : ℕ} (le : a ≤ b) : p.eval a ≤ p.eval b := by
  rw [Polynomial.eval_eq_sum,Polynomial.eval_eq_sum]
  unfold Polynomial.sum
  exact Finset.sum_le_sum (fun i _=>Nat.mul_le_mul_left _ (Nat.pow_le_pow_left le i))

noncomputable def learnerBound (B : Polynomial ℕ) (coefficient degree : ℕ) : Polynomial ℕ := C coefficient*(X+B+3)^degree

theorem learnerBound_spec {p : BitProgram} (B : Polynomial ℕ) (coefficient degree : ℕ)
    (correct : ∀(N R : ℕ),0 < N → 0 < R → ∀(i : Fin N) (f : Transcript→Word→Bool),
      p.ComputesWithin (fun h w=>[f h w]) (priceInput R i) (coefficient*(N+(R+1).log2+1)^degree) (pricePost R i))
    {n : ℕ} (i : Fin n) (f : Transcript→Word→Bool) :
    p.ComputesWithin (fun h w=>[f h w]) (priceInput (2^(1+B.eval n)) i) ((learnerBound B coefficient degree).eval n)
      (pricePost (2^(1+B.eval n)) i) := by
  let e:=1+B.eval n
  have positive : 0<(2:ℕ)^e:=pow_pos (by decide) _
  have near : 2^e+1 ≤ 2^(e+1):=by rw [pow_succ];omega
  have log : (2^e+1).log2 ≤ e+1 := by
    have hp : 2^e+1≠0:=by omega
    apply Nat.lt_succ_iff.mp
    apply (Nat.log2_lt hp).2
    have far : (2:ℕ)^(e+1) < 2^((e+1)+1) :=
      Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self (e+1))
    exact near.trans_lt far
  obtain ⟨t,z,run,h,stop,out⟩:=correct n (2^e) (by have:=i.isLt;omega) positive i f
  refine ⟨t,z,run,h.trans ?_,stop,out⟩
  simp only [learnerBound,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_pow,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  dsimp [e] at log ⊢
  omega

/-- Once the actual dimensions are related by r+s=n, every public price-label clock
is below this expression. It uses only addition, multiplication, and fixed powers. -/
private def timeShape {A : Type*} [Semiring A] (n T cap states reset geom : A) : A :=
  let packet:=(n+1)*(24*T+50)+32*T+6*n+64
  let numeric:=4*(packet+11)+(4*(5000*(2*n+1)^3)+geom)
  let price:=(20*T+14)+(2*(numeric+1)+2+18)
  let transfer:=4*(13*T+7)+price+4*(18+9)+2
  let stage:=4*(4+reset)+((4*(2*states+35)+transfer+32)*(T+1)+5+81)
  8+((cap+1)*(stage+2)+1)+8

noncomputable def restartPolynomial (constant : ℕ) : Polynomial ℕ := C constant*X^2*(2*X+1)

noncomputable def geomTimePolynomial (B : Polynomial ℕ) : Polynomial ℕ :=
  (LabelRAM.labelTimePolynomial.comp (2*X))*(4+208*(2*X+1)^2+2*B)

noncomputable def subspaceTimePolynomial (p : BitProgram) (B T : Polynomial ℕ) (constant : ℕ) : Polynomial ℕ :=
  timeShape X T (restartPolynomial constant) (C p.states) (PriceEpoch.epochPolynomial p B) (geomTimePolynomial B)

theorem restartPolynomial_bound (constant n : ℕ) : constant*n^2*((2*n).log2+1) ≤ (restartPolynomial constant).eval n := by
  simp [restartPolynomial]
  gcongr
  exact Nat.log2_le_self _

theorem geomTimePolynomial_bound (B : Polynomial ℕ) (r s n : ℕ) (dims : r+s=n) :
    geometricCallTime r s n (B.eval n) ≤ (geomTimePolynomial B).eval n := by
  have geo:=(LabelRAM.concreteTime_le_eval r n).trans (poly_mono _ (by omega : r+n ≤ 2*n))
  have service:=serviceClock_le r s n (B.eval n)
  rw [dims] at service
  have ce : max 4 (serviceClock r s n (B.eval n)) ≤ 4+208*(2*n+1)^2+2*B.eval n := by
    rw [show n+n=2*n by omega] at service
    omega
  simpa [geomTimePolynomial,geometricCallTime] using Nat.mul_le_mul geo ce

theorem subspaceTimePolynomial_bound (p : BitProgram) (B T : Polynomial ℕ) (constant r s n cap : ℕ)
    (dims : r+s=n) (rc : cap ≤ (restartPolynomial constant).eval n) :
    retryTime p B r s n (B.eval n) (T.eval n) cap + 8 ≤ (subspaceTimePolynomial p B T constant).eval n := by
  have geometric:=geomTimePolynomial_bound B r s n dims
  have rs : r+n+1 ≤ 2*n+1 := by omega
  simp only [subspaceTimePolynomial,timeShape,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_C,Polynomial.eval_one,Polynomial.eval_ofNat]
  unfold retryTime episodeTime resetTime epochUnit transferTime priceHandlerTime numericPriceTime NativePrice.packetTime
  gcongr

noncomputable def scalarPolynomial (B T initial basis : Polynomial ℕ) (constant : ℕ) : Polynomial ℕ :=
  let increment:=(LabelRAM.labelWidthPolynomial.comp (2*X+basis+B))+(2*X+4)
  initial+(restartPolynomial constant+1)*((T+1)*increment)

theorem scalarPolynomial_bound (B T initial basis : Polynomial ℕ) (constant r s n L h e cap : ℕ)
    (dims : r+s=n) (nL : n ≤ L) (start : h ≤ initial.eval L) (row : e ≤ basis.eval L)
    (rc : cap ≤ (restartPolynomial constant).eval n) :
    h+(cap+1)*((T.eval n+1)*geometricIncrement r s n e (B.eval n)) ≤ (scalarPolynomial B T initial basis constant).eval L := by
  have b:=poly_mono B nL
  have t:=poly_mono T nL
  have c:=rc.trans (poly_mono _ nL)
  have width:=LabelRAM.concreteWidth_le_eval r n e (B.eval n) 0
  have wh : geometricLabelWidth r n e (B.eval n) 0 ≤ LabelRAM.labelWidthPolynomial.eval (2*L+basis.eval L+B.eval L) := by
    have localBound : geometricLabelWidth r n e (B.eval n) 0 ≤ LabelRAM.labelWidthPolynomial.eval (r+n+e+B.eval n) := by
      simpa only [geometricLabelWidth,Nat.zero_add] using width
    exact localBound.trans (poly_mono _ (by omega))
  have num : r+s+n+4 ≤ 2*L+4:=by omega
  simp only [scalarPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_one,Polynomial.eval_ofNat,Polynomial.eval_comp,
    Polynomial.eval_X,geometricIncrement]
  gcongr

end PackedPCG
end Recovery
end LinearProgramming
end Optimization
end OAI
