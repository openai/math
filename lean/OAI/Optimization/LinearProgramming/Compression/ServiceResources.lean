import OAI.Optimization.LinearProgramming.Compression.ServiceParameters
import OAI.Optimization.LinearProgramming.OracleSpec.Compression
import OAI.Optimization.LinearProgramming.Compression.PhysicalRestartCode

/-! One pair of fixed polynomials bounds the whole outer machine, including dynamic
window clearing, table insertion, and every digit of a successful output. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServiceResources
open Polynomial RAM ServiceBudget GeneratorTable

noncomputable def postWork (n g : ℕ) :=
  7*live n g+9+30*(g+1)*(stride n+1)+19*(3+2*onlineMinorBitPolynomial.eval n)+27

noncomputable def totalWork (time : Polynomial ℕ) (rom n g : ℕ) :=
  6200*(n+1)^13+ServicePrepare.work time rom n g+1+(2*time.eval n+2)+postWork n g+8

noncomputable def timePolynomial (time : Polynomial ℕ) (rom : ℕ) : Polynomial ℕ :=
  let G := (X+1)^6
  let L := 30*(X+1)^8
  let cap := C (coefficient time)*(X+1)^exponent time+C (rom+114)
  let prepare := monomialCapacityTime (coefficient time) (exponent time)+
    (12*L+28+(10*cap+150+40*(X+L+1)))
  let post := 7*L+9+30*(G+1)*((2*X+3)+1)+19*(3+2*onlineMinorBitPolynomial)+27
  6200*(X+1)^13+prepare+1+(2*time+2)+post+8

noncomputable def heightPolynomial (height : Polynomial ℕ) : Polynomial ℕ :=
  50*(X+1)^6 + C (height.eval 1)*(20*(X+1)^10+1)^height.natDegree +
    6+2*C (onlineMinorBitPolynomial.eval 1)*(X+1)^onlineMinorBitPolynomial.natDegree

theorem time_le (time : Polynomial ℕ) (rom n g : ℕ) (hg : g ≤ paperWidth n) :
    totalWork time rom n g ≤ (timePolynomial time rom).eval n := by
  have lg := live_le n g hg
  change g ≤ (n+1)^6 at hg
  simp only [totalWork,ServicePrepare.work,postWork,timePolynomial,capacity,stride,eval_add,
    eval_mul,eval_pow,eval_C,eval_X,eval_one,eval_ofNat]
  gcongr

theorem height_covers (height : Polynomial ℕ) (L n inputSize : ℕ) (hn : n ≤ L)
    (hsize : inputSize ≤ 20*(L+1)^10) :
    let H := (heightPolynomial height).eval L
    50*(L+1)^6 ≤ H ∧ height.eval inputSize ≤ H ∧ 6+2*onlineMinorBitPolynomial.eval n ≤ H := by
  have hi := polynomial_eval_le_polyBound height inputSize
  have hspace : height.eval inputSize ≤ height.eval 1*(20*(L+1)^10+1)^height.natDegree :=
    hi.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hsize) _))
  have hp := polynomial_eval_le_polyBound onlineMinorBitPolynomial n
  have ex : onlineMinorBitPolynomial.eval n ≤ onlineMinorBitPolynomial.eval 1*(L+1)^onlineMinorBitPolynomial.natDegree :=
    hp.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.succ_le_succ hn) _))
  dsimp only
  simp only [heightPolynomial,eval_add,eval_mul,eval_pow,eval_C,eval_X,eval_one,eval_ofNat,Nat.mul_assoc]
  omega

theorem restart_le (n g : ℕ) : restartPostBound n g (live n g) ≤ postWork n g := by
  unfold restartPostBound postWork
  omega

theorem success_le {n g : ℕ} {q : ℚ} (hq : ratBits q ≤ 3+2*onlineMinorBitPolynomial.eval n) :
    7*(live n g-1)+19*(OracleSpec.MinorLog.width q.num.natAbs+OracleSpec.MinorLog.width q.den)+27 ≤
      postWork n g := by
  have width : OracleSpec.MinorLog.width q.num.natAbs+OracleSpec.MinorLog.width q.den ≤ ratBits q := by
    unfold OracleSpec.MinorLog.width ratBits; omega
  unfold postWork
  omega

theorem nat_bits_le (j : ℕ) : ratBits (j:ℚ) ≤ j+3 := by
  simp only [ratBits, Rat.num_natCast, Int.natAbs_natCast, Rat.den_natCast,
    show Nat.log2 1 = 0 by rfl, Nat.add_zero]
  have h := Nat.log2_le_self j
  omega

end ServiceResources
end Compression
end LinearProgramming
end Optimization
end OAI

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace ServicePost
open RAM OracleSpec.MinorLog

theorem packet_room {q : ℚ} {cap : ℕ} (room : 2*(ratBits q+2) ≤ cap) :
    2*(3+width q.num.natAbs+width q.den) ≤ cap := by
  unfold width ratBits at *
  omega

end ServicePost
end Compression
end LinearProgramming
end Optimization
end OAI
