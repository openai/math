import OAI.Computability.VPVNP.VerifierMembership
import OAI.Computability.VPVNP.VerifierMachine

/-! # VNP membership of the integer family of Theorem 1.1 -/

namespace OAI
namespace Computability
namespace VPVNP

/-- Equation (1.1), interpreted as a formal polynomial family over any field, lies in
VNP. The Boolean witnesses are the input word, the canonical path choices and the
gate values of the compiled verifier for the encoded transition table. -/
theorem P_isVNP (F : Type*) [Field F] :
    IsVNP (σ := fun n => Fin n × Bool) (fun n => MvPolynomial.map (Int.castRingHom F) (P n)) :=
  Verifier.P_isVNP_of_verifier VerifierMachine.verifierCircuit
    VerifierMachine.verifierSize_polynomiallyBounded
    (fun _ x w => VerifierMachine.verifierCircuit_eval x w)

end VPVNP
end Computability
end OAI
