import OAI.Computability.BorderVNP.TransmissionJointPacket
import OAI.Computability.BorderVNP.ResidueStagedRates
import OAI.Computability.BorderVNP.DiagonalAdvice

/-! # Uniform startup and common-prefix charges for the stretched batch in §11

The binary packet contains the residue board, its query addresses, the 81 scalar
extension words and the distinguished live index. The common physical prefix gains
one branch bit and one subtotal field for every team and every coordinate.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.ProcessorSlots

open VPVNP BurstRAM ResidueRates Diagonal Filter

/-- Number of new broadcast bits for the mode and all teams' rectangular count vectors. -/
def subtotalPrefix (teams : ℕ) (x : ReaderSizes) := 1+teams*((x.h+x.labels)*x.tally)

/-- Bits and native ticks of the physical startup, native matrix reader, and common
subtotal fields are bounded by a polynomial in the staged-reader charge and team count. -/
theorem ReferencePacket.staged_budget {g v : ℕ} (teams : ℕ) (x : ReaderSizes)
    (base entry : ℕ) (c : BooleanTranscript.Circuit (Fin x.publicBits ⊕ Fin v) g)
    (src : Fin x.publicBits → ℕ) (extension : Fin 81 → Word x.word)
    (star : Fin ((x.h+2)*x.pin) → Bool) :
    let p := ReferencePacket.ofCircuit base entry c src extension star
    p.bits.length + jointBudget p.bits.length x.word + x.stagedCharge g + subtotalPrefix teams x ≤
      10000*(teams+1)*(x.stagedCharge g+1)^2 := by
  intro p
  let C := x.stagedCharge g
  have paid := ReferencePacket.joint_charge_le base entry c src extension star
  change jointBudget p.bits.length x.word + p.bits.length ≤
    4096*(x.word+1)*(g+x.publicBits+(x.h+2)*x.pin+1) at paid
  have hg : g+x.publicBits ≤ C := by dsimp [C,ReaderSizes.stagedCharge]; omega
  have hp : (x.h+2)*x.pin ≤ x.publicBits := by dsimp only [ReaderSizes.publicBits]; omega
  have hh : (x.h+x.labels)*x.tally ≤ x.publicBits := by dsimp only [ReaderSizes.publicBits]; omega
  have hw : x.word ≤ C := by
    have sq := Nat.le_self_pow (by decide : 2 ≠ 0) (x.publicBits+x.guessBits+g+x.word+1)
    dsimp [C,ReaderSizes.stagedCharge]
    omega
  have pm : 4096*(x.word+1)*(g+x.publicBits+(x.h+2)*x.pin+1) ≤ 8192*(C+1)^2 := by
    calc
      _ ≤ 4096*(C+1)*(2*(C+1)) := by gcongr; omega
      _ = _ := by ring
  have ct : teams*((x.h+x.labels)*x.tally) ≤ teams*C := Nat.mul_le_mul_left teams (by omega)
  change p.bits.length + jointBudget p.bits.length x.word + C + (1+teams*((x.h+x.labels)*x.tally)) ≤ _
  change _ ≤ 10000*(teams+1)*(C+1)^2
  calc
    _ ≤ 8192*(C+1)^2 + C+1+teams*C := by omega
    _ ≤ _ := by nlinarith [Nat.zero_le (teams*C*C)]

/-- Every fixed polynomial stage certificate on the §9 chart yields room for the actual
joint processor packet, the live/reference indices and all team subtotals, uniformly in
their values. Multiplying the total charge by any fixed factor still fits the batch. -/
theorem eventually_joint_reader {σ ρ : ℝ} (hs : 0 < σ) (hgap : σ < ρ) (factor A B C D : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (teams T g v : ℕ) (x : ReaderSizes),
      teams ≤ adviceScale σ ρ n → T ≤ B*(adviceScale σ ρ n+1)^D → x.stagedCharge g ≤ A*(T+1)^C →
      ∀ (base entry : ℕ) (c : BooleanTranscript.Circuit (Fin x.publicBits ⊕ Fin v) g)
        (src : Fin x.publicBits → ℕ) (extension : Fin 81 → Word x.word) (star : Fin ((x.h+2)*x.pin) → Bool),
        let p := ReferencePacket.ofCircuit base entry c src extension star
        factor*(p.bits.length + jointBudget p.bits.length x.word + x.stagedCharge g + subtotalPrefix teams x)
          < stretch ρ n := by
  let T (M : ℕ) := B*(M+1)^D
  let K (M : ℕ) := A*(T M+1)^C
  let cost (M : ℕ) := factor*(10000*(M+1)*(K M+1)^2)
  have ht : PolynomiallyBounded T := (PolynomiallyBounded.const B).mul
    ((PolynomiallyBounded.id.add (.const 1)).pow D)
  have hk : PolynomiallyBounded K := (PolynomiallyBounded.const A).mul ((ht.add (.const 1)).pow C)
  have hc : PolynomiallyBounded cost := (PolynomiallyBounded.const factor).mul
    (((PolynomiallyBounded.const 10000).mul (PolynomiallyBounded.id.add (.const 1))).mul ((hk.add (.const 1)).pow 2))
  obtain ⟨a,b,hab⟩ := hc.exists_global_bound
  filter_upwards [advice_polynomial_lt_batch hs hgap (a*2^b) b,eventually_ge_atTop 1] with n bound hn
  intro teams t g v x hteams hT hstage base entry c src extension star p
  let M := adviceScale σ ρ n
  have hM : 1 ≤ M := by dsimp only [M,adviceScale]; omega
  have htM : t ≤ T M := hT
  have charge : x.stagedCharge g ≤ K M := hstage.trans (Nat.mul_le_mul_left A (Nat.pow_le_pow_left (Nat.succ_le_succ htM) _))
  have estimate := ReferencePacket.staged_budget teams x base entry c src extension star
  change p.bits.length + jointBudget p.bits.length x.word + x.stagedCharge g + subtotalPrefix teams x ≤ _ at estimate
  calc
    _ ≤ factor*(10000*(teams+1)*(x.stagedCharge g+1)^2) := Nat.mul_le_mul_left factor estimate
    _ ≤ cost M := by dsimp only [cost]; gcongr
    _ ≤ a*(M+1)^b := hab M
    _ ≤ a*(2*M)^b := by gcongr; omega
    _ = (a*2^b)*M^b := by rw [mul_pow,Nat.mul_assoc]
    _ < stretch ρ n := bound

end TeamContraction.ProcessorSlots

end BorderVNP
end Computability
end OAI
