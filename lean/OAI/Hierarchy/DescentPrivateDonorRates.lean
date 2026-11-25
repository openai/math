import OAI.Hierarchy.DescentStageLedger
import OAI.Hierarchy.DescentPrivateDonorBillNumbers

namespace OAI
/-! # Age-independent exponents for the ordinary private-counter program -/
namespace Hierarchy.DescentCompiler.TerminalScale
open DescentSixParty Filter
open scoped BigOperators

theorem donor_rates {J K f amount s a : ℕ} (field : f≤ scale J s) (record : amount≤ scale J a) :
    K*(1274+6*f)≤ scale J s*(1376*K) ∧
    K*(4*amount*(342+2*f))≤ scale J (a+s)*(1376*K) := by
  have live : 0< scale J s := Nat.two_pow_pos _
  have small : 1274+6*f≤1376*scale J s :=by
    have x:=Nat.le_mul_of_pos_right 1274 live
    omega
  have work : 342+2*f≤344*scale J s := by
    have x:=Nat.le_mul_of_pos_right 342 live
    omega
  constructor
  · calc
      _ ≤ K*(1376*scale J s) := Nat.mul_le_mul_left _ small
      _ = _ := by ring
  · calc
      _ ≤ K*(4*scale J a*(344*scale J s)) :=
        Nat.mul_le_mul_left _ (Nat.mul_le_mul (Nat.mul_le_mul_left _ record) work)
      _ = _ := by rw [←scale_mul];ring

variable {F : Type} [Field F] (G : PoweredGadget F)

/-- The calibrated unit price applies to the two native procedures with the verified
per-age clock and syntax charges. A reset contributes zero to this ordinary subtotal. -/
theorem donor_calibration_at (t f g reset s a e K τ : ℕ)
    (tailRoom : s+3+(e+5)≤τ) :
    let n:=2+hostRate t reset*(t+1)+(a+s)+1+1
    ∀B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀M q p : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
        0<q→q≤ scale J e→h≤32*(q*p)→
        ∀ (fee work amount : Fin (S.length+1)→ℕ),
          (∀i,work i≤ scale J s) → (∀i,amount i≤ scale J a) →
          (∀i,fee i≤S.hostSize i.val*h*(K*(1274+6*work i))+
            S.hostSize i.val*(S.groupCount i.val*S.radix)*(K*(4*amount i*(342+2*work i)))) →
          (∑i,fee i)*2^J≤2*(M*(S.copies*p)) := by
  intro _ B positive bought
  have paid := calibration_at G t f g reset s (a+s) e (1376*K) 0 τ (by simpa using tailRoom) B positive (by simpa using bought)
  filter_upwards [paid] with h calcFee
  dsimp only
  intro M q p occupied fit cpu fee work amount fbound abound rows
  let J:=Nat.log 2 h/(2*B)
  apply calcFee M q p (scale J s*(1376*K)) (scale J (a+s)*(1376*K)) occupied fit cpu (by simp [J]) (by simp [J]) fee
  intro i
  obtain ⟨chargedHost,chargedItem⟩:=donor_rates (K:=K) (fbound i) (abound i)
  exact (rows i).trans (Nat.add_le_add (Nat.mul_le_mul_left _ chargedHost) (Nat.mul_le_mul_left _ chargedItem))

theorem donor_calibration (t f g reset s a e K : ℕ) :
    let τ:=s+3+(e+5)
    let n:=2+hostRate t reset*(t+1)+(a+s)+1+1
    ∀B : ℕ,0<B→2*(n+5+e)≤B→∀ᶠ h : ℕ in atTop,
      let J:=Nat.log 2 h/(2*B)
      ∀M q p : ℕ,let S:=stageNumbers G t J f g reset M (tail τ J)
        0<q→q≤ scale J e→h≤32*(q*p)→
        ∀ (fee work amount : Fin (S.length+1)→ℕ),
          (∀i,work i≤ scale J s) → (∀i,amount i≤ scale J a) →
          (∀i,fee i≤S.hostSize i.val*h*(K*(1274+6*work i))+
            S.hostSize i.val*(S.groupCount i.val*S.radix)*(K*(4*amount i*(342+2*work i)))) →
          (∑i,fee i)*2^J≤2*(M*(S.copies*p)) :=
  donor_calibration_at G t f g reset s a e K _ le_rfl

end Hierarchy.DescentCompiler.TerminalScale

end OAI
