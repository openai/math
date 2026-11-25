import OAI.Hierarchy.DescentStageLedger
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # A single initial charge at the original group's true zero-date price -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentDyadicSpan
open scoped BigOperators

def highPrice (factor N r : ℕ) := 3*factor*(14000066+224000*(N+1)*r)
def lowPrice (N signed operand selector : ℕ) :=
  3*(14000000*signed+224000*(N+1)*operand+528*selector)

/-- One paid date suffices even when the physical host row count is rounded up. -/
theorem rectangle_at_zero (S : AtomSchedule) (h word factor V G r N s₁ s₂ s₃ fee : ℕ)
    (hosts : 0<S.initialSites) (rows : V≤span S.initialSites)
    (wordFit : word≤factor*h) (groups : G=S.groupCount 0) (radix : r=S.radix)
    (actual : fee≤V*word*(14000066+224000*(N+1)*r)+V*(G*r)*(14000000*s₁+224000*(N+1)*s₂+528*s₃)) :
    fee≤S.hostSize 0*h*highPrice factor N r+S.hostSize 0*(S.groupCount 0*S.radix)*lowPrice N s₁ s₂ s₃ :=by
  have raw:=span_le S.initialSites
  have bound : V≤3*S.initialSites :=by omega
  have broad:=Nat.mul_le_mul_right (14000066+224000*(N+1)*r) (Nat.mul_le_mul bound wordFit)
  have narrow:=Nat.mul_le_mul_right (14000000*s₁+224000*(N+1)*s₂+528*s₃) (Nat.mul_le_mul_right (G*r) bound)
  apply actual.trans
  apply (Nat.add_le_add broad narrow).trans_eq
  rw [←groups,←radix]
  simp only [AtomSchedule.hostSize,pow_zero,Nat.mul_one,highPrice,lowPrice]
  ring

/-- Public exponents for the common-host component and the short-field component.
The coefficient may depend on the previously chosen cutoff, independently of h. -/
theorem price_scales (J a b factor K N r s₁ s₂ s₃ : ℕ)
    (arg : N≤scale J a) (radix : r≤scale J b)
    (signed : s₁≤K*scale J b) (operand : s₂≤K*scale J b) (selector : s₃≤K*scale J b) :
    highPrice factor N r≤scale J (a+b)*(50000000*factor) ∧
    lowPrice N s₁ s₂ s₃≤scale J (a+b)*(50000000*K) :=by
  have nz : 1≤scale J a :=Nat.two_pow_pos _
  have bz : 1≤scale J b :=Nat.two_pow_pos _
  have ap : N+1≤2*scale J a :=by omega
  have ex := Nat.mul_le_mul ap radix
  have sp : scale J b≤scale J (a+b) :=short_mono J (by omega)
  have one : 1≤scale J (a+b) :=Nat.two_pow_pos _
  have change_ : (2*scale J a)*scale J b=2*scale J (a+b) :=by rw [Nat.mul_assoc,scale_mul]
  rw [change_] at ex
  have lowArg:=Nat.mul_le_mul ap operand
  have cutoff : (2*scale J a)*(K*scale J b)=2*(K*scale J (a+b)) :=by rw [←scale_mul];ring
  rw [cutoff] at lowArg
  have os:=signed.trans (Nat.mul_le_mul_left K sp)
  have cs:=selector.trans (Nat.mul_le_mul_left K sp)
  constructor
  · unfold highPrice
    have e : 14000066+224000*(N+1)*r≤15000000*scale J (a+b) :=by
      rw [Nat.mul_assoc]
      omega
    calc
      _≤(3*factor)*(15000000*scale J (a+b)) :=Nat.mul_le_mul_left _ e
      _≤_:=by
        have df : 45000000*(factor*scale J (a+b))≤50000000*(factor*scale J (a+b)) :=
          Nat.mul_le_mul_right _ (by decide)
        nlinarith only [df]
  · unfold lowPrice
    rw [Nat.mul_assoc 224000]
    have e : 3*(14000000*s₁+224000*((N+1)*s₂)+528*s₃) ≤ 50000000*(K*scale J (a+b)) :=by omega
    exact e.trans_eq (by ring)

def atZero (S : AtomSchedule) (price : ℕ) (i : Fin (S.length+1)) := if i.val=0 then price else 0

theorem zero_receipt (S : AtomSchedule) (h high low price : ℕ)
    (paid : price≤S.hostSize 0*h*high+S.hostSize 0*(S.groupCount 0*S.radix)*low) :
    (∀i,atZero S price i≤S.hostSize i.val*h*high+S.hostSize i.val*(S.groupCount i.val*S.radix)*low) ∧
      (∑i,atZero S price i)=price :=by
  constructor
  · intro i
    by_cases atOrigin : i.val=0
    · simpa [atZero,atOrigin] using paid
    · simp [atZero,atOrigin]
  · simp [atZero,show ∀i : Fin (S.length+1),i.val=0 ↔ i=0 from
      fun i=>⟨fun eqn=>Fin.ext eqn,fun eqn=>by rw [eqn];rfl⟩]

end Hierarchy.DescentDatedSeedStartup

end OAI
