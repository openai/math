import OAI.Hierarchy.DescentTerminalPreflightPolynomial
import OAI.Hierarchy.DescentTerminalPointerChosenBounds
import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # The terminal scan rate omits the tail-group exponent at the actual named epoch -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical
open scoped Fin.CommRing
noncomputable section

set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


open DescentTerminalPreflightSpace
open Computability.BorderVNP.FragmentBucket
namespace Branch

open DescentCompiler.TerminalScale DescentTerminalPointerDigits Filter
variable {tail:ℕ} (base:S.baseGroups=2^tail) (L:PreflightFormat)
local notation "spec" => preflightSpec X G S k g p tail L
local notation "J" => S.height

include base b hp in
theorem preflight_scan_scale (κ ℓ:ℕ) (positive:0<J) (blocks:k≤κ*(J+1))
    (nodeCols:L.columns≤ scale J ℓ) :
    (spec).scanScale≤ scale J (6+(κ+max ℓ S.localCapacityExponent)) := by
  let e:=max ℓ S.localCapacityExponent
  have pos:0<scale J e:=Nat.two_pow_pos _
  have upto (i j:ℕ) (ij:i≤j) : scale J i≤ scale J j :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ ij)
  have capband:2^(8+S.capGain*S.length)≤ scale J S.localCapacityExponent:=by
    have trueCap:=S.local_capacity (cap:=2^(8+S.capGain*S.length)) positive le_rfl le_rfl
    apply trueCap.trans
    change (2^J)^S.localCapacityExponent≤2^(S.localCapacityExponent*(J+1))
    rw [←pow_mul];apply Nat.pow_le_pow_right (by decide)
    rw [Nat.mul_add,Nat.mul_one,Nat.mul_comm J];omega
  have old:(spec).cap≤2^(8+S.capGain*S.length):=by
    rw [←(preflight_caps X G S b (tail:=tail) L).2.1];exact b.target.valid.capacity
  have cap:=capband.trans (upto _ e (Nat.le_max_right ..))
  have area:=(spec).scan_original (k:=scale J κ) (n:=scale J e) pos
    (preflight_grains X G S b hp base L).2
    (by change 0<S.groupCount S.length;simp [AtomSchedule.groupCount,base])
    (Nat.pow_le_pow_right (by decide) blocks) (show (3:ℕ) ≤ 3 from le_rfl) (old.trans cap)
    (nodeCols.trans (upto _ e (Nat.le_max_left ..))) cap (Nat.two_pow_pos _)
  have coeff:64≤ scale J 6:=(show 64≤2^6 by decide).trans
    (Nat.pow_le_pow_right (by decide) (by omega:6≤6*(J+1)))
  exact area.trans ((Nat.mul_le_mul_right _ coeff).trans_eq (by rw [scale_mul,scale_mul]))

/-- The replicated short words may use a tail-dependent exponent; this only decides
how far the scalar-table address lies below the common height. -/
theorem preflight_word_room (σ B:ℕ) (positive:0<B) (bought:2*(6*σ+11)≤B) :
    ∀ᶠ h₀:ℕ in Filter.atTop, let J₀:=Nat.log 2 h₀/(2*B)
      ∀ y:DescentTerminalPreflightSpace.Spec, (∀z∈y.shortFields,z≤ scale J₀ σ) →
        y.signedLanes=y.groups → 0<y.groups → y.registerBits≤h₀ := by
  filter_upwards [age_room B positive] with h₀ age
  let j:=Nat.log 2 h₀/(2*B)
  change 0<j ∧ 32*(2^j)^B≤h₀ at age
  dsimp only
  intro y sizes pitch groups
  have reg:=y.register_original (scale j σ) (Nat.two_pow_pos _) sizes pitch groups
  have exp:(6*σ+11)*(j+1)≤j*B:=by
    have h:=Nat.mul_le_mul_left (6*σ+11) (show j+1≤2*j by omega)
    have b:=Nat.mul_le_mul_left j bought;nlinarith only [h,b]
  have six:2048*(scale j σ)^6≤ scale j (6*σ+11):=by
    change 2^11*(2^(σ*(j+1)))^6≤2^((6*σ+11)*(j+1))
    rw [←pow_mul,←pow_add];apply Nat.pow_le_pow_right (by decide)
    nlinarith only [show 0≤11*j by omega]
  have paid:scale j (6*σ+11)≤(2^j)^B:=by
    rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) exp
  exact reg.trans (six.trans (paid.trans (by omega)))

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
