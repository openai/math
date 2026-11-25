import OAI.Hierarchy.DescentNamedHistoryShape
import OAI.Hierarchy.DescentNamedPrivateArchive
import OAI.Hierarchy.DescentPrivateMeterClock

namespace OAI
/-! # A single public word holds the complete named branch's private exponent -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentKernelHistory DescentBundleHistory Catalyst
open DescentTerminalObservedExponent DescentHistoryOrder
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F]
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
local notation "A" => Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp
local notation "N" => ((Epochs.finish G hu he r).state c).graph

/-- The public seed coefficient has a single exponent, on the same chosen named history as the matrix and local tables. -/
def unitExponent (one : 1≤R) (_ : Unit) : ℕ :=
  deadCount hp N (A).bit.recipe (bundleShape X G S b hp one).sites

theorem unitExponent_le (one : 1≤R) :
    unitExponent X G S b hp one ()≤NativeBranch.privateMax G S p := by
  have sum:=partition hp N (A).bit.recipe (bundleShape X G S b hp one).sites
  have maxVol : DescentTerminalObservedExponent.volume N (A).bit.recipe≤NativeBranch.privateMax G S p:=private_max X G S b hp
  unfold unitExponent
  omega

theorem unitExponent_lt (one : 1≤R) {wb : ℕ} (room : Nat.log 2 (NativeBranch.privateMax G S p)+1≤wb) :
    unitExponent X G S b hp one ()<2^wb :=
  (unitExponent_le X G S b hp one).trans_lt
    ((Nat.lt_pow_succ_log_self (by decide : 1<2) _).trans_le
      (Nat.pow_le_pow_right (by decide : 0<2) room))

/-- The coefficient of the machine word width is fixed before the input height is chosen. -/
theorem unitExponent_date (one : 1≤R) {t cutF cutG reset τ M bits B : ℕ}
    (positive : 0<bits) (menu : 0<B)
    (chart : S=stageNumbers G t (Nat.log 2 bits/(2*B)) cutF cutG reset M
      (τ*(Nat.log 2 bits/(2*B)+1))) (sites : M≤2^(2*bits)) (payload : p≤bits) :
    unitExponent X G S b hp one ()<2^(NativeBranch.clockRate G t cutF cutG reset τ*bits) := by
  apply unitExponent_lt X G S b hp one
  rw [chart]
  exact NativeBranch.private_clock_chosen G t cutF cutG reset M τ p bits B positive menu sites payload

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
