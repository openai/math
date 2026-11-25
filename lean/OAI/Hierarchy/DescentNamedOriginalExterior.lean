import OAI.Hierarchy.DescentNamedLeafOrder
import OAI.Hierarchy.DescentTerminalOriginalExterior

namespace OAI
/-! # Reading the original independently copied input from the final named exterior flight -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionFrame
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
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


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))


/-- Transport the outer assignment along the actual equality of copy counts.
Port widths and the ambient product cardinality change together. -/
def copyInput (X : Approximation F cp P) (t : ℕ) {m n : ℕ} (eqn : m=n)
    (x : Port ((m*t)*P) (copiesWidth (m*t) X.width) → Bool) :
    Port ((n*t)*P) (copiesWidth (n*t) X.width) → Bool := eqn ▸ x

omit [Field F] in
theorem copyInput_back (X : Approximation F cp P) (t : ℕ) {m n : ℕ} (eqn : m=n)
    (x : Port ((m*t)*P) (copiesWidth (m*t) X.width) → Bool) :
    copyInput X t eqn.symm (copyInput X t eqn x) = x := by cases eqn; rfl

omit [Field F] in
private theorem package_copy (X : Approximation F cp P) (t : ℕ) {old physical : ℕ}
    (eqn : old=physical) (x : Port ((physical*t)*P) (copiesWidth (physical*t) X.width) → Bool)
    (a : Σ _:Fin old,Fin (Fintype.card (Port P X.width))) (d : Fin t) :
    packagePins X physical t x ⟨Fin.cast eqn a.1,a.2⟩ (finProdFinEquiv (d,(0:Fin 1))) =
      packagePins X old t (copyInput X t eqn.symm x) a (finProdFinEquiv (d,(0:Fin 1))) := by
  cases eqn
  rfl

local notation "power" => NativeBranch.copy_power S (radix:=radix) base width
local notation "originalPin" => NativeBranch.rawPin S (X:=X) (radix:=radix) base width
local notation "M" => publicLayout X G S b hp base width
local notation "rows" => (originalPin).symm.trans (chart (j:=j) (r:=rest) M)
local notation "physical" => 2^(j+(j+rest))
local notation "count" => E*2^(j+rest)

theorem public_flight_read (outer : Port ((physical*s)*P) (copiesWidth (physical*s) X.width) → Bool)
    (hidden : Hidden E j rest s → Bool)
    (valid : ∀a, stagesOK (M a) (publicRows X outer a) (projected hidden false a) (projected hidden true a))
    (z : Σ _:Fin S.copies,Fin E) (d : Fin s) :
    wordBits (2^j*s) (flight X M hidden (rows z).1) (finProdFinEquiv ((rows z).2,d)) =
      packagePins X S.copies s (copyInput X s (power).symm outer) z (finProdFinEquiv (d,(0:Fin 1))) :=
  (flight_read X M outer hidden valid ((originalPin).symm z) d).trans (package_copy X s power outer z d)

theorem public_flight_of_world (outer : Port ((S.copies*s)*P) (copiesWidth (S.copies*s) X.width) → Bool)
    (hidden : Hidden E j rest s → Bool)
    (valid : ∀a, stagesOK (M a) (publicRows X (copyInput X s power outer) a)
      (projected hidden false a) (projected hidden true a))
    (z : Σ _:Fin S.copies,Fin E) (d : Fin s) :
    wordBits (2^j*s) (flight X M hidden (rows z).1) (finProdFinEquiv ((rows z).2,d)) =
      packagePins X S.copies s outer z (finProdFinEquiv (d,(0:Fin 1))) := by
  simpa only [copyInput_back] using
    public_flight_read X G S b hp base width (copyInput X s power outer) hidden valid z d

include radix base width in
theorem public_volume :
    (∑ _z : (Σ _:Fin S.copies,Fin E),s*1) = count*(2^j*s) := by
  simp [Fintype.card_sigma,power,pow_add]; ring

private theorem stream_cast {Z : Type} [Fintype Z] (code : Z ↪ ℕ) {m n : ℕ} (eqn : m = n)
    (x : Z → Fin m → Bool) :
    publicStream (bits:=fun _:Z => m) code x =
      publicStream (bits:=fun _:Z => n) code (fun z k => x z (Fin.cast eqn.symm k)) := by
  cases eqn
  rfl

/-- Each home-major row of the graph's actual width-(s*1) exterior field
is the genuine complete word at the inverse stable-permutation index. -/
theorem public_original_dense (outer : Port ((physical*s)*P) (copiesWidth (physical*s) X.width) → Bool)
    (hidden : Hidden E j rest s → Bool)
    (valid : ∀a, stagesOK (M a) (publicRows X outer a) (projected hidden false a) (projected hidden true a))
    (i : Fin count) :
    dense (2^j*s) (publicStream (leafExternal X G S b hp base width)
      (packagePins X S.copies s (copyInput X s (power).symm outer))) i.val =
      flight X M hidden ((Computability.BorderVNP.FragmentBucket.dest (publicHost X G S b hp base width)).symm i) := by
  let ext := leafExternal X G S b hp base width
  let world := packagePins X S.copies s (copyInput X s (power).symm outer)
  have coordinate (d : Fin s) : Fin.cast (Nat.mul_one s).symm d = finProdFinEquiv (d,(0:Fin 1)) := by
    apply Fin.ext
    change d.val=0+1*d.val
    omega
  change dense _ (publicStream ext world) i.val = _
  rw [stream_cast ext (Nat.mul_one s) world]
  simp_rw [coordinate]
  exact dense_value rows (publicHost X G S b hp base width) _ (flight X M hidden)
    (public_flight_read X G S b hp base width outer hidden valid) i

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
