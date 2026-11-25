import OAI.Hierarchy.DescentTerminalFrozenPointerWords
import OAI.Hierarchy.DescentTerminalPointerWordRoom
import OAI.Hierarchy.DescentSignedCableCodec
import OAI.Hierarchy.DescentOccurrenceAllowance
import OAI.Hierarchy.DescentTerminalSeedStampWidth

namespace OAI
/-! # The actual last-stage signed, frozen and local pointer widths on the same named branch -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open CorrectionBatch DescentKernelHistory
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p : ℕ}
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k} {R : ℕ}
    {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S radix R r c) (hp : 0<p)

open DescentGL DescentColonies DescentExterior PinCohorts
local notation "SeedPin" => Σ _ : Fin S.copies, Fin (Fintype.card (Port P X.width))


namespace Branch
variable {tail : ℕ} (base : S.baseGroups=2^tail)
local notation "trace" => pinSpine X G S b hp base
local notation "portCount" => Fintype.card (Port P X.width)
local notation "H" => S.hostSize S.length
local notation "N" => ((Epochs.finish G hu he r).state c).graph
local notation "A" => b.target.placement
local notation "f" => b.path.frozen
local notation "Cohort" => Fin (portCount*2^f)



local notation "homes" => cohortHome X G S b hp base
local notation "initialBits" => S.groupWidth k tail 0+k
local notation "old" => b.origin.source
local notation "frozen" => (fun t:Cohort=>(finProdFinEquiv.symm t : Fin portCount×Fin (2^f)).2)
local notation "codeAt" => DescentTerminalFrozenRoster.book homes frozen

local notation "T_" => S.epochPower
local notation "cap_" => 2^(8+S.capGain*S.length)
open DescentTerminalPointerDigits DescentSharedCableNames

theorem signed_width (v : ℕ) (positive : 0<S.height)
    (reserve : S.localCapacityExponent+3≤v) :
    DescentSignedCableCodec.width (A).degree (A).cap ≤ (2*T_)^v := by
  let C:=T_^S.localCapacityExponent
  have Tpos : 0<T_:=Nat.two_pow_pos _
  have one : 1≤C:=Nat.one_le_pow _ _ Tpos
  have maxCap : (A).cap≤C:=S.local_capacity positive le_rfl b.target.valid.capacity
  have bitsCap : Packed.bits (A).cap≤C :=by
    apply le_trans _ maxCap
    apply (Nat.clog_le_iff_le_pow (by decide)).2
    exact Nat.lt_two_pow_self
  have neighbor : Packed.bits (A).degree=2:=by rw [b.target.branch];decide
  have up : C≤(2*T_)^S.localCapacityExponent:=Nat.pow_le_pow_left (by omega) _
  have eight : 8≤(2*T_)^3:=Nat.pow_le_pow_left (by omega : 2≤2*T_) 3
  calc
    _ ≤ 8*C :=by unfold DescentSignedCableCodec.width;rw [neighbor];omega
    _ ≤ (2*T_)^S.localCapacityExponent*(2*T_)^3:=by
      rw [Nat.mul_comm 8 C];exact Nat.mul_le_mul up eight
    _ ≤ _:=by rw [←pow_add];exact Nat.pow_le_pow_right (by omega) reserve

theorem frozen_width (positive : 0<S.height) (J t κ τ : ℕ)
    (dates:S.length=(t+1)*J) (active:k≤κ*(J+1)) (res : tail=τ*(J+1)) :
    initialBits≤(τ+κ*(t+2))*(J+1)^2 ∧
    f+1≤(τ+κ*(t+2))*(J+1)^2+1 ∧
    ∀v:Fin H, Computability.BorderVNP.FragmentBucket.count homes v≤T_^S.localCapacityExponent :=by
  have stamp:=S.stamp_width J t k τ κ dates active
  change S.groupWidth k (τ*(J+1)) 0+k≤_ at stamp
  rw [←res] at stamp
  have alive:=(trace).width
  exact ⟨stamp,by omega,fun v=>(cohort_cap X G S b hp base v).trans <|
    S.local_capacity positive (i:=S.length) le_rfl le_rfl⟩

end Branch
end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
