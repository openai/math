import OAI.Hierarchy.DescentTerminalPublicRows
import OAI.Hierarchy.DescentNamedNormalizedChart
import OAI.Hierarchy.DescentNamedNativeCaps
import OAI.Hierarchy.DescentTerminalIntegralFrontier

namespace OAI
/-! # The common row purchase for the physically named normalized histories -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalGraphVolume DescentTerminalGraphPositions DescentTerminalBinPack CorrectionBatch
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
local notation "s" => S.firstWidth G.b p
local notation "E" => Fintype.card (Port P X.width)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "K" => 258*reentryRate h C+reentryExteriorRate h C 256 Ht
local notation "d" => S.copies*s

variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0<p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "run" => (cert).choose
local notation "last" => Epochs.finish G _ _ run
variable (c : (Epochs.finish G _ _ (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose).Choice)
local notation "b" => issued X G S ordinary reset branch positive room shorten c
local notation "world" => (last).state c
local notation "net" => (world).graph
local notation "total" => terminalWireBudget X G S p n h C f g

theorem issued_wire_mass : (∑e,(net).width e) ≤ total := by
  have certRows:=((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec
  have hsum:=Finset.sum_add_sum_compl (world).core (net).width
  change (world).liveWidth+(world).tetherWidth=∑e,(net).width e at hsum
  rw [←hsum]
  exact integralFrontier_bound (Nat.two_pow_pos _) K (Nat.le_ceil K)
    (by simpa only [Nat.cast_mul] using certRows.2.2.2.2) certRows.2.2.2.1

theorem issued_volume {q : ℕ} (hq : 0<q) :
    (∑e,(net).width e) ≤ terminalRawRows X G S p q n h C f g*(q*p) :=
  (issued_wire_mass X G S ordinary reset branch positive room shorten c).trans
    (by simpa only [terminalRawRows, Nat.mul_comm (q*p)] using CallPool.count_le_batches_mul total (q*p) (Nat.mul_pos hq positive))

theorem issued_purchase (q W : ℕ) (hq : 0<q) (hW : 0<W)
    (O : Order net (S.hostSize S.length) p) (loc : O.home=(b).target.home) :
    purchased W (fun i=>(O.site i).rows q) ≤ terminalPool X G S p q W n h C f g := by
  have cable (e : (net).Edge) : p ∣ (net).width e := by
    have he:=(b).target.valid.divides e
    rw [(b).target.grain] at he
    exact dvd_trans (dvd_mul_right p G.b) he
  have hs : p ∣ s := by
    unfold AtomSchedule.firstWidth AtomSchedule.grainAt
    exact ⟨G.b^(S.rounds*S.height-S.ordinaryDone 0)*G.b,by ac_rfl⟩
  have pins (z : (Σ _ : Fin S.copies,Fin E)) : p ∣ (fun _ : (Σ _ : Fin S.copies,Fin E)=>s*1) z := by
    simpa using hs
  have ext : (∑_ : (Σ _ : Fin S.copies,Fin E),s*1) ≤ d*E := by
    simp [Fintype.card_sigma,Nat.mul_assoc,Nat.mul_comm]
  have groupCount:=(b).target.terminal_groups O loc
  rw [(b).target.branch] at groupCount
  exact Nat.mul_le_mul_right W (fixed_bins O q W 3 total (d*E) positive hq hW cable pins
    (issued_wire_mass X G S ordinary reset branch positive room shorten c) ext groupCount)

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
