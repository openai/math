import OAI.Hierarchy.DescentCalendarRetainedSensors
import OAI.Hierarchy.DescentRetainedIssuedSelectors

namespace OAI
/-! Original reset owner bits and prior-grain comparisons at a registered retained caller. -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentResetHostSize DescentSIMDLookup DescentSharedBookScan DescentResetLocalRoster
open DescentRotorWindowArchive DescentFallbackPeriod DescentFallbackPeriod.Projected DescentContactSenderDate
open DescentPaidResidentCount.Reset DescentOldContactSender DescentPacking DescentRetainedRangeDigits
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z w hist D n h C f g cut tail : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl) (M field : ℕ)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "c" => (T).commonDepth
local notation "r" => (Z).k-c
local notation "Y" => 2^(Z).n
local notation "H" => S.hostSize i
local notation "dep" => GroupStage.depthBound D n f g
local notation "host" => input.vertex.trans (Fin.castLEEmb input.valid.host)
local notation "slots" => congrArg (fun t=>2^(t-c)) B.keyWidth
variable {bw N K R hm l tiny : ℕ}
    (rc : Receiver (A).degree (A).cap N (Z).n r c H (S.groupCount i) K R M hm l tiny field dep bw)
    (book : RootBook (Z).n r (A).degree (2^r) (A).cap field) (space : rc.PreparedFits book) (mem : Memory bw)
    (hdr : OriginalHeader B input.valid.host rc book mem) (x : OriginalArrays B input.valid.host field)
local notation "view" => root_snapshot B input.valid.host rc book space mem hdr x


private theorem transported_digit {D₁ D₂ L₁ L₂ C₁ C₂ F₁ F₂:ℕ}
    (degree:D₁=D₂) (donors:L₁=L₂) (cap:C₁=C₂) (field:F₁=F₂)
    (data:Fin (DescentRotorWindowArchive.count D₂ L₂ C₂)→Cell F₂) (packed:Cell (F₁*DescentRotorWindowArchive.count D₁ L₁ C₁))
    (same:packed.val=(encode F₂ _ data).val) (d j:Fin L₁) :
    (((encode F₁ _).symm packed) (DescentRotorWindowArchive.ix (.inl (.inl (.inl d))))).val=
      (data (DescentRotorWindowArchive.ix (.inl (.inl (.inl (d.cast donors)))))).val ∧
    (((encode F₁ _).symm packed) (DescentRotorWindowArchive.ix (.inr (.inl (d,j))))).val=
      (data (DescentRotorWindowArchive.ix (.inr (.inl (d.cast donors,j.cast donors))))).val:=by
  subst D₂;subst L₂;subst C₂;subst F₂
  rw [show packed=encode _ _ data from Fin.ext same,Equiv.symm_apply_apply]
  exact ⟨rfl,rfl⟩

variable (chart:DescentResetOperandSetup.Chart) (which:chart.seven.control.Targets)
  (windows:chart.seven.Packets) (shp:Fin chart.placement.shapes)
  (carrier:Fin chart.retained.hosts) (coarse:Fin chart.retained.grouped)
  (v:Fin H) (hi:Block c) (code:ℕ) (target:which shp=some code)
  (degree:chart.seven.degree=(A).degree) (nd:chart.retained.donors=2^r)
  (capacity:chart.seven.capacity=(A).cap) (width:chart.seven.packetBits=field)
  (same:(windows carrier coarse).val=(encode field _ (calendar_sender_matrix B M field rc book space mem hdr x v hi)).val)
  (positive:0<field) (fit:∀lo,x.stencil v hi lo<2^field)
local notation:max "lo" d:arg => (((d:Fin chart.retained.donors).cast nd).cast slots)
local notation "dim" => B.frame.enough.trans (Nat.sub_le ..)
local notation:max "old" d:arg => (DescentColonies.rearrange B.frame.basis).symm (DescentIssuedFallbackPanel.join dim hi (lo d))

include target same positive fit degree capacity width in
theorem registered_window_selectors :
    ownerAt chart which windows shp carrier coarse=(fun j=>decide (x.stencil v hi (lo j)/2=code)) ∧
      priorAt chart windows carrier coarse=(fun d j=>decide (old d<old j)):=by
  rw [calendar_sender_matrix_eq] at same
  have read:=fun d j=>transported_digit degree nd capacity width _ (windows carrier coarse) same d j
  constructor
  · funext j
    unfold ownerAt
    rw [target]
    erw [(read j j).1]
    simp only [RootSources.paddedRow,Equiv.symm_apply_apply,DescentRotorWindowArchive.observed,
      DescentFallbackPeriod.inputs,Fin.val_natCast,Nat.mod_eq_of_lt (fit _)]
    simp [eq_comm]
  · funext d j
    unfold priorAt
    erw [(read d j).2]
    change _=GroupStage.previousDigit B.frame.basis dim hi (lo d) (lo j)
    simp only [RootSources.paddedRow,DescentRotorWindowArchive.observed,Equiv.symm_apply_apply]
    have boolRead (flag : Bool) : decide ((flag.toNat : Cell field).val ≠ 0) = flag := by
      cases flag <;> simp [Nat.mod_eq_of_lt (Nat.one_lt_two_pow positive.ne')]
    exact boolRead _

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
