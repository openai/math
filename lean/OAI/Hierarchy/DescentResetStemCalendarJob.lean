import OAI.Hierarchy.DescentCanonicalFrontScene
import OAI.Hierarchy.DescentResetStemCalendarTemplate
import OAI.Hierarchy.DescentResetStemPhysicalJob

namespace OAI
/-! # The calendar and the reached graph run the same signed stem instruction stream -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook DescentDatedAddressBook.CandidateFront DescentDenseHostOrder DescentResetStemDateSignature
open DescentFallbackPeriod DescentPackedColony DescentResetStemPackedIssue ProtocolRAM
noncomputable section
set_option quotPrecheck false

structure StemWindow (degree lows cap : ℕ) where
  ports : Ports degree
  bank : Projected.Column lows cap→Bank

namespace StemWindow
def transfer {d l c d' l' c' : ℕ} (s : StemWindow d l c) (degree : d=d') (lows : l=l') (cap : c=c') :
    StemWindow d' l' c' := by
  subst d'; subst l'; subst c'; exact s

def castColumn {l c l' c' : ℕ} (lows : l=l') (cap : c=c') :
    Projected.Column l c→Projected.Column l' c'
  | .inl (face,x)=>.inl (face,x.cast lows)
  | .inr (slot,x)=>.inr (slot.cast (congrArg (2*·) cap),x.cast lows)

theorem transfer_bank {d l c d' l' c' : ℕ} (s : StemWindow d l c) (hd : d=d') (hl : l=l') (hc : c=c')
    (j : Projected.Column l' c') :
    (s.transfer hd hl hc).bank j=s.bank (castColumn hl.symm hc.symm j) :=by
  subst d'; subst l'; subst c'
  rcases j with ⟨j,lo⟩ | ⟨j,lo⟩ <;> rfl

theorem transfer_ports {d l c d' l' c' : ℕ} (s : StemWindow d l c) (hd : d=d') (hl : l=l') (hc : c=c') :
    HEq (s.transfer hd hl hc).ports s.ports :=by subst d'; subst l'; subst c'; rfl

theorem same_code {d l c d' l' c' : ℕ} (s : StemWindow d l c) (hd : d=d') (hl : l=l') (hc : c=c')
    (field hosts : ℕ) :
    HEq (DescentResetStemKey.parse d c field) (DescentResetStemKey.parse d' c' field) ∧
      HEq (side l c) (side l' c') ∧
      HEq (operands s.ports s.bank hosts)
        (operands (s.transfer hd hl hc).ports (s.transfer hd hl hc).bank hosts) :=by
  subst d'; subst l'; subst c'; exact ⟨HEq.rfl,HEq.rfl,HEq.rfl⟩
end StemWindow

private theorem masked_eq {K J S T : ℕ} {a : Fin (2*K)→Option (Fin S×Fin S)}
    {b : Fin (2*J)→Option (Fin T×Fin T)} (heads : K=J) (cells : S=T) (shape : HEq a b)
    (reg : DescentResetStemTemplatePorts.Banks) (num : Bank) (H : ℕ) :
    HEq (DescentResetStemMaskedPorts.ports reg num H a) (DescentResetStemMaskedPorts.ports reg num H b) :=by
  subst J; subst T; cases eq_of_heq shape; rfl

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : DescentCompiler.AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

open DescentColonies DescentSIMDLookup
local notation "A₀" => input.placement
local notation "u" => S.groupWidth k tail i
local notation "L₀" => 2^(u+k-B.terminals.commonDepth)
local notation "p" => S.hostSize i
local notation "np" => S.hostSize (i+1)
local notation "nG" => S.groupCount (i+1)
local notation "K₀" => 2*DescentFallbackShapeTable.rows (B.reset.k-B.terminals.commonDepth) (2^B.reset.n)
variable (M₀ M field bitsOut packet : ℕ) (calendar : List ℕ)
local notation "physical" => setupFront S ctl.board k tail i D f g M₀ M field bitsOut C packet calendar
local notation "cap₁" => (calendar.take i).prod*256
variable (paid : input.placement.cap=(calendar.take i).prod*256) (floor : ℕ)
  (older : EarlierBanks D k ((calendar.take i).prod*256) n)
local notation "oldCode" => calendarOriginals S ctl.board k tail i D f g M₀ M field bitsOut C packet calendar floor older
variable (flags number inverse : Bank)
local notation "chart" => (physical).fromOriginals floor oldCode flags number inverse
local notation "regs" => (physical).stemRegisters floor chart older.oldHub

theorem calendar_low_count : 2^k=L₀ :=by
  have rank : u+k-B.terminals.commonDepth=k :=by rw [B.commonDepth]; omega
  rw [rank]

def calendarWindow : StemWindow (A₀).degree L₀ (A₀).cap :=
  (⟨older.ports,older.window⟩ : StemWindow D (2^k) cap₁).transfer input.branch.symm (calendar_low_count B) paid.symm

theorem calendar_window_word (j : Projected.Column L₀ (A₀).cap) :
    (calendarWindow B calendar paid older).bank j=
      older.window (StemWindow.castColumn (calendar_low_count B).symm paid j) :=
  StemWindow.transfer_bank _ _ _ _ j

local notation "oldWin" => calendarWindow B calendar paid older

def reachedStemJob : StemJob where
  D:=(A₀).degree
  f:=field
  b:=bitsOut
  K:=K₀
  prev:=p
  H:=np
  groups:=nG
  blocks:=2^k
  M₀:=M₀
  M:=M
  Q:=DescentResetStemPackedIssue.count L₀ (A₀).cap
  parse:=DescentResetStemKey.parse (A₀).degree (A₀).cap field
  side:=side L₀ (A₀).cap
  src:=operands (oldWin).ports (oldWin).bank p
  ports:=DescentResetStemMaskedPorts.ports regs number p (stemTemplates B)

theorem calendar_job :
    (physical).job (chart).stems=reachedStemJob B M₀ M field bitsOut packet calendar paid floor older flags number inverse :=by
  let window : StemWindow D (2^k) cap₁:=⟨older.ports,older.window⟩
  have matchCode:=window.same_code input.branch.symm (calendar_low_count B) paid.symm field p
  have queries : DescentResetStemPackedIssue.count (2^k) cap₁=DescentResetStemPackedIssue.count L₀ (A₀).cap:=congrArg₂ DescentResetStemPackedIssue.count (calendar_low_count B) paid.symm
  exact StemJob.eq_of_fields _ _ input.branch.symm rfl rfl (calendar_heads B) rfl rfl rfl rfl rfl rfl queries
    matchCode.1 matchCode.2.1 matchCode.2.2
    (masked_eq (calendar_heads B) (calendar_palette B) (calendar_stemTemplates B) regs number p)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
