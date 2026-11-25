import OAI.Hierarchy.DescentCalendarMatrixOrigins
import OAI.Hierarchy.DescentCalendarPeerRegisters
import OAI.Hierarchy.DescentResetPrefixRoom

namespace OAI
/-! # The original signed and stencil windows at the calendar peer program -/
namespace Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks
open DescentSixParty.ClosedReset.Window DescentFallbackPeriod DescentFallbackPeriod.Projected
noncomputable section

theorem original_window {d r c n D R C N l : ℕ} (hd : d=D) (hr : r=R)
    (hc : c=C) (hn : n=N) (wide : 2^R=l) (x : EarlierBanks d r c n) :
    let lifted:=castTo hd hr hc hn x
    let back:=(⟨lifted.ports,lifted.window⟩ : StemWindow D (2^R) C).transfer hd.symm wide hc.symm
    back.ports=x.ports ∧ ∀j,back.bank j=x.window
      (StemWindow.castColumn (wide.symm.trans (congrArg (fun u=>2^u) hr.symm)) rfl j) := by
  subst D; subst R; subst C; subst N; subst l
  refine ⟨rfl,?_⟩
  rintro (⟨s,i⟩|⟨p,i⟩) <;> rfl
end
end Hierarchy.DescentDatedAddressBook.CandidateFront.EarlierBanks

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentDatedAddressBook CandidateFront DescentCompiler DescentColonies DescentDenseHostOrder
open DescentPackedColony DescentPaidResidentCount.Reset DescentFallbackPeriod DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPacking.PackedMatch.Local.Stage DescentResetLocalRoster
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] {d : ℕ} {b : P→ℕ} {W : MarkedWorld F d P b}
    {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
    {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
    (B : ClosedReset input ctl) {M field : ℕ} (calendar : List ℕ)
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "cc" => B.terminals.commonDepth
local notation "H" => S.hostSize i
local notation "J" => 2^cc
local notation "cap" => (A).cap
local notation "deg" => (A).degree
local notation "r" => (Z).k-cc
local notation "Ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r Ht).card
local notation "axis" => congrArg (fun u=>2^(u-cc)) B.keyWidth
variable (paid : cap=(calendar.take i).prod*256) {w N K R hm l tiny : ℕ}
    (rc : Receiver deg cap N (Z).n r cc H (S.groupCount i) K R M hm l tiny field Ht w)
    (book : RootBook (Z).n r deg (2^r) cap field) (space : rc.PreparedFits book) (mem : Memory w)
    (src : RootSources deg (2^r) cap) (oldId oldHub : Bank) (directory : ℕ)
    (actorBank : Bank) (before : Memory w)
local notation "dir" => (⟨directory,H,shelf,chunks J M⟩ : DescentResetNewActorDirectory.Layout)
local notation "orig" => EarlierBanks.fromRoot rc book src oldId oldHub dir actorBank
local notation "prior" => EarlierBanks.castTo input.branch (calendar_residual B) paid B.dimension orig
local notation "win" => calendarWindow B calendar paid prior
local notation "issued" => bankAt rc.stencil rc.tapped tiny deg rc.signedEnd H J M
local notation "middle" => rc.preparedMid book space mem
local notation "initial" => (dir).result actorBank before
local notation "floor" => (dir).endAddress

theorem calendar_original_window :
    (win).ports=src.peers ∧ ∀j,(win).bank j=issued (StemWindow.castColumn (axis).symm rfl j) :=
  EarlierBanks.original_window input.branch (calendar_residual B) paid B.dimension (calendar_low_count B) orig

/-- Preserve the very same projected code, tagged code, signed words and
original roster through the root programs and actor directory. -/
theorem calendar_window_receipt (x : OriginalArrays B input.valid.host field)
    (separated : rc.preparedEnd book ≤ directory)
    (keep : ∀a,a < rc.preparedEnd book → before a=rc.preparedImage book space mem a)
    (actorFit : actorBank.Fits w directory) (chunksFit : chunks J M ≤ 2^w)
    (last : floor < 2^w)
    (reachable : ∀(a : Fin (2^r)),Accessible src.peers (issued (.inl (1,a))) H J M w (rc.headerEnd book))
    (rosterWords : Mounted src.peers x.peers middle J M)
    (sites : ∀a,Reads (issued (.inl (0,a))) (fun v hi=>(x.stencil v hi (a.cast axis):Cell field)) M middle)
    (tagged : ∀a,Reads (issued (.inl (1,a))) (fun v hi=>((x.stencil v hi (a.cast axis)+1:ℕ):Cell field)) M middle)
    (marks : ∀j a,Reads (issued (.inr (j,a))) (fun v hi=>
      ((DescentSignedCableCodec.encode (x.marks v hi (a.cast axis) j)).val:Cell field)) M middle) :
    (∀j,((win).bank j).Fits w floor) ∧ (∀j,H*chunks J M ≤ ((win).bank j).size) ∧
    (∀a,Accessible (win).ports ((win).bank (.inl (1,a))) H J M w floor) ∧
    Mounted (win).ports x.peers initial J M ∧
    (∀a,Reads ((win).bank (.inl (0,a))) (fun v hi=>(x.stencil v hi a:Cell field)) M initial) ∧
    (∀a,Reads ((win).bank (.inl (1,a))) (fun v hi=>((x.stencil v hi a+1:ℕ):Cell field)) M initial) ∧
    ∀j a,Reads ((win).bank (.inr (j,a))) (fun v hi=>
      ((DescentSignedCableCodec.encode (x.marks v hi a j)).val:Cell field)) M initial := by
  obtain ⟨ports,banks⟩:=calendar_original_window B calendar paid rc book src oldId oldHub directory actorBank
  obtain ⟨c₁,c₂,c₃⟩:=book.limits rc.projectionEnd H J M
  have proj : rc.projectionEnd ≤ rc.headerEnd book:=c₁.trans (c₂.trans c₃)
  have head : rc.headerEnd book ≤ rc.preparedEnd book:=Nat.le_add_right ..
  have cut : directory ≤ floor:=Nat.le_add_right ..
  have grow := head.trans (separated.trans cut)
  have after := (dir).evaluate actorBank before actorFit chunksFit last
  have held (a : ℕ) (lo : a < rc.headerEnd book) : initial a=middle a :=
    (after.2.2 a (.inl (lo.trans_le (head.trans separated)))).trans
      ((keep a (lo.trans_le head)).trans (rc.before_header book space mem a lo))
  have fits (j : Column (2^r) cap) := rc.window_fits j (proj.trans_lt (grow.trans_lt last))
  have rows (j : Column (2^r) cap) : H*chunks J M ≤ (issued j).size:=Nat.le_pow_clog (by decide) _
  have liftWords {j : Column (2^r) cap} {v : Fin H→Fin J→Cell field}
      (read : Reads (issued j) v M middle) : Reads (issued j) v M initial :=
    Chooser.reads_before (issued j) v middle initial read held (Chooser.bank_before (fits j) proj) (rows j)
  refine ⟨fun j=>?_,fun j=>?_,fun a=>?_,?_,fun a=>?_,fun a=>?_,fun j a=>?_⟩
  · rw [banks]
    exact Chooser.bank_before (fits _) (proj.trans grow)
  · rw [banks]
    exact rows _
  · rw [ports,banks]
    exact Chooser.accessible_before _ _ (reachable (a.cast (axis).symm)) grow
  · rw [ports]
    exact Chooser.mounted_before _ _ _ middle initial rosterWords held (reachable 0)
  · rw [banks]
    simpa only [StemWindow.castColumn,Fin.cast_cast,Fin.cast_refl,id_eq] using liftWords (sites (a.cast (axis).symm))
  · rw [banks]
    simpa only [StemWindow.castColumn,Fin.cast_cast,Fin.cast_refl,id_eq] using liftWords (tagged (a.cast (axis).symm))
  · rw [banks]
    simpa only [StemWindow.castColumn,Fin.cast_cast,Fin.cast_refl,id_eq] using liftWords (marks j (a.cast (axis).symm))

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
