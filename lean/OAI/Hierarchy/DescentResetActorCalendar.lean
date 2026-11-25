import OAI.Hierarchy.DescentDatedActorSetup
import OAI.Hierarchy.DescentPhysicalResetActors
import OAI.Hierarchy.DescentResetActorPlanes
import OAI.Hierarchy.DescentActorHeaderControl
import OAI.Hierarchy.DescentResetMiddleCalendar

namespace OAI
/-! The actor controller, its roster order and both opcode columns are public at the reset date. -/
namespace Hierarchy.DescentDatedAddressBook.ActorSetup
open DescentCompiler DescentSixParty DescentSixParty.ResetInput DescentDenseHostOrder DescentCommonHost DescentContacts
open DescentActorRaster DescentSixParty.ResetInput.SourceFrame ProtocolRAM
noncomputable section
open scoped Classical
variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)

def levelBits (width D Ht : ℕ) :=Nat.clog 2 (max width (Nat.clog 2 (D*2^Ht))+2)

def fromCalendar (S : AtomSchedule) (k tail age D e Ht : ℕ) : ActorSetup :=
  let c:=S.groupWidth k tail age
  let H:=S.hostSize age
  ⟨H,c,k,2^e,2*k+n+2,levelBits (c+k) D Ht,(roster board k Ht).card,
    DescentSharedBookScan.width k (2^n) D,c+k,D*2^Ht⟩

def shapeIndex (k Ht : ℕ) : ↥(roster board k Ht)≃Fin (roster board k Ht).card :=
  Equiv.ofBijective (localRank board k Ht) ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨(localRank board k Ht).injective,by simp⟩)
def shapeAt (k Ht : ℕ) (j : Fin (roster board k Ht).card) :=((shapeIndex board k Ht).symm j).val

def calendarInputs (S : AtomSchedule) (k tail age D e Ht : ℕ) (count depths : Bank)
    (prior : DescentSharedBookScan.Chart) (st : Expr) : (fromCalendar board S k tail age D e Ht).Inputs :=
  ⟨count,depths,prior,D,2^Ht,fun j=>headerControl k D (shapeAt board k Ht j),
    fun j=>opcode k (shapeAt board k Ht j),st⟩

theorem header_fits {width D Ht x : ℕ}
    (h : x≤width ∨ x≤Nat.clog 2 (D*2^Ht)) : x+1<2^(levelBits width D Ht) := by
  have maxBound:x≤ max width (Nat.clog 2 (D*2^Ht)):=h.elim (fun a=>a.trans (le_max_left ..)) (fun a=>a.trans (le_max_right ..))
  exact (by omega : x+1< max width (Nat.clog 2 (D*2^Ht))+2).trans_le (Nat.le_pow_clog (by decide) _)

open DescentChosenRouter DescentResetAttachments
open DescentPlainTerminal DescentColonies DescentRelativeContacts DescentRosterOrder DescentTreePrefixIntervals

theorem measured_level {F P V : Type} [Field F] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {price eps : ℝ} {hh C Ht g : ℕ}
    {Z : ResetInput W price eps hh C Ht} {T : Terminals Z} {pos : W.graph.Site→V} {ix : W.graph.Site→DescentColonies.Block k}
    {hub : V→Bool} (frame : SourceFrame Z T pos ix hub g) (f D : ℕ) (near : V→Fin D→Option V)
    (bound : ∀v,Z.placement.b (frame.host v)≤k) (v : V)
    (q : Node Unit (Unit×Endpoint (2^Z.n)) (DescentCommonPalette.rotor Z.graph).Site) :
    levelAt frame f near v q+1<2^(levelBits k D Ht) := by
  apply header_fits
  cases q with
  | good => exact .inl ((Nat.sub_le ..).trans (bound v))
  | trunk => exact .inl (Nat.zero_le _)
  | fall s z p =>
    rcases z with ⟨u,z⟩
    simp only [levelAt]
    split
    · right
      unfold heightAt
      apply Nat.clog_mono_right
      exact (Finset.card_filter_le ..).trans (by simp)
    · exact .inl (Nat.zero_le _)

end
end Hierarchy.DescentDatedAddressBook.ActorSetup

end OAI
