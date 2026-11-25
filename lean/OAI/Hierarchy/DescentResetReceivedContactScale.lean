import OAI.Hierarchy.DescentContactDonorScale
import OAI.Hierarchy.DescentContactProbeScale
import OAI.Hierarchy.DescentResetReceivedTariff
import OAI.Hierarchy.DescentResetReceiverPitch

namespace OAI
/-! # The two contact sections in the selected date's native receipt -/
namespace Hierarchy.DescentDatedAddressBook.ResetOutput
open DescentSIMDLookup DescentContactCostUnit
noncomputable section
variable (v : ResetOutput)
local notation "A" => v.front.donor
local notation "C" => v.front.contact
local notation "marker" => DescentContactPreROM.Layout.markerLimit 7
def contactFactor (U : ℕ) := ((A).clockFactor U+7*(A).nameFactor U)+
  ((C).clockFactor ((C).oldLimit U) marker+7*(C).nameFactor ((C).oldLimit U) marker)
def contactWork (base U : ℕ) :=
  let d:=v.front.donorStart base
  let a:=v.front.contactLayout base
  ((A).fee d U+7*(A).size d U)+(a.clockBound (a.oldLimit U) marker+7*a.size (a.oldLimit U) marker)

/-- Only the original host racks, their physical SIMD words and the common dictionary enter the bill. -/
def contactArea (h : ℕ) := 1+((A).hosts+(A).hosts*chunks (A).groups (A).batch)+2^(h/2)

theorem contact_work (h base U : ℕ) (positive : 0<(A).batch)
    (host : (C).hosts=(A).hosts) (groups : (C).groups=(A).groups) (batch : (C).batch=(A).batch)
    (lookup : ∀t∈v.rootUnits,t*(A).batch≤h/2) :
    v.contactWork base U≤v.contactFactor U*v.contactArea h := by
  let T:=v.contactArea h
  have parts (a b c : ℕ) : a ≤ 1+(a+b)+c ∧ b ≤ 1+(a+b)+c ∧ c ≤ 1+(a+b)+c := by omega
  obtain ⟨hs,rs,ps⟩ := parts (A).hosts ((A).hosts*chunks (A).groups (A).batch) (2^(h/2))
  have previous:=(A).donor_scale (v.front.donorStart base) U h T hs rs ps positive
    (lookup _ (by simp [rootUnits])) (lookup _ (by simp [rootUnits])) (lookup _ (by simp [rootUnits]))
    (lookup _ (by simp [rootUnits])) (lookup _ (by simp [rootUnits])) (lookup _ (by simp [rootUnits]))
  let a:=v.front.contactLayout base
  have sh : a.hosts=(C).hosts:=rfl
  have sg : a.groups=(C).groups:=rfl
  have sb : a.batch=(C).batch:=rfl
  have host' : a.hosts≤T:=by rwa [sh,host]
  have rows' : a.hosts*chunks a.groups a.batch≤T:=by rwa [sh,sg,sb,host,groups,batch]
  have key (t : ℕ) (live : t∈v.rootUnits) : t*a.batch≤h/2:=by rw [sb,batch];exact lookup _ live
  have next:=a.contact_scale (a.oldLimit U) marker h T host' rows' ps
    (key _ (by change (C).fieldBits*(C).oldFields+(C).fieldBits∈v.rootUnits;simp [rootUnits]))
    (key _ (by change (C).viewBits+(C).viewBits∈v.rootUnits;simp [rootUnits]))
    (key _ (by change (C).fieldBits*8+(C).fieldBits∈v.rootUnits;simp [rootUnits]))
  exact sum previous next

end
end Hierarchy.DescentDatedAddressBook.ResetOutput

namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPackedWalsh ProtocolRAM
noncomputable section
variable {F : Type} [Field F] {n d : ℕ} (G : PoweredGadget F) (S : AtomSchedule)
    (board : NonlinearExpanders.Graph n d) (k tail age p f g drift degree h : ℕ)
    (previous nextM C packet oldLanes primitiveLanes printedBits : ℕ) (venue : StageVenueTail.Date)
    (addr : ℕ→ℕ→Bank) (roster : Bank)
local notation "prev" => ResetOutput.Prior.atDate G S age p drift oldLanes primitiveLanes printedBits venue
local notation "fields" => ResetOutput.fromBoard G S board k tail age p f g drift degree h 0 previous 1 nextM C packet prev 0
local notation "issued" => selected G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits venue addr roster
local notation "cut" => receiverCut G S board k tail age p f g drift degree h previous nextM C packet oldLanes primitiveLanes printedBits venue

theorem selected_contact_work (floor base U : ℕ) (short : 8*(fields).groupWidth≤h) :
    let v:=(issued floor).successor
    v.contactWork base U≤v.contactFactor U*v.contactArea h := by
  let v:=(issued floor).successor
  apply v.contact_work h base U (show 0<2^cut from Nat.two_pow_pos _) rfl rfl rfl
  intro t live
  exact selected_room G S board k tail age p f g drift degree h previous nextM C packet oldLanes
    primitiveLanes printedBits venue addr roster floor t short (Or.inl live)

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
