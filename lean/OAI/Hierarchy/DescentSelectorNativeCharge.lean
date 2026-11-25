import OAI.Hierarchy.DescentSelectorWordBudget
import OAI.Hierarchy.DescentDatedOperandSelectionRun

namespace OAI
/-! # Word-scaled native charge of the key computation and selected candidate -/
namespace Hierarchy.DescentDatedOperandSelectionRun
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.Chronology
open DescentPackedFlowBatch DescentDatedAddressBook ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescentStaticWordColumn
noncomputable section
variable {K n a : ℕ} (l : DescentDatedOperandMux.Layout)
    (F : Fin K → (Fin n → Cell a) → Cell l.keyBits) (which : Fin l.pages → Fin K)
    (args : Fin l.pages → Fin n → Expr) (head : Fin l.pages → Fin l.candidates → Expr)

theorem stage_word_bill (base w h ratio short u v : ℕ) (bus : w≤ratio*h) (fill : h≤l.lanes*short)
    (keyFits : DescentOperandFamilyBook.unit n a*l.lanes≤h/2)
    (muxFits : DescentResetStemMux.unit l.keyBits l.fieldBits*l.lanes≤h/2)
    (inputs : ∀p i,(args p i).work≤u) (values : ∀p i,(head p i).work≤v) :
    let p:=phase l F which args head base w
    (p.ticks+7*names p.program)*w≤
      readFactor K n l.candidates u v*ratio*(l.pages+1)*(h+l.hosts*h+l.hosts*l.groups*short)+
      readFactor K n l.candidates u v*ratio*(l.pages+1)*2^(h/2)*h :=by
  intro p
  have native:=physical_cost l F which args head base w u v inputs values
  apply DescentDatedSeedStartup.page_scan_words l.hosts l.groups l.lanes short h w ratio l.pages
    (readFactor K n l.candidates u v) _ fill bus
  apply read_budget l.pages (l.hosts*chunks l.groups l.lanes) n K l.candidates _ (readWork l.candidates n u v)
    (DescentOperandFamilyBook.words K n a l.lanes) (DescentDatedOperandMux.tables l)
  · exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) keyFits))
  · exact DescentResetStemMux.words_le l.candidates l.keyBits l.fieldBits l.lanes h muxFits
  · exact native.1
  · exact native.2

end
end Hierarchy.DescentDatedOperandSelectionRun

end OAI
