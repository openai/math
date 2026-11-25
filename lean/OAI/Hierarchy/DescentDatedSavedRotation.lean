import OAI.Hierarchy.DescentDatedNativeCalendar

namespace OAI
/-! # One attained rotation word per physical date -/
namespace Hierarchy.DescentDatedAddressBook.NativeDate
open DescentSixParty.Chronology
noncomputable section
variable {F P : Type} [Field F]

def saved (date : NativeDate F P) (base : ℕ) : ℕ := match date with
  | .ordinary v=>v.area.flagEnd v.old (v.stageStart base)+2^v.area.k
  | .reset v=>let p:=v.chart (v.stageStart base);let d:=p.geo.high+p.geo.low
              p.remixEnd v.payload v.gain v.positive+(2^d)^d+(2^d)^d

theorem saved_succ (date : NativeDate F P) (base : ℕ) :
    date.saved base+1=match date with
      | .ordinary v=>v.area.rotationEnd v.old (v.stageStart base)
      | .reset v=>(v.chart (v.stageStart base)).rotationEnd v.payload v.gain v.positive :=by cases date <;> rfl

end
end Hierarchy.DescentDatedAddressBook.NativeDate

end OAI
