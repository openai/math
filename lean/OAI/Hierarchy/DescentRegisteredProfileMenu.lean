import OAI.Hierarchy.DescentRegisteredWindow
import OAI.Hierarchy.DescentPackedEpochShelfLayout
import OAI.Hierarchy.DescentOrdinaryCountDates
import OAI.Hierarchy.DescentNamedRegisteredStaticCore

namespace OAI
/-! # Date-indexed packed ballot shelves in the register calendar -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPacking.PackedMatch.Local.Stage
noncomputable section

def rowNumber (S : DescentCompiler.AtomSchedule) (age : ℕ) : ℕ :=
  (countDates 0 ((kindCalendar S.rounds S.height).take age)).length

variable {A : Type} {F : Type} [Field F] (G : PoweredGadget F) (S : DescentCompiler.AtomSchedule)
    {n D : ℕ} (board : NonlinearExpanders.Graph n D) (op : RotorSpec)
    (k tail p f gain drift degree payload lo hdr : ℕ) (entries : List (Source A))

def profileAt (S : DescentCompiler.AtomSchedule) (oldPitch lo : ℕ) (ls : List (Source A)) (age : ℕ) :=
  (shelves oldPitch lo 0 ls)[rowNumber S age]?

def fromProfiles : Menu n D :=
  let oldPitch:=DescentPackedEpochShelves.grain (payload/2) G.C
  let seats:=fun i=>((profileAt S oldPitch lo entries i).map (fun x=>x.src.seats)).getD 0
  { board:=board,op:=op,gain:=gain,tail:=tail,p:=p,f:=f,drift:=drift,degreeLimit:=degree,
    payload:=payload,seats:=seats,profile:=fun i=>((profileAt S oldPitch lo entries i).map DescentPackedEpochShelves.Shelf.base).getD lo,
    ordinary:=fun i=>(DonorDate.atDate G S gain k i p).schedule payload (seats i) (S.censusBits p),header:=hdr }

theorem profileAt_entry {oldPitch lo age : ℕ} {ls : List (Source A)} (s : DescentPackedEpochShelves.Shelf A)
    (selected : profileAt S oldPitch lo ls age=some s) : ls[rowNumber S age]?=some s.src :=by
  rw [←sources oldPitch lo 0 ls,List.getElem?_map]
  change Option.map DescentPackedEpochShelves.Shelf.src (profileAt S oldPitch lo ls age)=some s.src
  rw [selected]
  rfl

theorem fromProfiles_at (i : ℕ) (s : DescentPackedEpochShelves.Shelf A)
    (hit : profileAt S (DescentPackedEpochShelves.grain (payload/2) G.C) lo entries i=some s) :
    let b:=fromProfiles G S board op k tail p f gain drift degree payload lo hdr entries
    b.profile i=s.base ∧ b.seats i=s.src.seats ∧
      b.ordinary i=(DonorDate.atDate G S gain k i p).schedule payload s.src.seats (S.censusBits p) :=by
  simp [fromProfiles,hit]

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
