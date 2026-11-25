import OAI.Hierarchy.DescentNamedOrdinaryArchiveTags
import OAI.Hierarchy.DescentNamedResetArchiveTags
import OAI.Hierarchy.DescentSeedArchiveTags

namespace OAI
/-! # The archived tag pages at each original cut of the paid trajectory -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist len w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist len bits d) {n degree : ℕ} (b : Menu n degree)
    (initial : Position) (c : C) (boot : Memory w)
local notation "codes" => instruction (w:=w) traces b initial
local notation "machine" => RunTrace.machine traces (fun t _=>(codes) t)
local notation "cursor" => calendar (w:=w) traces b initial
local notation "atDate" i:arg => DatePorts.ArchiveTags (((cursor) i).ports) (DateCode.history (machine) boot i)

def TagInputs (i : ℕ) : (traces c).path.Event i→Prop
  | .ordinary _ ticket _ _ => OrdinaryTagSources traces b initial boot ticket
  | .reset before closed rest cut => ResetTagSources traces b initial i ⟨c,.reset before closed rest cut⟩ boot

omit [Fintype P] in
theorem TagInputs.result {i : ℕ} (e : (traces c).path.Event i) (live : i<len)
    (rows : TagInputs traces b initial c boot i e) : atDate (i+1) :=by
  cases e with
  | ordinary before ticket rest cut =>
    exact OrdinaryTagSources.result traces b initial c boot before ticket rest cut live rows
  | reset before closed rest cut =>
    exact ResetTagSources.result rows

omit [Fintype P] in
/-- The selected path supplies an actual event at each live index. Its pre-write rows
and the initial loader determine every field of the returned tagged archive. -/
theorem cut_archive_tags (seed : DatePorts.ArchiveTags initial.ports boot)
    (acquire : ∀i<len,∀e : (traces c).path.Event i,atDate i → TagInputs traces b initial c boot i e)
    (i : ℕ) (active : i≤len) : atDate i :=by
  induction i with
  | zero => exact seed
  | succ i ih =>
    have live : i<len:=active
    obtain ⟨e⟩:=(traces c).cut_in_prefix (traces c).path .here rfl i live
    exact TagInputs.result traces b initial c boot e live (acquire i live e (ih live.le))

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
