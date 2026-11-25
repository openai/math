import OAI.Hierarchy.DescentRegisterArchiveInduction

namespace OAI
/-! # Attaching a returned archive to the physical move that wrote it -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}


namespace RegisterTimeline
variable {C : Type*} (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
set_option quotPrecheck false
local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial
local notation "code" => instruction (w:=w) traces b initial
variable (c : C) (mem : Memory w)
local notation "t" => traces c
local notation "ram" => DateCode.history code mem
variable (limit : ℕ) (valid : Prop) (claim : PrefixClaim (traces c) w)


omit [Fintype P] in
/-- The archive assembled on the genuine history belongs to the very execution
that returns the venue. This applies to the ordinary and reset instruction alike. -/
theorem advances_with_archive (i:ℕ) (e:(t).path.Event i)
    (fixed:∀a z:RunTrace.Events traces i,∀x y,steps i a (cursor i) x → steps i z (cursor i) y → x=y)
    (venue:advances traces b initial c mem limit valid i e)
    (recorded:e.incoming (cursor i) (ram i) → e.previousClaim claim (cursor i) (ram i) → e.required limit valid →
      e.nextClaim claim (cursor (i+1)) (ram (i+1))) :
    advancesArchive traces b initial c mem limit valid claim i e:=by
  intro old archive required
  obtain ⟨move,posted,out,executed,finished⟩:=venue old required
  obtain ⟨op,next⟩:=returned traces b initial i ⟨c,e⟩ move posted (fun a x hit=>fixed a _ x move hit posted)
  have actual:(code i).Runs (ram i) out:=by rw [op];exact executed
  have image:ram (i+1)=out:=DateCode.history_event code mem i (Q := fun m => m = out) ⟨out,actual,rfl⟩
  have read:=recorded old archive required
  rw [next,image] at read
  exact ⟨move,posted,out,executed,finished,read⟩

end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
