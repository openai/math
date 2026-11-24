import OAI.Computability.VPVNP.CompressorSourceWalk
import OAI.Computability.VPVNP.CompressorRefreshStageFrame

/-!
# Combining a native source walk with its per-stage certificates

When both walks contain a prescribed number of reports for each stage, their
boundaries coincide. Thus both properties hold at the same input memories.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords

open BurstRAM

theorem StageFrame.Scanned.calls {w first stop : ℕ} {rs : List (Report w)}
    (h : StageFrame.Scanned first stop rs) : rs.length + first = stop := by
  induction h with
  | done => simp
  | next _ _ _ ih => rw [List.length_cons]; omega

namespace SourceWalk

variable {w : ℕ} {J : Type*} {src extra : J → Memory w → List (Report w) → Prop}

private theorem split_cons {i : J} {is : List J} {m : Memory w} {rs : List (Report w)}
    (walk : SourceWalk src (i::is) m rs) :
    ∃ xs ys, src i m xs ∧ SourceWalk src is (after m (eventLog xs)) ys ∧ rs = xs++ys := by
  cases walk with
  | next head tail => exact ⟨_,_,head,tail,rfl⟩

theorem and_of_counts (count : J → ℕ)
    (sourceCount : ∀ j m rs, src j m rs → rs.length = count j)
    (extraCount : ∀ j m rs, extra j m rs → rs.length = count j)
    {is : List J} {m : Memory w} {rs : List (Report w)}
    (source : SourceWalk src is m rs) (other : SourceWalk extra is m rs) :
    SourceWalk (fun j m rs ↦ src j m rs ∧ extra j m rs) is m rs := by
  induction source with
  | done => exact .done _
  | @next i is m xs ys h tail ih =>
    obtain ⟨xs',ys',h',rest,eqn⟩ := split_cons other
    obtain ⟨rfl,rfl⟩ := List.append_inj eqn ((sourceCount i m xs h).trans (extraCount i m xs' h').symm)
    exact .next ⟨h,h'⟩ (ih rest)

end SourceWalk
end CompressorRecords

end VPVNP
end Computability
end OAI
