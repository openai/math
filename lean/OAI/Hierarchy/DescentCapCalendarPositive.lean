import OAI.Hierarchy.DescentFixedMenu

namespace OAI
/-! # Every physical capacity multiplier in the ordinary/reset calendar is positive -/
namespace Hierarchy.DescentSixParty.Chronology.DonorDate
open DescentCompiler
theorem prefix_cap_pos (base rounds gain height age : ℕ) (basePos : 0<base) :
    0<((capCalendar base rounds gain height).take age).prod := by
  have ord : ∀start count x,x∈ordinaryCapFactors base start count→0<x := by
    intro start count
    induction count generalizing start with
    | zero=>simp [ordinaryCapFactors]
    | succ count ih=>
      intro x hx
      rcases List.mem_cons.mp hx with rfl|tail
      · exact Nat.mul_pos (Nat.two_pow_pos _) basePos
      · exact ih _ _ tail
  have periods : ∀y x,x∈capCalendar base rounds gain y→0<x := by
    intro y
    induction y with
    | zero=>simp [capCalendar]
    | succ y ih=>
      intro x hit
      rcases List.mem_append.mp hit with here|later
      · rcases List.mem_append.mp here with old|last
        · exact ord _ _ _ old
        · rw [List.mem_singleton.mp last]
          exact Nat.two_pow_pos _
      · exact ih _ later
  exact CanonicallyOrderedAdd.list_prod_pos.mpr (fun x h=>periods _ x (List.mem_of_mem_take h))

end Hierarchy.DescentSixParty.Chronology.DonorDate

end OAI
