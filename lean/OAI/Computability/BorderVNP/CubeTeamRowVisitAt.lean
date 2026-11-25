import OAI.Computability.BorderVNP.CubeTeamRowInverse

/-! # Locating an actual ordered-pair visit in a returned team traversal -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.TeamRows

open RoutingISA VPVNP.BurstRAM TeamRowPrepare

/-- At each ordinal in the remaining interval there is an actual visit, with its
prepared control bank and input memory. A memory property propagated by the genuine
visits still holds at the chosen ordinal. -/
theorem ReturnedRows.visit_at {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    {l : Layout} {strict diagonal : Code} {k r m rows es t mt}
    (returned : ReturnedRows pub mac l strict diagonal k r m rows es t mt)
    (resident : ℕ → Word w → Memory w → Prop) (start : resident k (r 7) m)
    (step : ∀ {q a ma gs u mu}, q < l.d*l.d → resident q (a 7) ma → ReadyRow l (readings ma) q (.ofWords a ma) →
      Visit pub mac l strict diagonal q a ma gs u mu → resident (q+1) (u 7) mu)
    (j : ℕ) (lo : k ≤ j) (hi : j < l.d*l.d) :
    ∃ a ma gs u mu, resident j (a 7) ma ∧ ReadyRow l (readings ma) j (.ofWords a ma) ∧
      Visit pub mac l strict diagonal j a ma gs u mu := by
  induction returned with
  | done => omega
  | @row q _ _ _ _ a _ b _ _ _ _ _ _ inRange prep ready visit bump _ ih =>
    have prep7 := prep.keepsReg prepare_keeps
    have bumped := bump.keepsReg (k := 7) (by decide)
    by_cases atHead : j = q
    · subst j
      exact ⟨a,_,_,b,_,prep7 ▸ start,ready,visit⟩
    · exact ih (bumped ▸ step inRange (prep7 ▸ start) ready visit) (by omega)

end Cube.TeamRows

end BorderVNP
end Computability
end OAI
