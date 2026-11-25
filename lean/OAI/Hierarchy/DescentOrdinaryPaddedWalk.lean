import OAI.Hierarchy.DescentHaloPackedGather

namespace OAI
/-! Four steps in the previous rack directory keep an unoccupied padding component isolated. -/
namespace Hierarchy.DescentDatedAddressBook.SignedExtent
open DescentHaloWalkRAM
open scoped Classical
variable {H D n : ℕ} (R:Fin H→Fin D→Option (Fin H))
private theorem no_walk (v : Fin H) (blank : ∀j,R v j=none) (p : Path D) (t : ℕ) :
    walk R v p t=none ∨ walk R v p t=some v :=by
  induction t with
  | zero=>exact .inr rfl
  | succ t ih=>
    unfold walk
    split
    · unfold step
      split
      · rcases ih with gone|here
        · exact .inl (by rw [gone];rfl)
        · exact .inl (by rw [here];exact blank _)
      · exact ih
    · exact ih

theorem padded_donor (empty : ∀v:Fin H,n≤v.val→∀j,R v j=none) (v donor : Fin H)
    (past:n≤v.val) (p : Fin (breadth D)) (picked:Gather.select (Gather.reaching R) v p=some donor) :
    n≤donor.val:=by
  unfold Gather.select at picked
  split at picked
  · contradiction
  · rcases no_walk R v (empty v past) (path p) 4 with gone|same
    · change walk R v (path p) 4=some donor at picked;rw [gone] at picked;contradiction
    · have eqn:=Option.some.inj (same.symm.trans picked);simpa [←eqn] using past

/-- A reciprocal old directory may contain arbitrary unreachable padding components. -/
theorem closed_donor (closed:∀v u j,n≤v.val→R v j=some u→n≤u.val)
    (v d:Fin H) (past:n≤v.val) (p:Fin (breadth D))
    (picked:Gather.select (Gather.reaching R) v p=some d) : n≤d.val:=by
  have all_ (t:ℕ) (u:Fin H) (hit:walk R v (path p) t=some u) : n≤u.val:=by
    induction t generalizing u with
    | zero=>change some v=some u at hit;exact (Option.some.inj hit) ▸ past
    | succ t ih=>
      unfold walk at hit
      split at hit
      · unfold step at hit
        split at hit
        · cases prev:walk R v (path p) t with
          | none=>simp [prev] at hit
          | some prior=>rw [prev] at hit;exact closed _ _ _ (ih _ prev) hit
        · exact ih _ hit
      · exact ih _ hit
  unfold Gather.select at picked
  split at picked
  · contradiction
  · exact all_ _ _ picked

end Hierarchy.DescentDatedAddressBook.SignedExtent

end OAI
