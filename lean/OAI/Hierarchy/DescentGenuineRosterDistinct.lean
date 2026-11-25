import OAI.Hierarchy.DescentGroupPeerOrder
import OAI.Hierarchy.DescentPackedMatchTerrain

namespace OAI
/-! Distinct occupied port numbers in the actual mounted old host roster. -/
namespace Hierarchy.DescentGroupPeerOrder
open DescentSixParty DescentPacking.PackedMatch.Local.Stage
open scoped Classical
noncomputable section

variable {F P J V : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {q ε : ℝ}

theorem hostRoster_distinct (A : GroupStage W G q ε J V k) (vertex : V ↪ ℕ)
    (v : V) (i j : Fin A.degree) (u : V) (left : hostRoster A vertex v i=some u)
    (right : hostRoster A vertex v j=some u) : i=j := by
  classical
  unfold hostRoster at left right
  split at left
  next li =>
    split at right
    next rj =>
      have eqn : li.choose = rj.choose:=Subtype.ext ((Option.some.inj left).trans (Option.some.inj right).symm)
      exact li.choose_spec.symm.trans ((congrArg (hostSlot A vertex v) eqn).trans rj.choose_spec)
    next=>contradiction
  next=>contradiction

theorem hostRotor_distinct {H : ℕ} (A : GroupStage W G q ε J V k) (names : V ↪ Fin H) (h : Fin H)
    (i j : Fin A.degree) (z : Fin H)
    (left : hostRotor names (hostRoster A (names.trans Fin.valEmbedding)) h i=some z)
    (right : hostRotor names (hostRoster A (names.trans Fin.valEmbedding)) h j=some z) : i=j := by
  classical
  unfold hostRotor at left right
  by_cases live : ∃v,names v=h
  · let r:=hostRoster A (names.trans Fin.valEmbedding) live.choose
    rw [dite_eq_left live] at left right
    change (r i).map names=some z at left
    change (r j).map names=some z at right
    obtain ⟨u,hi,eqn⟩:=Option.map_eq_some_iff.mp left
    obtain ⟨u',hj,eqn'⟩:=Option.map_eq_some_iff.mp right
    have same : u=u':=names.injective (eqn.trans eqn'.symm)
    subst u'
    exact hostRoster_distinct A _ _ i j u hi hj
  · simp [live] at left

end
end Hierarchy.DescentGroupPeerOrder

end OAI
