import OAI.Hierarchy.DescentHostRosterOrder
import OAI.Hierarchy.DescentHaloPackedGather
import OAI.Hierarchy.DescentSortedRosterPadding

namespace OAI
/-! Embedding the old physical population into the dated host rectangle preserves the entire four-hop rotor. -/
namespace Hierarchy.DescentScalarVenueMask
open DescentHaloWalkRAM DescentPacking.PackedMatch.Local.Stage
noncomputable section
set_option quotPrecheck false
variable {H H' d : ℕ} (wide : H ≤ H')
local notation "up_" => Fin.castLEEmb wide

theorem physical_rotor {V : Type} [Fintype V] (host : V ↪ Fin H) (near : V → Fin d → Option V) (h : Fin H) (j : Fin d) :
    hostRotor (host.trans up_) near (up_ h) j=(hostRotor host near h j).map up_ := by
  classical
  by_cases live : ∃ v,host v=h
  · have reach : ∃ v,(host.trans up_) v=up_ h := ⟨live.choose,congrArg up_ live.choose_spec⟩
    have eqn : reach.choose=live.choose := host.injective (((up_).injective reach.choose_spec).trans live.choose_spec.symm)
    simp only [hostRotor,dite_eq_left reach,dite_eq_left live,eqn,Option.map_map]; rfl
  · have blank : ¬ ∃ v,(host.trans up_) v=up_ h := fun ⟨v,hit⟩ => live ⟨v,(up_).injective hit⟩
    simp [hostRotor,live]

theorem reaching_pad (s : Fin H→Fin d→Option (Fin H)) (l : Fin H'→Fin d→Option (Fin H'))
    (agree : ∀h j,l (up_ h) j=(s h j).map up_) (h : Fin H) (j : Fin (breadth d)) :
    Gather.reaching l (up_ h) j=(Gather.reaching s h j).map up_ := by
  have eqn (n : ℕ) : walk l (up_ h) (path j) n=(walk s h (path j) n).map up_ := by
    induction n with
    | zero => rfl
    | succ n ih =>
      simp only [walk,ih]
      split
      · unfold step
        split
        · cases v : walk s h (path j) n with
          | none => rfl
          | some u => exact agree u _
        · rfl
      · rfl
  exact eqn 4

theorem padded_donor_blank {V : Type} [Fintype V] (host : V↪Fin H) (near : V→Fin d→Option V)
    (u : Fin H') (ghost : H ≤ u.val) (j : Fin (breadth d)) (z : Fin H')
    (hit : Gather.reaching (hostRotor (host.trans up_) near) u j=some z) : H≤z.val := by
  have absent : ¬∃v,(host.trans up_) v=u := by
    rintro ⟨v,got⟩
    have eqn : (host v).val=u.val := congrArg Fin.val got
    have lt := (host v).isLt
    omega
  have emptyAt (a : Fin d) : hostRotor (host.trans up_) near u a=none := by
    simp only [hostRotor,dite_eq_right absent]
  have closed (p : Path d) (t : ℕ) : ∀ z,walk (hostRotor (host.trans up_) near) u p t=some z → z=u := by
    induction t with
    | zero => intro z got;exact (Option.some.inj got).symm
    | succ t ih =>
      intro z got
      rw [walk] at got
      split at got
      · unfold step at got
        split at got
        · cases curr : walk (hostRotor (host.trans up_) near) u p t with
          | none => simp [curr] at got
          | some y =>
            simp only [curr,Option.bind_some] at got
            rw [ih y curr,emptyAt] at got
            contradiction
        · exact ih z got
      · exact ih z got
  rw [closed (path j) 4 z hit]
  exact ghost

end
end Hierarchy.DescentScalarVenueMask

end OAI
