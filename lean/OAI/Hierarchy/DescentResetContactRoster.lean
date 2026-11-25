import OAI.Hierarchy.DescentResetLocalOverflow

namespace OAI
/-! # Both directed contacts of every host slot in an issued reciprocal roster -/
namespace Hierarchy.DescentPlainTerminal.Suffix.ContactRoster
open DescentColonies DescentIssuedFallbackPanel
open scoped Classical
noncomputable section
variable {V : Type} [Fintype V] [DecidableEq V] {Δ : ℕ}
variable (near : V→Finset V) (raw : V→Fin Δ→Option V)
    (listed : ∀v u,u∈near v ↔ ∃j,raw v j=some u)
    (reciprocal : ∀v u,u∈near v → v∈near u)

def dart (v : V) (s : Fin Δ ⊕ Fin Δ) : Option (Contacts near) :=
  match s with
  | .inl j => Option.pmap (p := fun u => u ∈ near v) (fun u mem => ⟨v,⟨u,mem⟩⟩)
      (raw v j) (fun u hit => (listed v u).mpr ⟨j,hit⟩)
  | .inr j => Option.pmap (p := fun u => v ∈ near u) (fun u mem => ⟨u,⟨v,mem⟩⟩)
      (raw v j) (fun u hit => reciprocal v u ((listed v u).mpr ⟨j,hit⟩))

def ports (v : V) (p : Fin (Δ+Δ)) : Option (Contacts near) :=
  dart near raw listed reciprocal v (finSumFinEquiv.symm p)

omit [Fintype V] [DecidableEq V] in
theorem covers (v : V) (e : Contacts near) :
    incident near v e ↔ ∃p,ports near raw listed reciprocal v p=some e := by
  rcases e with ⟨u,t,mem⟩
  constructor
  · rintro (h|h)
    · change u=v at h
      subst v
      obtain ⟨j,atSlot⟩:=(listed u t).mp mem
      refine ⟨finSumFinEquiv (Sum.inl j),?_⟩
      simp only [ports,Equiv.symm_apply_apply,dart]
      exact Option.pmap_some' atSlot
    · change t=v at h
      subst v
      obtain ⟨j,atSlot⟩:=(listed t u).mp (reciprocal u t mem)
      refine ⟨finSumFinEquiv (Sum.inr j),?_⟩
      simp only [ports,Equiv.symm_apply_apply,dart]
      exact Option.pmap_some' atSlot
  · rintro ⟨p,atSlot⟩
    unfold ports at atSlot
    cases h : finSumFinEquiv.symm p with
    | inl j =>
      rw [h] at atSlot
      simp only [dart,Option.pmap_eq_some_iff] at atSlot
      obtain ⟨_,_,_,eq⟩ := atSlot
      exact Or.inl (congrArg Sigma.fst eq)
    | inr j =>
      rw [h] at atSlot
      simp only [dart,Option.pmap_eq_some_iff] at atSlot
      obtain ⟨_,_,_,eq⟩ := atSlot
      exact Or.inr (congrArg (fun d : Contacts near => d.2.val) eq)


end
end Hierarchy.DescentPlainTerminal.Suffix.ContactRoster

end OAI
