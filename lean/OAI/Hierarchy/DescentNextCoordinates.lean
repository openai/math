import OAI.Hierarchy.DescentHubDirectory
import OAI.Hierarchy.DescentCommonGroups
import OAI.Hierarchy.DescentPackMass

namespace OAI
/-! # One common finite position directory for the next block of each normalized branch -/

namespace Hierarchy.DescentHostDirectory
open DescentColonies
open scoped Classical BigOperators
noncomputable section
variable {V J G : Type} [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
variable [Fintype G] [DecidableEq G] {k step slots : ℕ}

/-- The same list of reusable physical site addresses is available in every
summand. The next block digit is not part of the position. -/
abbrev Host (V : Type) [Fintype V] (k slots : ℕ) := ↥(keys (V:=V) k slots)

def restrictedNear (near : V→Finset V) (D k slots : ℕ) (v : Host V k slots) : Finset (Host V k slots) :=
  Finset.univ.filter fun w=>w.val∈directory near D slots 10 v.val ∧ v.val∈directory near D slots 10 w.val

theorem restricted_symmetric (near : V→Finset V) (D k slots : ℕ) (v w : Host V k slots) :
    w∈restrictedNear near D k slots v ↔ v∈restrictedNear near D k slots w := by
  simp [restrictedNear,and_comm]

theorem restricted_degree (near : V→Finset V) (D k slots Δ : ℕ) (old : ∀v,(near v).card≤Δ)
    (v : Host V k slots) : (restrictedNear near D k slots v).card≤((Δ+1)*(D+1+2*2^D)*slots)^10 := by
  let addresses := (restrictedNear near D k slots v).map (Function.Embedding.subtype _)
  have keep : addresses⊆directory near D slots 10 v.val := by
    intro a member
    obtain ⟨w,isListed,rfl⟩ := Finset.mem_map.mp member
    exact (Finset.mem_filter.mp isListed).2.1
  have size : (restrictedNear near D k slots v).card ≤ (directory near D slots 10 v.val).card := by
    simpa [addresses] using Finset.card_le_card keep
  exact size.trans (directory_card near D slots Δ old 10 v.val)

omit [DecidableEq V] in
theorem host_size : Fintype.card (Host V k slots)≤Fintype.card V*2^(k+1)*slots := by
  simpa using keys_card (V:=V) k slots

variable {S : Type} [Fintype S] (id : S ↪ Key (J×V)) (digits : J≃G×Block step)
variable (ok : ∀v,(splitKey (id v)).2∈keys k slots)

def nextPos (u : S) : G×Host V k slots :=
  ((digits (splitKey (id u)).1).1,⟨(splitKey (id u)).2,ok u⟩)
def nextBlock (u : S) : Block step := (digits (splitKey (id u)).1).2

omit [DecidableEq V] [Fintype J] [DecidableEq J] [Fintype G] [DecidableEq G] [Fintype S] in
theorem next_injective : Function.Injective (fun v=>(nextPos id digits ok v,nextBlock id digits v)) := by
  intro u v eqn
  apply id.injective
  apply splitKey.injective
  have eg := congrArg (fun z : (G×Host V k slots)×Block step=>z.1.1) eqn
  have es := congrArg (fun z : (G×Host V k slots)×Block step=>z.1.2.val) eqn
  have eb := congrArg Prod.snd eqn
  exact Prod.ext (digits.injective (Prod.ext eg eb)) es

omit [Fintype J] [DecidableEq J] [Fintype G] in
theorem next_mass (full : S→ℕ) (cap : ℕ) (measured : ∀u,full u≤cap)
    (v : G×Host V k slots) (i : Block step) :
    (∑u,if nextPos id digits ok u=v ∧ nextBlock id digits u=i then full u else 0)≤cap := by
  by_cases hit : ∃u,nextPos id digits ok u=v ∧ nextBlock id digits u=i
  · obtain ⟨x,hx⟩ := hit
    rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)]
    · rw [ite_eq_left hx]
      exact measured x
    · intro y _ different
      apply ite_eq_right
      exact fun hy=>different (next_injective id digits ok (Prod.ext (hy.1.trans hx.1.symm) (hy.2.trans hx.2.symm)))
  · have empty := not_exists.mp hit
    simp [empty]

omit [Fintype J] [DecidableEq J] [Fintype G] in
theorem next_full_at (full : S→ℕ) (x : S) :
    (∑u,if nextPos id digits ok u=nextPos id digits ok x ∧ nextBlock id digits u=nextBlock id digits x
      then full u else 0)=full x := by
  rw [Finset.sum_eq_single_of_mem x (Finset.mem_univ _)]
  · simp
  · intro y _ different
    exact ite_eq_right (fun both=>different (next_injective id digits ok (Prod.ext both.1 both.2)))

omit [Fintype J] [Fintype G] [DecidableEq G] [Fintype S] in
theorem next_close (near : V→Finset V) {D : ℕ} {u v : S}
    (walk : id v∈directory (groupedNear near) D slots 10 (id u))
    (back : id u∈directory (groupedNear near) D slots 10 (id v)) :
    nextPos id digits ok v ∈ groupedNear (restrictedNear near D k slots) (nextPos id digits ok u) ∧
      nextBlock id digits v=nextBlock id digits u := by
  obtain ⟨eg,edir⟩ := same_and_close near D slots 10 walk
  have h : (digits (splitKey (id v)).1)=(digits (splitKey (id u)).1) := congrArg digits eg
  constructor
  · refine Finset.mem_map.mpr ⟨(nextPos id digits ok v).2,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,edir,(same_and_close near D slots 10 back).2⟩,?_⟩
    exact Prod.ext (congrArg Prod.fst h).symm rfl
  · exact congrArg Prod.snd h

end
end Hierarchy.DescentHostDirectory

end OAI
