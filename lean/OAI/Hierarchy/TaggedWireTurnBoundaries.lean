import OAI.Hierarchy.TaggedWireWordTurns
import OAI.Hierarchy.TaggedWireWalkVisits

namespace OAI
/-! # Exact signed sides of the two links at each native itinerary boundary -/
noncomputable section
namespace Hierarchy.WireTelescope.Spine
open LinearAlgebra.SpectralBooks SiteTensor
open scoped Classical BigOperators
variable {S : ℕ} {E : Type} {G : PortGraph (Fin S) E} {a b : Fin S} {es : List E}

/-- The pair of wire identities at boundary `j`. At either end the
corresponding resource half-port is used; other identities carry a natural
ordinal into the reported occurrence sequence. -/
def sides : {a b : Fin S} → {es : List E} → (sp : Spine G a es b) →
    TurnRef → TurnRef → ℕ → Fin (es.length+1) → (TurnRef × TurnRef)
  | _,_,_,.nil _,l,r,_,_ => (l,r)
  | _,_,_,.cons _ t tail,l,r,n,z => Fin.cases (l,.inr (n,t)) (fun j=>
      tail.sides (.inr (n,!t)) r (n+1) j) z

theorem in_wordTurns (sp : Spine G a es b) (l r : TurnRef) (n : ℕ) (s : Fin S) (pair : TurnRef×TurnRef) :
    pair∈wordTurns b r sp.itinerary l n s ↔ ∃j,sp.visit j=s ∧ sp.sides l r n j=pair := by
  induction sp generalizing l n with
  | nil v=>
    by_cases h:v=s <;> simp [itinerary,wordTurns,visit,sides,h,eq_comm]
  | @cons e side xs b tail ih=>
    simp only [itinerary,wordTurns,List.mem_append]
    rw [ih (.inr (n,!side)) (n+1)]
    have first : pair∈(if G.vertex e side=s then [(l,Sum.inr (n,side))] else []) ↔
        G.vertex e side=s ∧ (l,Sum.inr (n,side))=pair := by
      by_cases h:G.vertex e side=s <;> simp [h,eq_comm]
    rw [first]
    constructor
    · rintro (h|⟨j,h⟩)
      · exact ⟨0,h⟩
      · exact ⟨j.succ,h⟩
    · rintro ⟨j,h⟩
      induction j using Fin.cases with
      | zero=>exact Or.inl h
      | succ j=>exact Or.inr ⟨j,h⟩

/-- The row emitted at `j` verifies exactly the preceding arrival and the
succeeding departure. Repetitions remain separate, using their actual
ordinals. This projects the native adjacent-read ABI to both gate inputs. -/
theorem left_index (sp : Spine G a es b) (l r : TurnRef) (n : ℕ) (j : Fin (es.length+1)) :
    j.val=0 ∧ (sp.sides l r n j).1=l ∨
      (0<j.val ∧ ∃ t,(sp.sides l r n j).1=.inr (n+(j.val-1),t)) := by
  induction sp generalizing n l with
  | nil v=>exact Or.inl ⟨Fin.eq_zero j ▸ rfl,rfl⟩
  | @cons e t xs b tail ih=>
    induction j using Fin.cases with
    | zero=>exact Or.inl ⟨rfl,rfl⟩
    | succ j=>
      rcases ih (.inr (n,!t)) (n+1) j with ⟨zero,eq⟩|⟨positive,u,eq⟩
      · exact Or.inr ⟨Nat.succ_pos _,!t,by simpa [sides,zero] using eq⟩
      · apply Or.inr
        refine ⟨Nat.succ_pos _,u,?_⟩
        change (tail.sides (.inr (n,!t)) r (n+1) j).1=_
        rw [eq]
        congr 2
        simp only [Fin.val_succ]; omega

theorem right_index (sp : Spine G a es b) (l r : TurnRef) (n : ℕ) (j : Fin (es.length+1)) :
    j.val=es.length ∧ (sp.sides l r n j).2=r ∨
      (j.val<es.length ∧ ∃ t,(sp.sides l r n j).2=.inr (n+j.val,t)) := by
  induction sp generalizing n l with
  | nil v=>exact Or.inl ⟨Fin.eq_zero j ▸ rfl,rfl⟩
  | @cons e t xs b tail ih=>
    induction j using Fin.cases with
    | zero=>exact Or.inr ⟨Nat.succ_pos _,t,by simp [sides]⟩
    | succ j=>
      rcases ih (.inr (n,!t)) (n+1) j with ⟨last,eq⟩|⟨short,u,eq⟩
      · exact Or.inl ⟨congrArg Nat.succ last,eq⟩
      · apply Or.inr
        refine ⟨Nat.succ_lt_succ short,u,?_⟩
        change (tail.sides (.inr (n,!t)) r (n+1) j).2=_
        rw [eq]
        congr 2
        simp only [Fin.val_succ]; omega

end Hierarchy.WireTelescope.Spine

end
end OAI
