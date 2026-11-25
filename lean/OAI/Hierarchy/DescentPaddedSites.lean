import OAI.Hierarchy.DescentColonyScanLeaves
import OAI.Hierarchy.DescentScanMinimum

namespace OAI
/-! # Exact cost of padding the public host directory in a multiplier search -/

namespace Hierarchy.DescentColonies.Scan
open scoped BigOperators Classical
noncomputable section
variable {k : ℕ} {V U : Type} [Fintype V] [Fintype U]

theorem padded_lookup (e : V↪U) (inc : V→List V) (pad : U→List U)
    (w : V→Block k→ℕ) (w' : U→Block k→ℕ)
    (list : ∀v,pad (e v)=(inc v).map e) (same : ∀v x,w' (e v) x=w v x)
    (D cap n d : ℕ) (v : V) (x : Block k) :
    lookup (build pad w' D cap n) d (e v) x=lookup (build inc w D cap n) d v x := by
  induction n generalizing d v x with
  | zero=>rfl
  | succ n ih=>
    rw [lookup_build_succ,lookup_build_succ]
    split
    · apply Bool.eq_iff_iff.mpr
      rw [rowValue_spec,rowValue_spec,mass,mass]
      simp only [same,ih,list,List.mem_map]
      apply or_congr Iff.rfl
      apply or_congr Iff.rfl
      constructor
      · rintro ⟨_,⟨u,mem,rfl⟩,y,eq,found⟩
        exact ⟨u,mem,y,eq,(ih _ u y) ▸ found⟩
      · rintro ⟨u,mem,y,eq,found⟩
        exact ⟨e u,⟨u,mem,rfl⟩,y,eq,(ih _ u y).symm ▸ found⟩
    · exact ih d v x

theorem absent_lookup (pad : U→List U) (w : U→Block k→ℕ) (v : U)
    (empty : pad v=[]) (zero : ∀x,w v x=0) (D cap n d : ℕ) (x : Block k) :
    lookup (build pad w D cap n) d v x=false := by
  induction n generalizing d x with
  | zero=>rfl
  | succ n ih=>
    rw [lookup_build_succ]
    split
    · apply Bool.eq_iff_iff.mpr
      rw [rowValue_spec]
      simp [mass,zero,empty,ih]
    · exact ih d x

theorem sites_padded (e : V↪U) (inc : V→List V) (pad : U→List U)
    (w : V→Block k→ℕ) (w' : U→Block k→ℕ)
    (list : ∀v,pad (e v)=(inc v).map e) (same : ∀v x,w' (e v) x=w v x)
    (D cap : ℕ) (v : V) :
    siteKeys (build pad w' D cap k) (e v)=siteKeys (build inc w D cap k) v := by
  unfold siteKeys leafDepth
  simp_rw [padded_lookup e inc pad w w' list same]

theorem absent_site (pad : U→List U) (w : U→Block k→ℕ) (v : U)
    (empty : pad v=[]) (zero : ∀x,w v x=0) (D cap : ℕ) :
    siteKeys (build pad w D cap k) v={(0,0)} := by
  have dep (x : Block k) : leafDepth (build pad w D cap k) v x=0 := by
    unfold leafDepth
    simp_rw [absent_lookup pad w v empty zero D cap k]
    cases k <;> rfl
  have grouped (x : Block k) : group 0 x=0 := by
    simp [group,width]
  simp only [siteKeys,dep,grouped]
  exact Finset.image_const ⟨⟨0,Nat.two_pow_pos _⟩,Finset.mem_univ _⟩ _

/-- Empty rows add exactly one root leaf each. The additive constant does
not depend on the candidate multiplier. -/
theorem padding_score (e : V↪U) (inc : V→List V) (pad : U→List U)
    (w : V→Block k→ℕ) (w' : U→Block k→ℕ)
    (list : ∀v,pad (e v)=(inc v).map e) (same : ∀v x,w' (e v) x=w v x)
    (ghost : ∀v,v∉Set.range e→pad v=[] ∧ ∀x,w' v x=0)
    (D cap : ℕ) : leafScore pad w' D cap=leafScore inc w D cap+(Fintype.card U-Fintype.card V) := by
  classical
  rw [leafScore_siteKeys,leafScore_siteKeys]
  let live := Finset.univ.map e
  let term := fun v=>(siteKeys (build pad w' D cap k) v).card
  have hits : (∑v∈live,term v)=∑v,(siteKeys (build inc w D cap k) v).card := by
    simp [live,term,Finset.sum_map,sites_padded e inc pad w w' list same]
  have extras : ∀v∈liveᶜ,term v=1 := by
    intro v missing
    have outside : v∉Set.range e := by
      rintro ⟨u,rfl⟩
      exact (Finset.mem_compl.mp missing) (by simp [live])
    obtain ⟨no,nul⟩:=ghost v outside
    simp [term,absent_site pad w' v no nul]
  have partition := Finset.sum_add_sum_compl live term
  have remainder : (∑v∈liveᶜ,term v)=Fintype.card U-Fintype.card V := by
    rw [Finset.sum_congr rfl extras]
    simp [live,Finset.card_compl]
  rw [←partition,hits,remainder]

end
end Hierarchy.DescentColonies.Scan

namespace Hierarchy.DescentColonies
theorem minimum_shift {X : Type*} (f : X→ℕ) (c : ℕ) (l : List X) :
    (scanMinimum (fun x=>f x+c) l).1=(scanMinimum f l).1.map (fun p=>(p.1,p.2+c)) := by
  induction l with
  | nil=>rfl
  | cons x xs ih=>
    simp only [scanMinimum,ih]
    cases h : (scanMinimum f xs).1 with
    | none=>rfl
    | some p=>by_cases h' : f x≤p.2 <;> simp [h']

end Hierarchy.DescentColonies

end OAI
