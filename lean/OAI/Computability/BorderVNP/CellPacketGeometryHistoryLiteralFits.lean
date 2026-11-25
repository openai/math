import OAI.Computability.BorderVNP.CellPacketGeometryHistoryGateCost
import OAI.Computability.BorderVNP.CellPacketGeometryHistoryCells
import OAI.Computability.BorderVNP.CellPacketFields

/-! # Width of the true history counts and hardwired public scalar literals -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open CellSparse CellSparse.Packet Packing.Inherited FrozenTape LiveWords SiteWords
open private factor_fields small_list from OAI.Computability.BorderVNP.CellPacketFields
open private group reportAtoms rowAtoms from OAI.Computability.BorderVNP.CellPacketGeometryLiveTemplate
open private roster_sum box_sum from OAI.Computability.BorderVNP.CellPacketGeometryHistoryGateCost

variable {a C cap w d t : ℕ} {R B U V E Orig : Type}

private def scalarBound {A : Type} (w : ℕ) : Atom A C → Prop
  | .literal n => n<2^w
  | _ => True

private theorem group_bound {A K X : Type} (xs : List X) (own : X → K) (f : X → List (Atom A C))
    (ok : ∀ i ∈ xs, ∀ z ∈ f i, scalarBound w z) :
    ∀ z ∈ group xs own f, scalarBound w z.2 := by
  intro z hz
  obtain ⟨i,hi,hz⟩ := List.mem_flatMap.mp hz
  obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hz
  exact ok i hi v hv

/-- Only the known-box natural words and the report-list arities enter the fixed
scalar literals. Dynamic site, count, and record pins require no literal width premise. -/
theorem LiveWords.Template.literal_fits {s : ℕ} {I : Type} (T : Template E I Orig s C)
    (boxes : ∀ i n, n ∈ boxWords (T.boxes i) → n<2^w)
    (rep : ∀ c, (T.reports c).length<2^w) (vector : ∀ c r, r∈T.reports c → r.length<2^w) :
    ∀ i : Fin T.atoms.length, ∀ n, T.atoms[i.val].2=.literal n → n<2^w := by
  have ok : ∀ z ∈ T.atoms, scalarBound w z.2 := by
    simp only [Template.atoms,List.forall_mem_append]
    refine ⟨⟨⟨⟨group_bound _ _ _ ?_,group_bound _ _ _ ?_⟩,group_bound _ _ _ ?_⟩,group_bound _ _ _ ?_⟩,
      group_bound _ _ _ ?_⟩
    · simp [scalarBound]
    · intro i _ v hv
      obtain ⟨n,hn,rfl⟩ := List.mem_map.mp hv
      exact boxes i n hn
    · simp [scalarBound]
    · intro i _ v hv
      obtain ⟨j,_,rfl⟩ := List.mem_map.mp hv
      trivial
    · intro c _ z hz
      rcases List.mem_cons.mp hz with rfl | rest
      · exact rep c
      · obtain ⟨r,hr,hz⟩ := List.mem_flatMap.mp rest
        rcases List.mem_cons.mp hz with rfl | h
        · exact vector c r hr
        · obtain ⟨e,_,rfl⟩ := List.mem_map.mp h
          trivial
  intro i n hn
  have hb := ok _ (List.getElem_mem i.isLt)
  rwa [hn] at hb

/-- Literal widths of public box words follow from the factor fields and the
one-copy factor count. The proof has no premise on the opaque delivered data. -/
theorem known_words_fit (xs : List (Source.Box Orig)) {bound : ℕ}
    (small : bound<2^w) (three : 3<2^w)
    (known : ∀ fs, Sum.inl fs∈xs → fs.length ≤ bound ∧ ∀ f∈fs, FactorFields f bound) :
    ∀ n ∈ boxWords xs, n<2^w := by
  intro n hn
  obtain ⟨part,hm,member⟩ := List.mem_flatMap.mp hn
  obtain ⟨b,hb,part_eq⟩ := List.mem_map.mp hm
  subst part
  cases b with
  | inr i => cases member
  | inl fs =>
    obtain ⟨hlen,hfields⟩ := known fs hb
    exact (small_list factor fs hlen (fun f hf => factor_fields f (hfields f hf)) n member).trans_lt
      (max_lt three small)

namespace History

variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E)) (args : E → ℕ)
variable (x : Pins R B d → Bool) (y : Pins U V t → Bool) (cells : Fin a → Fin C) (off box : Fin a → ℕ)

local notation3 "T₀" => template S L boxes sh lh priv rep
local notation3 "G₀" => directory S L boxes sh lh priv rep args x y cells off box

private theorem total_le {n C : ℕ} (own : Fin n → Fin C) (weights : Fin n → ℕ) (c : Fin C) :
    total own weights c ≤ ∑ i, weights i :=
  Finset.sum_le_sum (fun i _ => by split <;> simp)

/-- Every real and skipped cell fits both list-count words once the global
physical box count and the total frozen and final row-slot count fit. -/
theorem cell_counts_fit (boxRoom : (∑ i, (boxes i).length) < 2^w)
    (rowRoom : S.rows.length+L.rows.length < 2^w) (c : Fin (C+1)) :
    ((G₀).cellBoxes c).length<2^w ∧ ((G₀).cellRecords c).length<2^w := by
  let owner := cellOf S L x y cells
  let vals := fun i : Fin (roster a S L).length => scalarArgs (cap := cap) S L x y off box ((roster a S L).get i)
  let D := (T₀).directory owner args vals
  change (D.cellBoxes c).length < _ ∧ ((D.regroup (anchor S L x y)).cellRecords c).length < _
  rw [D.regroup_counts _ rfl (anchored S L x y cells) c]
  constructor
  · change ((owned c owner (List.finRange _)).flatMap (T₀).boxes).length < _
    rw [←merged_length]
    apply (total_le owner _ c).trans_lt
    rwa [box_sum S L boxes sh lh priv rep List.length rfl]
  · change ((owned c owner (List.finRange _)).flatMap D.rows).length < _
    rw [←merged_length]
    apply (total_le owner _ c).trans_lt
    have len (i) : (D.rows i).length = (format (a := a) S L sh lh ((roster a S L).get i)).length := List.length_map ..
    simp only [len]
    rw [roster_sum S L (fun v => (format S L sh lh v).length)]
    simpa [format,List.map_const'] using rowRoom

/-- Literal-fit specialization at the actual chronological site roster; padded row
slots emit no box literals of their own. -/
theorem literal_fits (known : ∀ i n, n ∈ boxWords (boxes i) → n<2^w)
    (reports : ∀ c, (rep c).length<2^w) (vectors : ∀ c r, r∈rep c → r.length<2^w) :
    ∀ i : Fin (T₀).atoms.length, ∀ n, (T₀).atoms[i.val].2=.literal n → n<2^w := by
  apply (T₀).literal_fits _ reports vectors
  intro i n hn
  change n ∈ boxWords (((roster a S L).get i).elim boxes (fun _ => [])) at hn
  cases e : (roster a S L).get i with
  | inl v => rw [e] at hn; exact known v n hn
  | inr v => rw [e] at hn; simp [boxWords] at hn

end History
end CellPacketGeometry

end BorderVNP
end Computability
end OAI
