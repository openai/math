import OAI.ThreeFlat.Diagonal.CompressorWordEncoding
import OAI.ThreeFlat.Diagonal.CompressorLocalSlots
import OAI.ThreeFlat.Diagonal.CompressorRankCorrect
import OAI.ThreeFlat.Diagonal.CompressorNativeGraph

namespace OAI
/-! # The bounded list underlying native source and target slot election -/

namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM
open scoped Classical BigOperators Fin.NatCast

/-- Physical traversal order, including all parallel-copy and child bits. -/
def Local.visits (d c : ℕ) (count : Fin 4 → ℕ) : List (Local.EdgeIndex d c count) :=
  (List.finRange 4).flatMap fun t =>
    (List.finRange (count t)).flatMap fun j =>
      [false,true].flatMap fun thin =>
        (List.finRange d).flatMap fun h =>
          (List.finRange (2^c)).flatMap fun u =>
            [false,true].flatMap fun inc =>
              (List.finRange d).map fun i =>
                ⟨t,((thin,h,(Native.tagOrdinal c).symm u),inc,i),j⟩

theorem Local.mem_visits {d c : ℕ} {count : Fin 4 → ℕ} (x : Local.EdgeIndex d c count) :
    x ∈ Local.visits d c count := by
  rcases x with ⟨t,⟨⟨thin,h,u⟩,inc,i⟩,j⟩
  simp only [visits,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  refine ⟨t,j,thin,?_,h,Native.tagOrdinal c u,inc,?_,i,?_⟩
  · cases thin <;> simp
  · cases inc <;> simp
  · simp

namespace Native.Graph
variable {B H Tag L : Type*} {d c w : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData B H Tag L d c) (layout : Bool) (role : Fin 4 → Role)
variable (count : Fin 4 → ℕ) (key : ShrinkEdge P count ↪ Word w)

noncomputable def refKey (b : B × Tag) (i : Local.EdgeIndex d c count) : Word w :=
  match Local.slotCandidate P layout role count b i with
  | none => 0
  | some e => if base (slotSite P layout role e)=b then key e else 0

theorem refKey_ne_zero (nz : ∀ e, key e ≠ 0) (b : B × Tag) (i : Local.EdgeIndex d c count) (z : Word w) :
    refKey P layout role count key b i = z ∧ z ≠ 0 ↔ ∃ e, Local.slotCandidate P layout role count b i = some e ∧
      base (slotSite P layout role e)=b ∧ key e=z := by
  cases h : Local.slotCandidate P layout role count b i with
  | none =>
    simp [refKey,h]
    exact Eq.symm
  | some e =>
    by_cases here : base (slotSite P layout role e) = b
    · simp [refKey,h,here]
      rintro rfl
      exact nz e
    · simp [refKey,h,here]
      exact Eq.symm

variable [Fintype B] [Fintype H] [Fintype Tag] [Fintype L]

theorem refKey_support (nz : ∀ e, key e ≠ 0) (b : B × Tag) :
    Rank.eligible ((Local.visits d c count).map (refKey P layout role count key b)) =
      (CompressorRegularize.incident (fun e => base (slotSite P layout role e)) b).map key := by
  ext v
  simp only [Rank.eligible,Finset.mem_erase,List.mem_toFinset,List.mem_map,Finset.mem_map,
    CompressorRegularize.incident,Finset.mem_filter,Finset.mem_univ,true_and,Local.mem_visits]
  constructor
  · rintro ⟨nzv,i,hi⟩
    obtain ⟨e,_,here,val⟩ := (refKey_ne_zero P layout role count key nz b i v).mp ⟨hi,nzv⟩
    exact ⟨e,here,val⟩
  · rintro ⟨e,here,rfl⟩
    obtain ⟨i,hi⟩ := Local.covers_slot P layout role count e
    rw [here] at hi
    exact ⟨nz e,i,by simp [refKey,hi,here]⟩

end Native.Graph
end ThreeFlat.Diagonal.CompressorPacking

end OAI
