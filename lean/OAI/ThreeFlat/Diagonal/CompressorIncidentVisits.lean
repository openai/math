import OAI.ThreeFlat.Diagonal.CompressorNodeIncident
import OAI.ThreeFlat.Diagonal.ShrinkActiveSites
import OAI.ThreeFlat.Diagonal.CompressorWordEncoding

namespace OAI
/-! # Candidate order for the chronological incident record scan -/

noncomputable section

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents
open Computability.VPVNP.Compression Placement

def visits (d c : ℕ) : List (Local.Slots d c) :=
  [false,true].flatMap fun own =>
    [false,true].flatMap fun thin =>
      (List.finRange d).flatMap fun h =>
        (List.finRange (2^c)).flatMap fun u =>
          [false,true].flatMap fun inc =>
            (List.finRange d).map fun i => (own,(thin,h,(tagOrdinal c).symm u),inc,i)

theorem mem_visits {d c : ℕ} (a : Local.Slots d c) : a ∈ visits d c := by
  rcases a with ⟨own,⟨thin,h,u⟩,inc,i⟩
  simp only [visits,List.mem_flatMap,List.mem_finRange,true_and,List.mem_map]
  refine ⟨own,?_,thin,?_,h,tagOrdinal c u,inc,?_,i,?_⟩
  · cases own <;> simp
  · cases thin <;> simp
  · cases inc <;> simp
  · simp

def visit (current : F) (S : Graph.Stage) (K : ℕ) (lay : Bool) (v : Placement.Site F)
    (a : Local.Slots S.degree S.colors) : Hit :=
  hit current S K lay a.1 a.2.1.1 a.2.2.1 v a.2.1.2.1 (tagOrdinal S.colors a.2.1.2.2) a.2.2.2

theorem all_eq_visits (current : F) (S : Graph.Stage) (K : ℕ) (lay : Bool) (v : Placement.Site F) :
    all current S K lay v = (visits S.degree S.colors).map (visit current S K lay v) := by
  simp [all,visits,visit,List.map_flatMap,List.map_map,Function.comp_def]

theorem mem_all (current : F) (S : Graph.Stage) (K : ℕ) (lay : Bool) (v : Placement.Site F) (raw : Hit) :
    raw ∈ all current S K lay v ↔ ∃ a, visit current S K lay v a = raw := by
  rw [all_eq_visits,List.mem_map]
  simp only [mem_visits,true_and]

private theorem fixedLength {α β : Type*} (xs : List α) (f : α → List β) (n : ℕ)
    (h : ∀ a,(f a).length=n) : (xs.flatMap f).length=xs.length*n := by
  induction xs with
  | nil => simp
  | cons a xs ih => simp [List.flatMap_cons,h,ih,Nat.add_mul,Nat.add_comm]

theorem length_all (current : F) (S : Graph.Stage) (K : ℕ) (lay : Bool) (v : Placement.Site F) :
    (all current S K lay v).length = capacity S := by
  let a := hit current S K lay
  have inner (own thin : Bool) (h : Fin S.degree) (u : Fin (2^S.colors)) :
      ([false,true].flatMap fun inc => (List.finRange S.degree).map (a own thin inc v h u)).length=
        2*S.degree := by simp [two_mul]
  have colors (own thin : Bool) (h : Fin S.degree) :
      ((List.finRange (2^S.colors)).flatMap fun u => [false,true].flatMap fun inc =>
        (List.finRange S.degree).map (a own thin inc v h u)).length=(2^S.colors)*(2*S.degree) := by
    simpa only [List.length_finRange] using fixedLength (List.finRange (2^S.colors)) _ _ (inner own thin h)
  have ports (own thin : Bool) :
      ((List.finRange S.degree).flatMap fun h => (List.finRange (2^S.colors)).flatMap fun u =>
        [false,true].flatMap fun inc => (List.finRange S.degree).map (a own thin inc v h u)).length=
        S.degree*((2^S.colors)*(2*S.degree)) := by
    simpa only [List.length_finRange] using fixedLength (List.finRange S.degree) _ _ (colors own thin)
  have choices (own : Bool) :
      ([false,true].flatMap fun thin => (List.finRange S.degree).flatMap fun h =>
        (List.finRange (2^S.colors)).flatMap fun u => [false,true].flatMap fun inc =>
          (List.finRange S.degree).map (a own thin inc v h u)).length=
          2*(S.degree*((2^S.colors)*(2*S.degree))) :=
    fixedLength [false,true] _ _ (ports own)
  have whole := fixedLength [false,true] _ _ choices
  calc
    _ = 2*(2*(S.degree*((2^S.colors)*(2*S.degree)))) := whole
    _ = capacity S := by unfold capacity;ring

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Incidents

end

end OAI
