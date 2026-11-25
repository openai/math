import OAI.Computability.BorderVNP.CellPacketGeometryLiveOwners

/-! # Charging disjoint real cell packet sections to their global source arrays -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.SiteWords

open CellSparse CellSparse.Packet
variable {C : ℕ} {S Orig : Type} {A : Type*}

/-- Every word of the true geometry source has a unique cell label. -/
theorem select_sum (rows : List (Fin C × ℕ)) : ∑ c : Fin C, (select c rows).length = rows.length := by
  induction rows with
  | nil => simp [select]
  | cons a rows ih =>
    have step (c : Fin C) : (select c (a::rows)).length = (if c=a.1 then 1 else 0) + (select c rows).length := by
      by_cases h : c=a.1 <;> simp [select,h,Eq.comm (a:=a.1),Nat.add_comm]
    simp only [step,Finset.sum_add_distrib,ih,List.length_cons]
    simp [Nat.add_comm]

/-- Sum of the genuine packet public buffers equals the length of the actual
global sparse word array, even when some cells have no owned sites. -/
theorem Directory.public_sum (D : Directory S Orig C) :
    (∑ c : Fin C, ((Source.plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c)).flatMap
      Source.Part.publicBuffer).length) = D.words.length := by
  simpa only [← D.select_words] using select_sum D.words

/-- Each owned site table contributes its real entries once across all cells.
One may filter for private entries before taking this sum. -/
theorem owned_sum (sites : List S) (owner : S → Fin C) (values : S → List A) :
    (∑ c : Fin C, ((owned c owner sites).flatMap values).length) = (sites.flatMap values).length := by
  induction sites with
  | nil => simp [owned]
  | cons a sites ih =>
    have step (c : Fin C) : ((owned c owner (a::sites)).flatMap values).length =
        (if c=owner a then (values a).length else 0) + ((owned c owner sites).flatMap values).length := by
      by_cases h : c=owner a <;> simp [owned,h,Eq.comm (a:=owner a)]
    simp only [step,Finset.sum_add_distrib,ih,List.flatMap_cons,List.length_append]
    simp

/-- All merged one-copy box counts sum to the number of actual static boxes. -/
theorem Directory.box_sum (D : Directory S Orig C) :
    (∑ c : Fin C, (D.cellBoxes c).length) = (D.sites.flatMap D.boxes).length :=
  owned_sum ..

/-- Sum of just the opaque source boxes, for the one-copy original transmission charge. -/
theorem Directory.private_sum (D : Directory S Orig C) :
    (∑ c : Fin C, ((D.cellBoxes c).filterMap Sum.getRight?).length) =
      (D.sites.flatMap fun s => (D.boxes s).filterMap Sum.getRight?).length := by
  simpa only [Directory.cellBoxes,List.filterMap_flatMap] using
    owned_sum D.sites D.owner (fun s => (D.boxes s).filterMap Sum.getRight?)

end CellPacketGeometry.SiteWords

namespace CellPacketGeometry.LiveWords

open CellSparse CellSparse.Packet
variable {s C p d : ℕ} {E I Orig : Type}

/-- The sum of the true per-cell public word counts is bounded by the actual first
sort capacity; restricting to any one team's cells only reduces the sum. -/
theorem Template.public_sum_le (T : Template E I Orig s C) (owner : Fin s → Fin C) (args : E → ℕ)
    (fields : Fin s → I → ℕ) (fit : C+T.atoms.length+C ≤ 2^p) (cells : Finset (Fin C)) :
    let D := T.directory owner args fields
    (∑ c ∈ cells, ((Source.plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c)).flatMap
      Source.Part.publicBuffer).length) ≤ 2^p := by
  intro D
  have all := D.public_sum
  have shape : D.words.length = T.atoms.length := by
    simpa only [List.length_map] using (congrArg List.length (T.atoms_eval owner args fields)).symm
  exact (Finset.sum_le_sum_of_subset (Finset.subset_univ cells)).trans (all.le.trans (shape.le.trans (by omega)))

/-- The number of emitted header, box, and reserved tail descriptors, before grouping. -/
theorem Template.chunkLabels_length (T : Template E I Orig s C) :
    T.chunkLabels.length = 5*C+((List.finRange s).flatMap T.boxes).length := by
  simp [Template.chunkLabels,List.length_flatMap,Nat.mul_comm]
  omega

/-- The subset of cells owned by one team pays at most the true global directory
size, including the three spare triples for its supplemental record prepass. -/
theorem Template.descriptors_sum_le (T : Template E I Orig s C) (owner : Fin s → Fin C) (args : E → ℕ)
    (fields : Fin s → I → ℕ) (fit : C+(Schema.coords T.chunkLabels.length).length+C ≤ 2^d)
    (cells : Finset (Fin C)) :
    let D := T.directory owner args fields
    (∑ c ∈ cells, 3*((Source.plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c)).length+3)) ≤ 2^d := by
  intro D
  have n (c : Fin C) : (Source.plan (D.privateWires c) (D.cellBoxes c) (D.cellRecords c) (D.reports c)).length+3 =
      5+(D.cellBoxes c).length := by simp [Source.plan]; omega
  have sum : (∑ c : Fin C, 3*(5+(D.cellBoxes c).length)) = 3*T.chunkLabels.length := by
    rw [← Finset.mul_sum,Finset.sum_add_distrib,D.box_sum,T.chunkLabels_length]
    simp [D,Template.directory,Nat.mul_comm]
  simp only [n]
  apply (Finset.sum_le_sum_of_subset (Finset.subset_univ cells)).trans
  rw [sum]
  have len : (Schema.coords T.chunkLabels.length).length = 3*T.chunkLabels.length := by
    simp [Schema.coords,List.length_flatMap,Nat.mul_comm]
  omega

end CellPacketGeometry.LiveWords

end BorderVNP
end Computability
end OAI
