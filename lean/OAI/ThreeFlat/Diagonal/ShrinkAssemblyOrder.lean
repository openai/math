import OAI.ThreeFlat.Diagonal.CompressorIncidentVisits
import OAI.ThreeFlat.Diagonal.ShrinkActiveSites

namespace OAI
/-! # The selected shrink-node order is independent of the RAM word size -/
namespace ThreeFlat.Diagonal.CompressorPacking
open Computability.VPVNP.Compression
open scoped Classical
noncomputable section

namespace Local

/-- Keep the first occupied visit for each motif, in the candidate-visit order. -/
def firstMotifs {A : Type*} [DecidableEq A] (seen : List A) : List (Option A) → List A
  | [] => []
  | none::xs => firstMotifs seen xs
  | some a::xs => let more:=firstMotifs (a::seen) xs
                  if a∈seen then more else a::more

private theorem mem_first {A : Type*} [DecidableEq A] (a : A) (xs : List (Option A)) (seen : List A) :
    a∈firstMotifs seen xs ↔ some a∈xs ∧ a∉seen := by
  induction xs generalizing seen with
  | nil=>simp [firstMotifs]
  | cons z xs ih=>
    cases z with
    | none=>simp [firstMotifs,ih]
    | some b=>
      by_cases ha : a=b
      · subst b;by_cases h : a∈seen <;> simp [firstMotifs,h,ih]
      · by_cases h : b∈seen <;> simp [firstMotifs,ih,h,ha]

private theorem nodup_first {A : Type*} [DecidableEq A] (xs : List (Option A)) (seen : List A) :
    (firstMotifs seen xs).Nodup := by
  induction xs generalizing seen with
  | nil=>simp [firstMotifs]
  | cons z xs ih=>cases z with
    | none=>exact ih seen
    | some b=>by_cases h : b∈seen <;> simp [firstMotifs,h,ih,mem_first]

variable {B H T L : Type} [AddCommGroup H] [AddCommGroup T] [AddCommGroup L] [Fintype B] [Fintype H] [Fintype T] [Fintype L]
variable {d c : ℕ} (P : PackingData B H T L d c) (lay : Bool) (v : Site B T L)

def assemblyList : List P.Motif :=
  firstMotifs [] ((Native.ShrinkStage.Incidents.visits d c).map (atSite P lay v))

def assemblyCount := (assemblyList P lay v).length

omit [Fintype B] [Fintype H] [Fintype T] [Fintype L] in
private theorem assembly_mem (m : P.Motif) : m∈assemblyList P lay v ↔ ∃j,partySite P lay m j=v := by
  rw [assemblyList,mem_first];simp only [List.not_mem_nil,not_false_eq_true,and_true,List.mem_map]
  constructor
  · rintro ⟨a,_,hit⟩; exact ((atSite_some P lay v a m).mp hit).2
  · intro occupied
    obtain ⟨a,hit⟩:=atSite_covers P lay v m occupied
    exact ⟨a,Native.ShrinkStage.Incidents.mem_visits a,hit⟩

def assemblyOrder : Fin (assemblyCount P lay v) ≃ MotifKernel.Active (partySite P lay) v := by
  let xs:=assemblyList P lay v
  let nth (i : Fin xs.length) : MotifKernel.Active (partySite P lay) v :=
    ⟨xs.get i,(assembly_mem P lay v _).mp (List.get_mem xs i)⟩
  apply Equiv.ofBijective nth
  constructor
  · intro i j h
    exact (nodup_first _ _ : xs.Nodup).get_inj_iff.mp (congrArg Subtype.val h)
  · intro z
    obtain ⟨i,read⟩:=List.mem_iff_get.mp ((assembly_mem P lay v z.val).mpr z.property)
    exact ⟨i,Subtype.ext read⟩

omit [Fintype B] [Fintype H] [Fintype T] [Fintype L] in
@[simp] theorem assemblyOrder_value (i : Fin (assemblyCount P lay v)) :
    (assemblyOrder P lay v i).val=(assemblyList P lay v).get i := rfl

end Local
end
end ThreeFlat.Diagonal.CompressorPacking

end OAI
