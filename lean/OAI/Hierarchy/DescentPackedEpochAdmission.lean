import OAI.Hierarchy.DescentPackedEpochFold
import OAI.Hierarchy.DescentTerminalObservationPrefix

namespace OAI
/-! # Packed physical rejection exactly matches the dependent history decoder -/
namespace Hierarchy.DescentPackedEpochFold
open DescentTerminalEpochChart DescentTerminalEpochHeader Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {src : U→Z}
variable {w : ℕ} (b : Chart bits ok src) (z : b.Pin→Bool) (m : Memory w) (ss : List (Stage b.Pin))

theorem reached (issuance : ss.map Stage.source=b.layout)
    (counts : List.IsPrefix ((b.rows z).map Observation.count) (ss.map fun s=>(m s.banks.count.base).val)) :
    List.IsPrefix (b.rows z) (ss.map fun s=>view s m z) := by
  apply prefix_fields
  · obtain ⟨tail,layout⟩:=b.archived z
    refine ⟨tail,?_⟩
    symm
    calc
      (ss.map (fun s=>view s m z)).map Observation.image=
          (ss.map Stage.source).map (fun s=>s.image z) := by simp only [List.map_map];rfl
      _ = (b.rows z).map Observation.image++tail := by rw [issuance,layout]
  · simpa only [List.map_map,Function.comp_def,view] using counts

/-- Counts of all still-reached epochs suffice. After a first malformed
candidate every later count may be arbitrary. -/
theorem survives (seed : ℕ) (initial : m seed=0 ↔ ok (z∘b.seed))
    (issuance : ss.map Stage.source=b.layout)
    (counts : List.IsPrefix ((b.rows z).map Observation.count) (ss.map fun s=>(m s.banks.count.base).val)) :
    (m seed=0 ∧ ∀s∈ss,m s.exterior=0 ∧ (view s m z).Valid) ↔
      (∃c,b.read z=some c) ∧ ∀s∈ss,m s.exterior=0 := by
  obtain ⟨tail,pre⟩:=reached b z m ss issuance counts
  have step : (∀s∈ss,(view s m z).Valid) ↔ ∀a∈(ss.map fun s=>view s m z),a.Valid := by simp
  constructor
  · rintro ⟨live,test⟩
    have good:=step.mp fun s h=>(test s h).2
    refine ⟨(b.accepted z).mpr ⟨initial.mp live,?_⟩,fun s h=>(test s h).1⟩
    intro a ha
    exact good a (by rw [←pre];exact List.mem_append_left _ ha)
  · rintro ⟨found,external⟩
    obtain ⟨start,good⟩:=(b.accepted z).mp found
    obtain ⟨c,hc⟩:=found
    have size:=congrArg List.length (b.complete z c hc)
    have recorded:=congrArg List.length issuance
    have len:=congrArg List.length pre
    simp only [List.length_map,List.length_append] at size recorded len
    have empty : tail=[]:=List.eq_nil_of_length_eq_zero (by omega)
    have same : b.rows z=(ss.map fun s=>view s m z) := by simpa only [empty,List.append_nil] using pre
    exact ⟨initial.mpr start,fun s h=>⟨external s h,step.mpr (same ▸ good) s h⟩⟩

theorem validated (low seed final : ℕ) (safe : Order w low seed final ss)
    (paid : ∀s∈ss,Paid w low s)
    (data_ : ∀s∈ss,DescentPackedProfileValidity.Reads s.banks m s.source.pin z s.grain)
    (initial : m seed=0 ↔ ok (z∘b.seed)) (issuance : ss.map Stage.source=b.layout)
    (counts : List.IsPrefix ((b.rows z).map Observation.count) (ss.map fun s=>(m s.banks.count.base).val)) :
    (fold w seed final ss).Spec (·=m) (fun _ o=>
      (o final=if (∃c,b.read z=some c) ∧ ∀s∈ss,m s.exterior=0 then 0 else 1) ∧
      ∀i < low,o i=m i) (bill seed final ss) ∧ ProtocolRAM.CheapCode (fold w seed final ss) := by
  have produced:=run low seed final ss z m safe paid data_
  simpa only [survives b z m ss seed initial issuance counts] using produced

end
end Hierarchy.DescentPackedEpochFold

end OAI
