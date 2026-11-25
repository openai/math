import OAI.Computability.BorderVNP.FiniteSewnFieldStaging
import OAI.Computability.BorderVNP.PackedBankInheritedSiteCharges
import OAI.Computability.BorderVNP.PackedInheritedWorkSewnCapacity
import OAI.Computability.BorderVNP.PackedBankFullProgramFields
import OAI.Computability.BorderVNP.PackedHistorySewnTagModels

/-! # Charges of the actual private program after exterior wiring -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open Inherited InheritedBank CellSparse Crossing Shortening Diagonal.ExternalSew
open scoped Classical BigOperators

private theorem stage_blocks (s : Site) (n : ℕ) (runs : List Interval) :
    (stage s n runs).directory.blocks = s.directory.blocks := by
  change Directory.resolvedRows s.boxes (stage s n runs).rows = Directory.resolvedRows s.boxes s.rows
  have none : Directory.resolvedRows s.boxes (runs.map (Interval.record s)) = [] := by
    apply Directory.resolvedRows_wires
    intro r hr id base count step
    obtain ⟨run,_,rfl⟩ := List.mem_map.mp hr
    cases h : run.source <;> simp [Interval.record,h]
  rw [stage_rows,Directory.resolvedRows_append,none,List.append_nil]

private theorem recordWords (s : Site) (runs : List Interval) :
    ((runs.map (Interval.record s)).flatMap Packet.record).length ≤ 9*runs.length := by
  induction runs with
  | nil => simp
  | cons run tail ih =>
    simp only [List.map_cons,List.flatMap_cons,List.length_append,List.length_cons,Nat.mul_succ]
    have n : (Packet.record (Interval.record s run)).length ≤ 9 := by
      cases h : run.source with
      | none => rw [Interval.record,h]; exact (by decide : 6 ≤ 9)
      | some j => rw [Interval.record,h]; exact le_rfl
    omega

private theorem recordGuards (s : Site) (runs : List Interval) :
    ((runs.map (Interval.record s)).map Record.guardMassBound).sum = 1024*runs.length := by
  induction runs with
  | nil => rfl
  | cons run tail ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ,ih]
    cases h : run.source <;> simp [Interval.record,h,Record.guardMassBound,Nat.add_comm]

/-- Sewing adds only a bounded-size zero or equality guard per actual run;
the repeated tables and the number of factor observations stay on their original site. -/
theorem stage_charges (s : Site) (n : ℕ) (runs : List Interval) :
    (stage s n runs).staticNodes ≤ s.staticNodes+1034*runs.length ∧
      (stage s n runs).expandedLoad=s.expandedLoad+s.incoming := by
  constructor
  · have words := recordWords s runs
    simp only [Site.staticNodes,stage_blocks,stage_rows,Directory.recordNodes,Packet.fieldList,
      List.length_cons,List.flatMap_append,List.length_append,List.length_map,List.map_append,List.sum_append,
      recordGuards]
    change _ ≤ _ at words
    change _+_+_+_+_ ≤ _+1034*_
    simp only [stage]
    omega
  · simp only [Site.expandedLoad,Directory.visitCount,stage_blocks]
    change s.work+s.incoming+_=_
    omega

/-- Every emitted original-to-sewn interval owns a distinct final source lane. -/
theorem intervals_count_le {old new : ℕ} (read : Fin old → Option (Fin new)) :
    (intervals read).length ≤ old := by
  unfold intervals
  simp only [List.length_map,Finset.length_sort]
  exact (Finset.card_le_univ _).trans_eq (Fintype.card_fin _)

variable {D ae ap be bp : ℕ} {A P U Free Cable : Type}
    [Fintype A] [Fintype P] [Fintype U] [Fintype Cable]
    {width : A → ℕ} (N : Network D A width) (lane : P ↪ Σ a, Fin (width a))
    {cw : Cable → ℕ} (B : Bundle (FineView.layout N lane) Free Cable cw)
    (gw : U → ℕ) (freeLane : Free ↪ Σ u, Fin (gw u)) (owner : U → N.Site)
    (aligned : ∀ f, owner (freeLane f).1 = B.layout.attach f)
    (oldEdge : N.Edge ↪ Fin ae) (oldPort : A ↪ Fin ap)
    (edge : (N.Edge ⊕ Cable) ↪ Fin be) (port : U ↪ Fin bp) (progs : Site.Programs N)

local notation "out" => Network.packExternal (Bundle.layout B) gw owner
local notation "read₀" => sewnRead N lane B gw freeLane owner aligned oldEdge oldPort edge port

/-- The private program charges that arrive on this network's real sewn
vertex, including the zero-clamped exterior intervals. -/
theorem sewnPrograms_charges (v : N.Site) :
    let result := sewnPrograms N lane B gw freeLane owner aligned oldEdge oldPort edge port progs v
    result.program.staticNodes ≤ (progs v).program.staticNodes+1034*(incoming N v) ∧
      result.program.expandedLoad=(progs v).program.expandedLoad+incoming N v := by
  intro result
  let s := progs v
  let read := read₀ v ∘ Fin.cast s.size
  have bounds := stage_charges s.program (incoming out v) (intervals read)
  have count := intervals_count_le read
  refine ⟨bounds.1.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (count.trans_eq s.size)) _),?_⟩
  exact bounds.2.trans (congrArg (s.program.expandedLoad+·) s.size)

open Finset


/-- Count all the public row words and the private visits of the full staged
directory in a region, using the predecessor's true incidence widths. -/
theorem sewnPrograms_region (test : N.Site → Prop) :
    let result := sewnPrograms N lane B gw freeLane owner aligned oldEdge oldPort edge port progs
    localRecords out true result.fullFields.prior result.fullFields.payload test ≤
      localRecords out true progs.fullFields.prior progs.fullFields.payload test +
        1035*testedWidth (incoming N) test := by
  intro result
  have hs : testedWidth (fun v => boxCost true (result v).program.staticNodes (result v).program.expandedLoad) test ≤
      testedWidth (fun v => boxCost true (progs v).program.staticNodes (progs v).program.expandedLoad) test +
      1035*testedWidth (incoming N) test := by
    unfold testedWidth
    rw [mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro v _
    by_cases hv : test v
    · simp only [ite_eq_left hv,boxCost,recordCost,ite_true]
      have b := sewnPrograms_charges N lane B gw freeLane owner aligned oldEdge oldPort edge port progs v
      change (result v).program.staticNodes ≤ _ ∧ (result v).program.expandedLoad = _ at b
      omega
    · simp [hv]
  unfold localRecords
  rw [show ∀ a b c d extra : ℕ, a+b+c+d+extra = a+extra+b+c+d by intros; omega]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hs _) _) _

end Packing.SewnField

end BorderVNP
end Computability
end OAI
