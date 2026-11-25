import OAI.Hierarchy.DescentRegisterTimelineCore
import OAI.Hierarchy.DescentCommonDateFamily

namespace OAI
/-! # Native execution and old words on the chronological register program -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
variable {w : ℕ} {Cut : ℕ→Type*} (issue : ∀i,Cut i→Position→Move w→Prop)
    (initial : Position) (header : ℕ)
local notation "at_" => position issue initial
local notation "cpu" => date issue initial

/-- An issued instruction can write its count to an earlier designated header. -/
structure Protected (code : DateCode w) (floor header : ℕ) : Prop where
  run : ∀m,∃out,code.Runs m out ∧ ∀z,z < floor → z ≠ header → out z = m z
  cheap : code.cheap

private theorem empty_protected (w floor header : ℕ) :
    Protected (DateCode.reset (scan w 0 0 .row) 4) floor header :=by
  constructor
  · intro m
    have zrun : (scan w 0 0 .row).Exec m (image 0 0 .row m) 4 :=
      scan_exec 0 0 .row m trivial (Nat.two_pow_pos w)
    have unmodified : image 0 0 .row m=m:=fillSegment_zero ..
    exact ⟨image 0 0 .row m,zrun,fun z _ _=>congrFun unmodified z⟩
  · exact scan_cheap w 0 0 .row

private theorem selected_protected (p : Position) (i : ℕ)
    (usable : ∀(c : Cut i) (m : Move w),issue i c p m→Protected m.code p.floor header) :
    Protected (selected issue i p).code p.floor header :=by
  classical
  by_cases hit : ∃m : Move w,(∃c : Cut i,issue i c p m) ∧ p.floor ≤ m.next.floor
  · have h : ∃c : Cut i,issue i c p (Classical.choose hit):=(Classical.choose_spec hit).1
    have chosen : selected issue i p=Classical.choose hit:=dite_eq_left hit
    rw [chosen]
    exact usable (Classical.choose h) (Classical.choose hit) (Classical.choose_spec h)
  · have absent : selected issue i p=⟨.reset (scan w 0 0 .row) 4,p⟩:=dite_eq_right hit
    rw [absent]
    exact empty_protected w p.floor header

theorem instruction_run (localRun : ∀(j : ℕ) (c : Cut j) (v : Move w),
    issue j c (position issue initial j) v → Protected v.code (position issue initial j).floor header) (i : ℕ) : Protected (cpu i) (at_ i).floor header :=
  selected_protected issue header (at_ i) i (localRun i)

theorem instruction_history (localRun : ∀(j : ℕ) (c : Cut j) (v : Move w),
    issue j c (position issue initial j) v → Protected v.code (position issue initial j).floor header) (m : Memory w) (i : ℕ) :
    (cpu i).Runs (DateCode.history cpu m i) (DateCode.history cpu m (i+1)) ∧
    (cpu i).cheap ∧ ∀z,z < (at_ i).floor → z ≠ header→
      DateCode.history cpu m (i+1) z=DateCode.history cpu m i z:=by
  let old:=DateCode.history cpu m i
  have ok : Protected (cpu i) (at_ i).floor header:=instruction_run issue initial header localRun i
  obtain ⟨out,ran,stable⟩:=ok.run old
  have step : DateCode.history cpu m (i+1)=out:=DateCode.nextMemory_eq (cpu i) (m:=old) (out:=out) ran
  rw [step]
  exact ⟨ran,ok.cheap,stable⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
