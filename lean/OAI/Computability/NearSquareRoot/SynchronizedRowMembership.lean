import OAI.Computability.NearSquareRoot.SynchronizedBoxPlanDepth

/-! # Provenance and kind of each nonidle scheduled instruction -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace SynchronizedLayers.ScheduleProgram

theorem kindCode_injective : Function.Injective kindCode := by
  intro a b
  cases a <;> cases b <;> decide

/-- A live field comes from this block's own word, and its kind equals the row tag. -/
theorem plan_read_spec {X : Type} {n : ℕ} (kind : X → Kind) (w : Fin n → List X) (D : ℕ)
    (r : Row X) (hr : r ∈ plan kind (List.ofFn w,IntegerMultiplication.Code.tally D))
    (i : Fin n) (x : X) (hx : readBlock r i.val = some x) :
    x ∈ w i ∧ kindCode (kind x) = r.1 := by
  rw [plan_eq_schedule] at hr
  obtain ⟨l,hl,rfl⟩ := List.mem_map.mp hr
  have hx' : l.action i = some x := by simpa using hx
  have hm : x ∈ (schedule (fun _ => kind) D w).filterMap (fun t => t.action i) :=
    List.mem_filterMap.mpr ⟨l,hl,hx'⟩
  rw [schedule_filterMap] at hm
  exact ⟨List.mem_of_mem_take hm, congrArg kindCode (l.compatible i x hx')⟩

end SynchronizedLayers.ScheduleProgram

namespace ShortFourier.BatchWord

open IntegerMultiplication.Code SynchronizedLayers SynchronizedLayers.ScheduleProgram SynchronizedBlocks

private theorem orient_mem {X : Type} {dir : Bool} {w : List X} {r : Bool × X}
    (hr : r ∈ orientRows (dir,w)) : r.1 = dir ∧ r.2 ∈ w := by
  cases dir
  · change r ∈ w.map (fun x => (false,x)) at hr
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
    exact ⟨rfl,hu⟩
  · change r ∈ w.reverse.map (fun x => (true,x)) at hr
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hr
    exact ⟨rfl,List.mem_reverse.mp hu⟩

/-- The adjoint branch reverses row order and preserves all local opcode fields. -/
theorem directed_mem {k : ℕ} {dir : Bool} {r : Bool × Row SlotDescriptor}
    (hr : r ∈ directedPlan (dir,tally k)) : r.1 = dir ∧ r.2 ∈ boxPlan (tally k) :=
  orient_mem (w := boxPlan (tally k)) (dir := dir) hr

theorem directed_read_spec {k : ℕ} {dir : Bool} {r : Bool × Row SlotDescriptor}
    (hr : r ∈ directedPlan (dir,tally k)) (i : Fin ((CoprimeBox.box k).length/4))
    {z : SlotDescriptor} (hz : readBlock r.2 i.val = some z) :
    z ∈ localSlots (block (List.ofFn fun t : Fin (count i) => tally (paddedLog (BoxFin.modulus (CoprimeBox.box k) (axis i t))))) ∧
    kindCode (slotKind z) = r.2.1 := by
  have h := (directed_mem hr).2
  rw [boxPlan_eq] at h
  exact plan_read_spec slotKind _ _ r.2 h i z hz

end ShortFourier.BatchWord

end NearSquareRoot
end Computability
end OAI
