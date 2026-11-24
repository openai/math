import OAI.Computability.VPVNP.CompressorSurvivingNative
import OAI.Computability.VPVNP.CompressorSourceTransport

/-!
# External footprint of one surviving subdivision call

The call reads its four input words before issuing the thirteen stores.
This identifies the physical addresses protected against scheduler writes.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.ShrinkSliceSweep.SurvivingNative

open BurstRAM RowRecipe
variable {w : ℕ}

private def rd (m : Memory w) (a : Word w) : Event w := .read a (m a.val)

private def inputLog (a : Fin 4 → Word w) (m : Memory w) : List (Event w) :=
  List.replicate 10 .tick ++ [rd m (a 0),.tick,rd m (a 1)] ++ List.replicate 5 .tick ++
    [rd m (a 2)] ++ List.replicate 4 .tick ++ [rd m (a 3)] ++ List.replicate 56 .tick

set_option maxRecDepth 8192 in
private theorem events (p : Public w) (st : Word w) (m : Memory w) :
    (report p st m).events = inputLog (readAddresses p st m) m ++ ScatterCall.storeLog (stores (read p st m)) := rfl

private def readCell : Event w → Option (Word w)
  | .read a _ => some a
  | _ => none

private def writeCell : Event w → Option (Word w)
  | .write a _ => some a
  | _ => none

private theorem readInputs (a : Fin 4 → Word w) (m : Memory w) :
    (inputLog a m).filterMap readCell = List.ofFn a := rfl

private theorem noWrites (a : Fin 4 → Word w) (m : Memory w) :
    (inputLog a m).filterMap writeCell = [] := rfl

private theorem storeCells (xs : List (Word w × Word w)) :
    (ScatterCall.storeLog xs).filterMap readCell = [] ∧
    (ScatterCall.storeLog xs).filterMap writeCell = xs.map Prod.fst := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons x xs ih =>
    simpa only [ScatterCall.storeLog,List.map_cons,List.filterMap_cons,readCell,writeCell] using
      And.intro ih.1 (congrArg (x.1 :: ·) ih.2)

theorem footprint (p : Public w) (st : Word w) (m : Memory w) :
    SourceTransport.Reads (fun x => ∃ f, (readAddresses p st m f).val = x) (report p st m).events ∧
    SourceTransport.Writes (fun x => ∃ f, ((read p st m).addresses f).val = x) (report p st m).events := by
  constructor <;> intro a v hv
  · have h : a ∈ (report p st m).events.filterMap readCell := List.mem_filterMap.mpr ⟨_,hv,rfl⟩
    rw [events,List.filterMap_append,readInputs,(storeCells _).1,List.append_nil] at h
    obtain ⟨f,hf⟩ := List.mem_ofFn.mp h
    exact ⟨f,congrArg Fin.val hf⟩
  · have h : a ∈ (report p st m).events.filterMap writeCell := List.mem_filterMap.mpr ⟨_,hv,rfl⟩
    rw [events,List.filterMap_append,noWrites,(storeCells _).2,List.nil_append] at h
    simp only [stores,List.map_ofFn,List.mem_ofFn,Function.comp_apply] at h
    obtain ⟨f,hf⟩ := h
    exact ⟨f,congrArg Fin.val hf⟩

end CompressorRecords.ShrinkSliceSweep.SurvivingNative

end VPVNP
end Computability
end OAI
