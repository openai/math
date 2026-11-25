import OAI.Computability.BorderVNP.CellSparseExteriorNativeBatchArena
import OAI.Computability.BorderVNP.CellSparseExteriorTyped
import OAI.Computability.BorderVNP.RoutingISACallModel

/-! # Physical separation for the sparse serializer's patched task and source rows -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.SparseExterior

open VPVNP.BurstRAM CellDispatch
open private batch_regions from OAI.Computability.BorderVNP.CellSparseExteriorNativeBatchArena

variable (a : SignedTaskArena.Layout) (frame ctl count : ℕ) (owned : ℕ → Owned)
local notation "l" => batchLayout a frame ctl count

private theorem output_windows
    (global : ∀ i < count, (owned i).global < a.fragments.cells)
    (width : ∀ i < count, (owned i).field.bytes.length ≤ a.fragments.stride) (i : ℕ) (hi : i < count) :
    a.fragments.external ≤ (owned i).dest l ∧ (owned i).dest l+(owned i).field.bytes.length ≤ a.fragments.counts ∧
    a.fragments.counts+(owned i).global < a.fragments.limit ∧ a.fragments.limit ≤ (l).tasks := by
  have pos := global i hi
  have size := width i hi
  have last := Nat.mul_le_mul_right a.fragments.stride (Nat.succ_le_of_lt pos)
  rw [Nat.succ_mul] at last
  obtain ⟨low,high⟩ := batch_regions a
  change a.fragments.external ≤ a.fragments.external+(owned i).global*a.fragments.stride ∧ _ ≤ a.fragments.counts ∧ _ < a.fragments.limit ∧ a.fragments.limit ≤ (a.tasks 0 0 0 0).tasks
  change _ ∧ a.fragments.external+(owned i).global*a.fragments.stride+(owned i).field.bytes.length ≤ a.fragments.counts ∧ _ ∧ _
  simp only [FragmentArena.Layout.counts,FragmentArena.Layout.limit] at low ⊢
  omega

/-- Immutable physical input addresses lie below the compact streams, between their
count bank and the typed task table, or beyond all patched task rows. -/
def inputRegion (a : SignedTaskArena.Layout) (count addr : ℕ) : Prop :=
  addr < a.fragments.external ∨
  (a.fragments.limit ≤ addr ∧ addr < (a.tasks 0 0 0 0).tasks) ∨
  (a.tasks 0 0 0 0).tasks+7*count ≤ addr

/-- Every sparse store avoids the complete designated input regions. -/
theorem inputRegion_outside
    (global : ∀ i < count, (owned i).global < a.fragments.cells)
    (width : ∀ i < count, (owned i).field.bytes.length ≤ a.fragments.stride)
    {i addr : ℕ} (hi : i < count) (region : inputRegion a count addr) :
    (owned i).Outside l i addr := by
  obtain ⟨lo,hi',top,tasks⟩ := output_windows a frame ctl count owned global width i hi
  have fc : a.fragments.external ≤ a.fragments.counts := by rw [FragmentArena.Layout.counts]; omega
  have cl : a.fragments.counts < a.fragments.limit := by rw [FragmentArena.Layout.limit]; omega
  change (_ ∨ _) ∧ addr≠(l).tasks+7*i+2 ∧ addr≠(l).tasks+7*i+3 ∧ addr≠a.fragments.counts+(owned i).global
  change addr < a.fragments.external ∨ (a.fragments.limit ≤ addr ∧ addr < (l).tasks) ∨ (l).tasks+7*count ≤ addr at region
  rcases region with lower | middle | upper <;> omega

/-- Distinct owned global ordinals place every compact byte in its own physical stride.
The two patched external words are the only stores in each real seven-word task row. -/
theorem protected_from_arena (original : ℕ → TypedBatch.Task)
    (global : ∀ i < count, (owned i).global < a.fragments.cells)
    (width : ∀ i < count, (owned i).field.bytes.length ≤ a.fragments.stride)
    (distinct : Function.Injective (fun i : Fin count => (owned i.val).global))
    (sources : ∀ i < count, ∀ addr, TypedSources (original i) addr → inputRegion a count addr) :
    Protected l owned original := by
  have W := output_windows a frame ctl count owned global width
  have cl : a.fragments.counts < a.fragments.limit := by rw [FragmentArena.Layout.limit]; omega
  have separate (i j : ℕ) (hi : i<count) (hj : j<count) (ne : j≠i) :
      (owned i).dest l+(owned i).field.bytes.length ≤ (owned j).dest l ∨
      (owned j).dest l+(owned j).field.bytes.length ≤ (owned i).dest l := by
    have different : (owned j).global ≠ (owned i).global := fun eq =>
      ne (congrArg Fin.val (distinct (show (fun z : Fin count => (owned z.val).global) ⟨j,hj⟩ =
        (fun z : Fin count => (owned z.val).global) ⟨i,hi⟩ from eq)))
    have earlier (x y : ℕ) (hx : x<count) (less : (owned x).global < (owned y).global) :
        (owned x).dest l+(owned x).field.bytes.length ≤ (owned y).dest l := by
      have hxw := width x hx
      have step := Nat.mul_le_mul_right a.fragments.stride (Nat.succ_le_of_lt less)
      rw [Nat.succ_mul] at step
      change a.fragments.external+(owned x).global*a.fragments.stride+(owned x).field.bytes.length ≤ a.fragments.external+(owned y).global*a.fragments.stride
      omega
    rcases lt_or_gt_of_ne different with first | second
    · exact Or.inr (earlier j i hj first)
    · exact Or.inl (earlier i j hi second)
  constructor
  case scalar =>
    intro i hi j hj k hk
    obtain ⟨_,upper,top,tasks⟩ := W j hj
    change (_ ∨ _) ∧ (l).tasks+7*i+k≠(l).tasks+7*j+2 ∧ (l).tasks+7*i+k≠(l).tasks+7*j+3 ∧ (l).tasks+7*i+k≠a.fragments.counts+(owned j).global
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl | rfl | rfl | rfl <;> omega
  case bytes =>
    intro i hi k hk j hj ne
    obtain ⟨_,upper,_,tasks⟩ := W i hi
    have disjoint := separate i j hi hj ne
    change (_ ∨ _) ∧ _ ≠ (l).tasks+7*j+2 ∧ _ ≠ (l).tasks+7*j+3 ∧ _ ≠ a.fragments.counts+(owned j).global
    rcases disjoint with less | less <;> omega
  case self =>
    intro i hi k hk
    obtain ⟨_,upper,_,tasks⟩ := W i hi
    change _ ≠ (l).tasks+7*i+2 ∧ _ ≠ (l).tasks+7*i+3 ∧ _ ≠ a.fragments.counts+(owned i).global
    omega
  case counter =>
    intro i hi
    obtain ⟨_,_,top,tasks⟩ := W i hi
    change a.fragments.counts+(owned i).global ≠ (l).tasks+7*i+2 ∧ a.fragments.counts+(owned i).global ≠ (l).tasks+7*i+3
    omega
  case row =>
    intro i hi j hj ne k hk
    obtain ⟨_,upper,top,tasks⟩ := W j hj
    change (_ ∨ _) ∧ (l).tasks+7*i+k≠(l).tasks+7*j+2 ∧ (l).tasks+7*i+k≠(l).tasks+7*j+3 ∧ (l).tasks+7*i+k≠a.fragments.counts+(owned j).global
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
    rcases hk with rfl | rfl <;> omega
  case original =>
    intro i hi addr source j hj
    exact inputRegion_outside a frame ctl count owned global width hj (sources i hi addr source)

/-- Both the actual scalar frame and each three-word global call owner are outside all
sparse stores. The owner bank lies between the fragment arena and the seven-word tasks. -/
theorem frame_owners_outside (f : CellDispatch.Frame)
    (global : ∀ i < count, (owned i).global < a.fragments.cells)
    (width : ∀ i < count, (owned i).field.bytes.length ≤ a.fragments.stride)
    (early : frame+112 ≤ a.fragments.external) (calls : f.base=a.before.limit) (cells : f.count ≤ a.cube.cells) :
    (∀ i < count, ∀ j < 112, (owned i).Outside l i (frame+j)) ∧
    (∀ i < count, ∀ j < f.count, (owned i).Outside l i (f.address j)) := by
  have lower : a.fragments.limit ≤ a.before.limit := by
    rw [a.before.footprint]; change a.before.start ≤ _; omega
  refine ⟨fun i hi j hj => inputRegion_outside a frame ctl count owned global width hi (.inl (by omega)),?_⟩
  intro i hi j hj
  apply inputRegion_outside a frame ctl count owned global width hi
  apply Or.inr ∘ Or.inl
  change a.fragments.limit ≤ j*3+f.base ∧ j*3+f.base < a.before.limit+3*a.cube.cells
  omega

end RoutingISA.SparseExterior

end BorderVNP
end Computability
end OAI
