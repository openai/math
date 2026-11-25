import OAI.Computability.BorderVNP.FragmentRowsSparsePatch
import OAI.Computability.BorderVNP.RoutingISAScheduleClockNativeInput

/-! # Control and width words retained by the actual supplemental writer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM CellPacket CellSparse CellPacket.Supplement.Batch TypedTaskBuilder

variable {w : ℕ} {Site : Type} (l : CellControlRows.Layout) (raw : ℕ → ℕ) (p : ℕ → Placed Site)
    (geom : ℕ → ℕ) (extra : ℕ → List Record) (m : Memory w) (room : l.toLayout.Room raw w)
    (span : ∀ c < l.cells, raw (l.sorted+l.padded+(l.stops+c))-raw (l.sorted+l.padded+c)-1=3*((p c).parts.length+3))

include room span

set_option quotPrecheck false

local notation "count" => l.before raw l.cells
local notation "owned" => produced l raw p geom extra
local notation "patched" => written m (fun j => (owned j).cell) count

/-- The native prepass and exterior encoder both load their actual public
controls and the published owned count. The occupied-count word written by
the earlier fragment emitter is outside this list of scalar inputs. -/
theorem produced_headers (a : SignedTaskArena.Layout) (fields : l.toLayout.Fields raw)
    (image : readings m=l.toLayout.published raw) (width : raw (l.frame+30)=w)
    (table : l.tasks=(a.tasks 0 0 0 0).tasks) (four : l.four=a.before.four)
    (controller : ∀ k ∈ [11,17,31,32,34,35,36], raw (l.control+k)=a.controls k)
    (frameLow : l.frame+112 ≤ l.sorted ∧ l.frame+112 ≤ l.merged)
    (controlLo : l.frame+112 ≤ l.control) (controlHi : l.control+37 ≤ l.calls ∧ l.control+37 ≤ l.tasks)
    (ctrlSorted : l.control+37 ≤ l.sorted ∨ l.sorted+l.padded ≤ l.control)
    (ctrlMerged : l.control+37 ≤ l.merged ∨ l.merged+l.cells ≤ l.control) :
    let sl := SparseExterior.batchLayout a l.frame l.control count
    readings m (l.frame+92)=l.control ∧ readings m (l.frame+89)=sl.tasks ∧ readings m (l.frame+90)=count ∧
    readings m (l.control+11)=l.four ∧ sl.Loaded (readings patched) ∧ readings patched (l.frame+30)=w := by
  intro sl
  let patch : SignedTaskArena.SparsePatch (w:=w) Site l raw := ⟨m,p,geom,extra,room,image,span⟩
  have frameRead (j : ℕ) (hj : j<112) (ne : j≠90) : readings m (l.frame+j)=raw (l.frame+j) := by
    rw [image]; exact l.toLayout.published_field raw room ne hj
  have frameSame (j : ℕ) (hj : j<112) : readings patched (l.frame+j)=readings m (l.frame+j) :=
    patch.preserved (l.frame+j) (.inl (by omega)) (.inl (by omega))
  have ctrlRead (j : ℕ) (hj : j<37) : readings m (l.control+j)=raw (l.control+j) := by
    rw [image,TypedTaskBuilder.Layout.published,Function.update_of_ne (by omega : l.control+j≠l.frame+90)]
    apply l.toLayout.image_outside raw _ le_rfl
    rintro (ha|⟨c,_,ha⟩|ha)
    · change l.tasks ≤ l.control+j ∧ _ at ha; omega
    · change l.control+j=l.calls+3*c at ha; omega
    · change l.control+j=l.frame+90 at ha; omega
  have ctrlSame (j : ℕ) (hj : j<37) : readings patched (l.control+j)=readings m (l.control+j) :=
    patch.preserved (l.control+j)
      (ctrlSorted.elim (fun _ => Or.inl (by omega)) (fun _ => Or.inr (by omega)))
      (ctrlMerged.elim (fun _ => Or.inl (by omega)) (fun _ => Or.inr (by omega)))
  have get (j : ℕ) (hj : j ∈ [11,17,31,32,34,35,36]) : readings patched (l.control+j)=a.controls j := by
    have lt : j<37 := by simp only [List.mem_cons,List.not_mem_nil,or_false] at hj; omega
    exact (ctrlSame j lt).trans ((ctrlRead j lt).trans (controller j hj))
  obtain ⟨_,_,_,_,_,_,taskBase,pointer⟩ := fields.outer
  have ptr := (frameRead 92 (by decide) (by decide)).trans pointer
  have tab : readings m (l.frame+89)=sl.tasks := (frameRead 89 (by decide) (by decide)).trans (taskBase.trans table)
  have num : readings m (l.frame+90)=count := by rw [image]; exact Function.update_self ..
  refine ⟨ptr,tab,num,(ctrlRead 11 (by decide)).trans ((controller 11 (by decide)).trans four.symm),?_,
    (frameSame 30 (by decide)).trans ((frameRead 30 (by decide) (by decide)).trans width)⟩
  exact ⟨(frameSame 90 (by decide)).trans num,(frameSame 89 (by decide)).trans tab,(frameSame 92 (by decide)).trans ptr,
    get 17 (by decide),get 31 (by decide),get 32 (by decide),get 34 (by decide),get 35 (by decide),get 36 (by decide)⟩

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
