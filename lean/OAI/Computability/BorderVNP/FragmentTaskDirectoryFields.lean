import OAI.Computability.BorderVNP.FragmentDirectoryReturn
import OAI.Computability.BorderVNP.FiniteEvaluatorCubeOpenRoom

/-! # Physical task-frame readback after native emission and stable bucketing -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.FragmentRows

open VPVNP.BurstRAM SignedTaskArena

variable {w team frame offsets ctl live ports : ℕ} {a : SignedTaskArena.Layout} {f : Layout} {m : Memory w}
    {fit : f.Fits w (readings m)} {cells : a.fragments.cells=f.cells} (e : SparseEmission a f m fit cells)

local notation "old" => readings m
local notation "newMem" => readings e.output
local notation "task" => a.tasks team frame offsets ctl
local notation "R" => a.controlRows team frame offsets ctl live ports

/-- Task-builder frame fields and eight task allocation operands in the
actual native bucket's final RAM. They are the real report/control input
words, outside both the compact fragment arrays and count publication. -/
theorem SparseEmission.task_fields (control : f.control=ctl) (place : a.SparsePlacement frame ctl)
    (outer : (R).Fields old)
    (calls : old (frame+14)=a.before.limit) (tasks : old (frame+89)=(task).tasks)
    (words : ∀ i : Fin 37, old (ctl+i.val)=a.controls i.val) : (task).Fields newMem := by
  have before := place.beforeControl
  have banks := place.beforeBank
  obtain ⟨cellStop,stop,_,_,_,_⟩ := a.sparse_order place.cells
  have fr (i : ℕ) (hi : i < 112) : (newMem) (frame+i) = old (frame+i) :=
    e.original _ (by rw [control]; omega) (.inl (by omega))
  have hdr (i : Fin 8) : (newMem) (ctl+i.val) = a.controls i.val := by
    have n := i.isLt
    exact (e.original _ (by rw [control]; omega) (.inl (by omega))).trans (words ⟨i.val,by omega⟩)
  obtain ⟨id,num,host,ends,nc,_,_,ptr⟩ := outer.frame
  have atZero := fr 0 (by decide)
  simp only [Nat.add_zero] at atZero
  have cZero := hdr ⟨0,by decide⟩
  simp only [Nat.add_zero] at cZero
  constructor
  · exact ⟨atZero.trans id,(fr 7 (by decide)).trans nc,(fr 14 (by decide)).trans calls,
      (fr 15 (by decide)).trans num,(fr 72 (by decide)).trans host,(fr 87 (by decide)).trans ends,
      (fr 89 (by decide)).trans tasks,(fr 92 (by decide)).trans ptr⟩
  · exact ⟨cZero,hdr 1,hdr 2,hdr 3,hdr 4,hdr 5,hdr 6,hdr 7⟩

end RoutingISA.FragmentRows

end BorderVNP
end Computability
end OAI
