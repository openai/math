import OAI.Computability.BorderVNP.CubeHostScatterPhysicalEnds
import OAI.Computability.BorderVNP.CubeHostScatterTeamClock

/-! # The scheduled team clock on the actual sparse host cable directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.HostScatter

open Physical NativeIntervals HostAddress Crossing Tally VPVNP.MotifBase
open RoutingISA VPVNP.BurstRAM
open scoped Classical

variable {D m n d blocks b h K s : ℕ} {P : Type*} {bits : P → ℕ} {Cell : Type}
    {N : Network D P bits} {cell : N.Site → Cell} {il : NativeIntervals.Layout} {l : Layout}
    {before dir mem : ℕ → ℕ} {ord : N.CrossingEdge cell ≃ Fin m} {row : Fin m ↪o Fin il.count}
    {cells : Cell ↪ ℕ} {label : Cell → Label (n+1) d} {code : Label (n+1) d ↪ Fin il.alphabet}
    (data : ResidentRows l il before dir mem n d blocks b h K s)
    (rows : PhysicalRows N cell il before ord row cells label code)

set_option maxHeartbeats 650000

/-- The resident scatter directory has exactly the physical per-bin loads,
including sparse holes and zero-width records. Its owner fetch on a live
endpoint is the scheduled owner of the original endpoint label. -/
noncomputable def ResidentRows.scheduledCables (hd : 0<d) (axis : Fin (n+1)) (owner : Fin d → ℕ)
    (cellOwner : ∀ c, mem (l.cells+2*cells c)=owner (label c axis))
    (cap : ∀ p, load (cablePair ord (crossSrc N cell) (crossDst N cell) label)
      (crossWidth N cell ∘ ord.symm) p ≤ blocks*(h*b)) :
    l.ScheduledCables mem (blocks*(h*b)) axis owner := by
  let kept (i : Fin m) : Fin l.count := Fin.cast data.count.symm (row i)
  have injective : Function.Injective kept := fun i j h => row.injective (Fin.ext (congrArg (fun x : Fin l.count => x.val) h))
  let names := cablePair ord (crossSrc N cell) (crossDst N cell) label
  let blank : Label (n+1) d := fun _ => ⟨0,hd⟩
  let names' := Function.extend kept names (fun _ => (blank,blank))
  have placed (i : Fin m) : names' (kept i) = names i := injective.extend_apply ..
  have width (i : Fin m) : l.liveWidth mem (kept i) = crossWidth N cell (ord.symm i) := by
    obtain ⟨left,right,bits⟩ := data.endpoints (row i)
    change (if l.cell mem (row i).val false = l.cell mem (row i).val true then 0 else l.width mem (row i).val) = _
    rw [left,right,bits]
    rcases rows.cable i with ⟨a,b,span⟩ | ⟨same|none,zero⟩
    · have diff : cells (crossSrc N cell (ord.symm i)) ≠ cells (crossDst N cell (ord.symm i)) :=
        fun eq => (ord.symm i).property (cells.injective eq)
      rw [a,b,ite_eq_right diff,span]
    · rw [ite_eq_left same,zero]
    · simp [none,zero]
  have hole (j : Fin l.count) (miss : j ∉ Set.range kept) : l.liveWidth mem j = 0 := by
    let r := Fin.cast data.count j
    have absent : r ∉ Set.range row := by
      rintro ⟨i,hi⟩
      exact miss ⟨i,Fin.ext (congrArg (fun z : Fin il.count => z.val) hi)⟩
    obtain ⟨a,b,span⟩ := data.endpoints r
    change (if l.cell mem j.val false = l.cell mem j.val true then 0 else l.width mem j.val) = 0
    change l.cell mem j.val false = _ at a
    change l.cell mem j.val true = _ at b
    change l.width mem j.val = _ at span
    rw [a,b,span]
    rcases rows.holes r absent with eq | zero
    · simp [eq]
    · simp [zero]
  refine ⟨names',fun p => ?_,?_⟩
  · apply le_trans _ (cap p)
    apply le_of_eq
    apply (Fintype.sum_of_injective kept injective _ _ ?_ ?_).symm
    · intro j miss
      simp [binWidth,hole j miss]
    · intro i
      simp [binWidth,placed,width,names]
  · intro j positive split
    have live : l.liveWidth mem j ≠ 0 := by simpa [Layout.liveWidth,split] using positive
    obtain ⟨i,rfl⟩ : j ∈ Set.range kept := by
      by_contra miss
      exact live (hole j miss)
    have hw : 0 < N.width (ord.symm i).val := Nat.pos_of_ne_zero (fun hz => live ((width i).trans hz))
    have cols := (rows.cable i).resolve_right fun empty => hw.ne' empty.2
    have resident := data.endpoints (row i)
    have ends := And.intro (resident.1.trans cols.1) (resident.2.1.trans cols.2.1)
    rw [placed i]
    exact ⟨(congrArg (fun k => mem (l.cells+2*k)) ends.1).trans (cellOwner _),
      (congrArg (fun k => mem (l.cells+2*k)) ends.2).trans (cellOwner _)⟩

end Cube.HostScatter

end BorderVNP
end Computability
end OAI
