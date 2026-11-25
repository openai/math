import OAI.Hierarchy.TaggedWideScatter
import OAI.Hierarchy.ProtocolRAMDependentSeries

namespace OAI
/-! # Preserving earlier input and output words during the concrete ordered replay -/
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators
variable {W n lo hi : ℕ} {pages : Fin (n+1)→Scatter}

/-- Each result may contain an existential witness (for instance the live
participant embedding), with all of its numerical fields on this page. -/
theorem Ordered.run_prefix (order : Ordered lo hi pages) (original : Memory W)
    (post : Fin (n+1)→Memory W→Prop)
    (locality : ∀i s t,(∀a,a<(pages i).stop→t a=s a)→post i s→post i t)
    (step : ∀i s,(∀a,a<lo→s a=original a)→(∀j,j < i → post j s)→
      ∃t,((pages i).code W).Exec s t (pages i).ticks ∧ post i t ∧ ∀a,a<(pages i).floor→t a=s a) :
    ∃out,(ProcedureBank.program n (fun i=>(pages i).code W)).Exec original out (∑i,(pages i).ticks) ∧
      (∀i,post i out) ∧ ∀a,a<lo→ out a=original a := by
  let inv (k : ℕ) (s : Memory W) := (∀a,a<lo→s a=original a) ∧ ∀i:Fin (n+1),i.val<k→post i s
  have initial : inv 0 original:=⟨fun _ _=>rfl,fun _ bad=>False.elim (by omega)⟩
  have next (i : Fin (n+1)) (s : Memory W) (prev : inv i.val s) :
      ∃t,((pages i).code W).Exec s t (pages i).ticks ∧ inv (i.val+1) t := by
    obtain ⟨t,run,now,frame⟩:=step i s prev.1 (fun j lt=>prev.2 j lt)
    refine ⟨t,run,fun a hx=>(frame a (hx.trans_le (order.lower i))).trans (prev.1 a hx),?_⟩
    intro j bound
    by_cases same : j=i
    · subst j;exact now
    · have before : j < i := by
        have neq : j.val≠i.val:=fun e=>same (Fin.ext e)
        change j.val < i.val;omega
      exact locality j s t (fun a small=>frame a (small.trans_le (order.separate j i before))) (prev.2 j before)
  obtain ⟨s,ran,low,kept⟩:=ProtocolRAMDependentSeries.chain n _ _ inv original initial next
  exact ⟨s,ran,fun i=>kept i i.isLt,low⟩

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
