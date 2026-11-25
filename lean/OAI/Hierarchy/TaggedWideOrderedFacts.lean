import OAI.Hierarchy.TaggedWideScatterOrder
import OAI.Hierarchy.TaggedWideOrderedPrefix

namespace OAI
/-! # Simultaneous readback after the dependent sparse phases -/
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators
variable {W n lo hi : ℕ} {pages : Fin (n+1)→Scatter}

theorem Ordered.run (order : Ordered lo hi pages) (original : Memory W)
    (post : Fin (n+1)→Memory W→Prop)
    (locality : ∀i s t,(∀a,(pages i).floor≤a→a<(pages i).stop→t a=s a)→post i s→post i t)
    (step : ∀i s,(∀a,a<lo→s a=original a)→(∀j,j < i→post j s)→
      ∃t,((pages i).code W).Exec s t (pages i).ticks ∧ post i t ∧ ∀a,a<(pages i).floor→t a=s a) :
    ∃out,(ProcedureBank.program n (fun i=>(pages i).code W)).Exec original out (∑i,(pages i).ticks) ∧
      (∀i,post i out) ∧ ∀a,a<lo→ out a=original a :=
  order.run_prefix original post (fun i s t equal held=>
    locality i s t (fun a _ below=>equal a below) held) step

end Hierarchy.ProtocolRAM.Calendar.WideCPU

end OAI
