import OAI.Hierarchy.DescentDatedOperandPipelineObserved

namespace OAI
/-! # Values of the eight physical expressions at the selected source occurrence -/
namespace Hierarchy.DescentDatedOperandCoordinates.Ticket

theorem fields_visible (blocks actor kind rank old key start peer mouth : ℕ)
    {x y : Fin 5 → ℕ} {r s : Fin 6 → ℕ}
    (x0 : x 0=y 0) (x1 : x 1=y 1) (x2 : x 2=y 2)
    (r2 : r 2=s 2) (r3 : r 3=s 3) (r4 : r 4=s 4) (r5 : r 5=s 5) :
    fields blocks actor kind rank old key start peer mouth x r=
      fields blocks actor kind rank old key start peer mouth y s := by
  simp only [fields,x0,x1,x2,r2,r3,r4,r5]

end Hierarchy.DescentDatedOperandCoordinates.Ticket

namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup DescentPackedZip DescentSixParty.Chronology
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable (g : Geometry) (v : Data g)

def ticketAt (j : Fin g.jobs) (h : Fin g.hosts) (k : Fin g.groups) : Fin 8 → ℕ :=
  let rawKey:=rawLaw g.paths (g.blocks*(g.cap*11)) g.digitBits 0 (fun i=>rawInputs g v j i h k)
  Ticket.fields g.blocks (v.origin j 0 h k).val (v.prior j 0 h k).val (rankV g v j 0 h k).val
    (v.origin j 2 h k).val rawKey.val (rawV g v j 6 h k).val (rawV g v j 7 h k).val (v.mouth j 1 h k).val
    (fun i=>(anchorV g v j i h k).val) (fun i=>(rawV g v j (i.castLE (by decide : 6≤8)) h k).val)

theorem final_ticket (j : Fin g.jobs) (h : Fin g.hosts) (k : Fin g.groups) (f : Fin 8) :
    finalLaw g f (fun i=>finalInputs g v j i h k)=((ticketAt g v j h k f:ℕ):Cell g.resultBits) :=by
  unfold finalLaw ticketAt
  apply congrArg (fun z : ℕ=>(z:Cell g.resultBits))
  apply congrFun
  apply Ticket.fields_visible <;> rfl

theorem observed_ticket (src : Sources g) {base w : ℕ} (m : Memory w)
    (held : Recorded g src v base m) (space : endAddress g base<2^w) :
    let body:=phase g src base w
    Step base (endAddress g base) body m ∧ ∀j f,
      Held g (endAddress g base) (body.image m) (expression g src base j f)
        (fun h k=>((ticketAt g v j h k f:ℕ):Cell g.resultBits)) :=by
  simpa only [final_ticket] using observed g src v m held space

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
