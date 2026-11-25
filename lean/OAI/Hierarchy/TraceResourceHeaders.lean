import OAI.Hierarchy.TraceResourceRoom
import OAI.Hierarchy.TraceResourceMount

namespace OAI
/-! # Installing the two fixed scan headers from common public words -/
namespace Hierarchy.TraceAdmission.Resources
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat
open RAM RAM.PhysicalProcedure Diagonal.NavigationPass
open scoped Fin.CommRing Classical

def headerWords (base dp directory stages : ℕ) (p : Parameters ℕ) : List ℕ :=
  [base+1, dp,(stages+1)*p.lanes,directory+44,p.lanes,
    base+6,p.scratch,(p.lanes+1)*(p.directions+1),p.resources,p.roots*(p.directions+2),
    p.lanes,p.roots,p.directions,p.pairSpan,p.band,p.cap,p.heads,p.links,p.scratch,p.resources,p.charges,p.firstFinal]

/-- One 67-tick program installs both complete headers while preserving the
incoming register, charge and source graph arrays. -/
theorem header_spec {W : ℕ} (base dp dir stages : ℕ) (p : Parameters ℕ) :
    (mount W base (headerWords base dp dir stages p)).Spec (fun _=>True)
      (fun m o=>o=mounted base (headerWords base dp dir stages p) m) 67 :=
  mount_spec base _

theorem header_ready {W : ℕ} (base dp dir stages : ℕ) (p : Parameters ℕ) (m : Memory W)
    (room : base+22≤2^W)
    (words : ∀ v ∈ headerWords base dp dir stages p,v<2^W) :
    let out:=mounted base (headerWords base dp dir stages p) m
    (out base).val=base+1 ∧ (out (base+1)).val=dp ∧
    (out (base+2)).val=(stages+1)*p.lanes ∧ (out (base+3)).val=dir+44 ∧
    (out (base+4)).val=p.lanes ∧ Header (base+5) (base+6) p out := by
  let xs:=headerWords base dp dir stages p
  intro out
  have atWord (i : Fin 22) : (out (base+i.val)).val=xs[i.val]'(i.isLt) := by
    change (mounted base xs m (base+i.val)).val=_
    rw [mounted_at base xs m i room]
    exact Fin.val_cast_of_lt (words _ (List.getElem_mem _))
  refine ⟨?_,atWord 1,atWord 2,atWord 3,atWord 4,?_⟩
  · simpa [xs,headerWords] using atWord 0
  · refine ⟨atWord 5,atWord 6,?_,?_,?_,?_⟩
    · simpa [xs,headerWords,Nat.add_assoc] using atWord 7
    · simpa [xs,headerWords,Nat.add_assoc] using atWord 8
    · simpa [xs,headerWords,Nat.add_assoc] using atWord 9
    · intro j
      have hit:=atWord (⟨10+j.val,by omega⟩ : Fin 22)
      fin_cases j <;> simpa [xs,headerWords,Nat.add_assoc] using hit

end Hierarchy.TraceAdmission.Resources

end OAI
