import OAI.Hierarchy.TaggedWidePageSweep
import OAI.Hierarchy.ProbeSparseParticipantSheet

namespace OAI
/-! # Retaining the actual signed candidate-party fields of a paid scatter -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {W : ℕ} (shape : Shape) (sites rom start : ℕ) (fields : Fields shape)
    (live : Finset (Fin shape.candidates))
local notation "rows" => {i : Fin shape.candidates // i∈live} × Fin shape.parties

def printedSiteRows (input output : Memory W) : Prop :=
  ∃party : rows ↪ Fin sites,
    (∀u : rows,(fields.site u.2).eval input (u.1.val.val:Word W)=((party u).val:Word W)) ∧
    ∀s c,output (start+1+(SiteScatter.pos s c).val)=
      SiteScatter.table party (fun u j=>(fields.value u.2 j).eval input (u.1.val.val:Word W)) s c

def originalBallotFact (floor : ℕ) (origin : Memory W) :
    PageResult W (shape.sheet sites rom start fields) where
  holds output:=∃input,(∀a,a<floor→input a=origin a) ∧ printedSiteRows shape sites start fields live input output
  localize x y agree := by
    rintro ⟨inp,frame,party,ids,observed⟩
    refine ⟨inp,frame,party,ids,?_⟩
    intro s c
    apply (agree _ ?_ ?_).trans (observed s c)
    · change start+1-1≤ start+1+_;omega
    · have bound : (SiteScatter.pos s c).val < sites * shape.columns :=
        (SiteScatter.pos s c).isLt
      change start + 1 + (SiteScatter.pos s c).val <
        start + 1 + sites * shape.columns + 2 * shape.count
      omega

def placedBallotFact {page : Scatter} (same : page=shape.sheet sites rom start fields)
    (floor : ℕ) (origin : Memory W) : PageResult W page :=
  same.symm ▸ originalBallotFact shape sites rom start fields live floor origin

theorem placedBallotFact_issued {page : Scatter} (same : page=shape.sheet sites rom start fields)
    (floor : ℕ) (origin : Memory W)
    (run : ∀processing,(∀i,i<floor→processing i=origin i)→
      ∃out,(page.code W).Exec processing out page.ticks ∧
        printedSiteRows shape sites start fields live processing out ∧ ∀a,a<page.floor → out a=processing a) :
    (placedBallotFact shape sites rom start fields live same floor origin).Issued floor origin := by
  subst page
  intro processing low
  obtain ⟨out,exec,facts,kept⟩:=run processing low
  exact ⟨out,exec,⟨processing,low,facts⟩,kept⟩

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
