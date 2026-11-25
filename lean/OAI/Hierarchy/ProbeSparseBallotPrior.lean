import OAI.Hierarchy.ProbeSparsePrintedRows
import OAI.Hierarchy.TaggedWideSpillAfterRoles
import OAI.Hierarchy.TaggedWideVacantBallot
import OAI.Hierarchy.ProbeSparseParticipantROM

namespace OAI
/-! # Keep the actual incoming auxiliary role-sheet observations of a ballot -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.WideCPU
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
variable {W T : ℕ}

/-- The witness is the memory supplied to this exact scatter, with the prior chronological
records the caller has already established there. Only the scatter's own range
is inspected in its resulting heap. -/
def printedWithPrior (shape : Shape) (sites rom start : ℕ) (fields : Fields shape)
    (live : Finset (Fin shape.candidates)) {page : Scatter} (same : page=shape.sheet sites rom start fields)
    (prior : Memory W→Prop) : PageResult W page := by
  subst page
  refine ⟨fun out=>∃input,prior input ∧ printedSiteRows shape sites start fields live input out,?_⟩
  intro x y agree
  rintro ⟨input,before,party,names,cells⟩
  refine ⟨input,before,party,names,fun s c=>(agree _ ?_ ?_).trans (cells s c)⟩
  · change start+1-1≤ start+1+_;omega
  · have len : (SiteScatter.pos s c).val < sites * shape.columns := (SiteScatter.pos s c).isLt
    change start + 1 + (SiteScatter.pos s c).val < start + 1 + sites * shape.columns + 2 * shape.count
    omega

theorem printedWithPrior.holds (shape : Shape) (sites rom start : ℕ) (fields : Fields shape)
    (live : Finset (Fin shape.candidates)) {page : Scatter} (same : page=shape.sheet sites rom start fields)
    (prior : Memory W→Prop) {input out : Memory W} (before : prior input)
    (reads : printedSiteRows shape sites start fields live input out) :
    (printedWithPrior shape sites rom start fields live same prior).holds out := by
  subst page
  exact ⟨input,before,reads⟩

/-- Feeding a date allocates a real zero-row sheet in the public program.
Its measured instruction count applies and the entire physical memory survives. -/
theorem Dated.empty_ballot_at (g : Dated T) (rom root : ℕ) (j : Fin T) (fields : Fields (g.ballot j))
    (table : Fin g.siteDirectorySize→ℕ) (transport : Fin g.rawEdges→Bool) (source input : Memory W)
    (fixed : ∀i,g.ballotROM rom j≤ i→i<g.ballotROM rom j+(g.ballot j).advice g.sites→
      input i=g.words rom table transport source i)
    (empty : (g.ballot j).parties=0 ∧ (g.ballot j).columns=0)
    (guard : 3*g.romEnd rom+2≤root) (room : g.controlStart root<2^W) :
    let page:=(g.ballot j).sheet g.sites (g.ballotROM rom j) (g.ballotStart root j) fields
    (page.code W).Exec input input page.ticks := by
  intro page
  have origin:=Shape.Origin.copy_low _ (g.ballot_origin rom table transport source j) fixed
  have tips : g.ballotROM rom j+(g.ballot j).advice g.sites≤g.controlROMStart rom:=extent _ _ j
  have endROM : g.controlROMStart rom≤g.romEnd rom:=by dsimp only [Dated.romEnd,Dated.maskROM,endOf];omega
  have floor : root≤g.ballotStart root j:=by dsimp only [Dated.ballotStart,offset,Dated.rolesEnd];omega
  have upper : g.ballotStart root j+(g.ballot j).span g.sites≤g.controlStart root:=extent _ _ j
  have eligible:=PublicSheet.of_placement (g.ballot j) fields input origin (tips.trans endROM) (guard.trans floor)
    (upper.trans_lt room) (fun i=>False.elim (by have:=i.isLt;omega))
    (show (g.ballot j).parties≤2^W by omega) (by omega)
  intro P R K machine pc reg pub exit installed data cfg mem entry same
  exact Shape.empty_exec (g.ballot j) g.sites (g.ballotROM rom j) (g.ballotStart root j) fields input
    (by simp [Shape.count,empty.1]) empty.2 (by have:=eligible.space;omega) eligible.address eligible.value
    machine pc reg pub exit installed data cfg mem entry same

end Hierarchy.ProtocolRAM.Calendar.WideCPU
end

end OAI
