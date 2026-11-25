import OAI.Hierarchy.DescentTerminalArgumentCount
import OAI.Hierarchy.DescentTerminalMaskedReached

namespace OAI
/-! # Private scalar count on authentic reached hosts using three physical argument channels -/
namespace Hierarchy.DescentSixParty.Reached
open DescentCompiler DescentTerminalVertexFields DescentTerminalGraphPositions DescentTerminalSiteShelves
open DescentTerminalChronologicalBooks DescentKernelHistory
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {D : ℕ} {bw : P→ℕ} {world : MarkedWorld F D P bw}
    {G : PoweredGadget F} {price ε : ℝ} {S : AtomSchedule} {k age z degree wire hist p : ℕ}
    (R : Reached world G price ε S k age z degree wire hist) (L : Order world.graph (S.hostSize age) p) (same : L.home=R.home)
    {q t H N A w : ℕ} (i : Fin (S.hostSize age))
local notation "site" => L.site i

theorem private_home_arguments (data : BlockFields q t H N A w (S.groupCount age) (2^k))
    (r : ∀v : Fin (L.site i).nodes,Recipe (Fin t) (Fin ((L.site i).arity v))) (birth : Birth r)
    (hH : ∀v,Fintype.card (r v).Hidden≤H) (hN : ∀v,Fintype.card (r v).Node≤N)
    (hA : ∀v u,(r v).arity u≤A) (hw : ∀v u,(r v).width u≤w) (short : ∀v,(L.site i).arity v≤q)
    (occupied : ∀c,blankAt data c≠0 ↔ ∃u,R.chart L same i u=c)
    (previous : ∀v,let book:=record site r birth hH hN hA hw short v
      ArgumentReads (venueField (cellAt data (R.rawResident L same i v))) (fun j=>(value book j).val)) :
    privateHome data=∑v,Fintype.card (r v).UsedWord := by
  let e:=((L.nodes i).symm.toEmbedding).trans (R.chart L same i)
  apply private_count_from_arguments data site r birth hH hN hA hw short e _ previous
  intro c
  rw [occupied]
  constructor
  · rintro ⟨u,hit⟩
    refine ⟨L.nodes i u,?_⟩
    change R.chart L same i ((L.nodes i).symm (L.nodes i u)) = c
    rw [Equiv.symm_apply_apply]
    exact hit
  · rintro ⟨u,hit⟩
    exact ⟨(L.nodes i).symm u,hit⟩

end
end Hierarchy.DescentSixParty.Reached

end OAI
