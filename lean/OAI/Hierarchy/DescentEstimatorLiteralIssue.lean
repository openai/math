import OAI.Hierarchy.DescentDatedImage
import OAI.Hierarchy.DescentPackedWalshMount

namespace OAI
/-! # Install the authentic integer estimator's relative tables on the current canvas -/
namespace Hierarchy.DescentPackedWalsh.EstimatorArena
open DescentPackedWalsh DescentSIMDLookup DescentPackedColony.Phase ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {w : ℕ} (E : EstimatorArena)
def header : Arena.Image w := ⟨E.origin,E.staticEnd,E.literal (fun _=>0)⟩

theorem header_eq (m : Memory w) (endRoom : E.staticEnd<2^w) :
    let I:=E.header (w:=w);
    I.program.Exec m (E.literal m) (4+10*(E.staticEnd-E.origin)) ∧
      CheapCode I.program ∧ DescentStaticWordColumn.names I.program=15*(E.staticEnd-E.origin+1) := by
  let I:=E.header (w:=w)
  obtain ⟨a,b,c,d,_,_,_⟩:=E.areas
  have stop : E.origin≤E.staticEnd:=(a.trans (b.trans (c.trans d))).trans (Nat.le_add_right ..)
  have space : I.low+I.length<2^w:=by change E.origin+(E.staticEnd-E.origin)<2^w;omega
  obtain ⟨run,table,frame⟩:=I.issue m space
  have eqOut : I.output m=E.literal m := by
    funext z
    by_cases lo:z<E.origin
    · exact (frame z (.inl lo)).trans (E.literal_before m lo).symm
    by_cases hi:z<E.staticEnd
    · exact (table z (Nat.le_of_not_gt lo) hi).trans
        (E.literal_inside (fun _=>0) m z (Nat.le_of_not_gt lo) hi)
    · have after:=Nat.le_of_not_gt hi
      exact (frame z (.inr after)).trans (E.literal_after m after).symm
  exact ⟨eqOut ▸ run,I.hardware⟩

/-- The static installation preserves both true coefficient columns and every packed source
word, and the solver's literal-read condition becomes a fixed-point equation on its own input. -/
theorem original_pages (m : Memory w) (fit : E.Fits w) :
    (∀a,E.literal (E.literal m) a=E.literal m a) ∧
    (∀i : Fin E.hosts,E.literal m (E.depthRows.base+i.val)=m (E.depthRows.base+i.val)) ∧
    (∀i : Fin E.hosts,E.literal m (E.gainRows.base+i.val)=m (E.gainRows.base+i.val)) ∧
    (∀a,E.start≤a→E.literal m a=m a) := by
  have immutable (a : ℕ) : E.literal (E.literal m) a=E.literal m a := by
    by_cases early:a<E.origin
    · exact E.literal_before _ early
    by_cases inside:a<E.staticEnd
    · exact E.literal_inside _ _ _ (Nat.le_of_not_gt early) inside
    · exact E.literal_after _ (Nat.le_of_not_gt inside)
  have bank (B : Bank) (rows : E.hosts≤B.size)
      (apart : B.base+B.size≤E.origin ∨ E.staticEnd≤B.base) (i : Fin E.hosts) :
      E.literal m (B.base+i.val)=m (B.base+i.val) := by
    rcases apart with left|right
    · exact E.literal_before m ((Nat.add_lt_add_left (i.isLt.trans_le rows) _).trans_le left)
    · exact E.literal_after m (right.trans (Nat.le_add_right ..))
  exact ⟨immutable,bank _ fit.hostRows.1 fit.depthAway,bank _ fit.hostRows.2 fit.gainAway,
    fun z after=>E.literal_after m ((Nat.le_add_right E.staticEnd E.dataGap).trans after)⟩

end
end Hierarchy.DescentPackedWalsh.EstimatorArena

end OAI
