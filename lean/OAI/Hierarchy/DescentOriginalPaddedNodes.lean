import OAI.Hierarchy.DescentOriginalNodeCoordinates

namespace OAI
/-! # Original node coordinates on a padded host rectangle -/
namespace Hierarchy.DescentSixParty.Reached.NodeCells
open DescentKernelHistory DescentLocalArchiveOrder DescentColonies DescentCompiler
open scoped Classical
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k age grain degree wire hist : ℕ}
  (cap : Reached W G q ε S k age grain degree wire hist) (B : BitDescription W) (ord : Local B)
  {H N : ℕ} (x : Block k) (j : Fin N) (h : Fin H) (g : Fin (S.groupCount age))

def atPhysical : Option (NodeOrder.All B) :=
  if legal:h.val<S.hostSize age then whereAt cap B ord x j ⟨h.val,legal⟩ g else none

theorem atPhysical_some (v : W.graph.Site) (s : (B.recipe v).Node) :
    atPhysical cap B ord x j h g=some ⟨v,s⟩ ↔
      (cap.vertex (cap.placement.pos v).2).val=h.val ∧ (cap.placement.pos v).1=g ∧
        cap.placement.block v=x ∧ j.val=(ord v s).val:=by
  classical
  by_cases legal:h.val<S.hostSize age
  · rw [atPhysical,dite_eq_left legal,whereAt_some]
    constructor
    · rintro ⟨eqn,size⟩
      exact ⟨congrArg (fun p=>p.1.val) eqn,congrArg (fun p=>p.2.1) eqn,congrArg (fun p=>p.2.2) eqn,size⟩
    · rintro ⟨same,group,block,size⟩
      exact ⟨Prod.ext (Fin.ext same) (Prod.ext group block),size⟩
  · rw [atPhysical,dite_eq_right legal]
    constructor
    · intro no;cases no
    · rintro ⟨rank,rest⟩
      have stored := ((cap.vertex (cap.placement.pos v).2).castLE cap.valid.host).isLt
      exact False.elim (legal (show h.val<S.hostSize age by rw [←rank];exact stored))



end
end Hierarchy.DescentSixParty.Reached.NodeCells

end OAI
