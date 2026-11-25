import OAI.Hierarchy.DescentPreviousOperandLayout
import OAI.Hierarchy.DescentDatedOperandRun
import OAI.Hierarchy.DescentOperandVectorArena

namespace OAI
/-! # The succeeding ordinary lookup reads the same printed block/page as its predecessor -/
namespace Hierarchy.DescentDatedPriorOperand
open DescentSIMDLookup DescentOperandStateBanks DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section

def fromVector (l : Layout) (base : ℕ) (side : Fin l.jobs→Fin 6→Bank) (route : Fin l.jobs→Fin 3→Bank) : Banks l:=
  ⟨previousBank l base,side,route⟩

theorem from_previous (oldH lows groups radix lanes size nodes slots base : ℕ) (block : Fin radix) (p : Pages slots) :
    previousBank ⟨radix,nodes,slots,oldH*lows,groups,lanes,size⟩ base block p=
      DescentVectorBookReshape.blockBank base oldH lows groups radix lanes p block :=rfl

theorem from_previous_placed (l : Layout) (A : DescentOperandVectorArena.Layout) (start : ℕ) {w : ℕ}
    (slots : l.operands=A.operands) (blocks : l.blocks=A.radix) (hs : l.hosts=A.hosts*A.lows)
    (groups : l.groups=A.groups) (lanes : l.lanes=A.lanes) (room : A.endAddress start<2^w)
    (block : Fin l.blocks) (p : Pages l.operands) :
    (previousBank l (A.out start) block p).Fits w (A.endAddress start) ∧ l.rows≤(previousBank l (A.out start) block p).size := by
  cases l;cases A;dsimp only at *;subst_vars
  exact ⟨DescentOperandVectorArena.block_room _ start room p block,
    DescentVectorBookReshape.blockBank_capacity _ _ _ _ _ _ p block⟩

/-- A newly reached array contributes its true all-block `.Reads` directly.
Every job references the printed page determined by its public block ordinal. -/
theorem registered_previous {l : Layout} {w : ℕ} (base : ℕ) (side : Fin l.jobs→Fin 6→Bank) (route : Fin l.jobs→Fin 3→Bank)
    (v : Fin l.jobs→Source l) (m : Memory w)
    (printed : ∀(b : Fin l.blocks) (n : Fin l.nodes) (a : Fin l.operands) (p : Pages l.operands),
      Reads (previousBank l base b p) ((v (l.index (b,n,a))).books p) l.lanes m) :
    ∀j p,Reads ((fromVector l base side route).book j p) ((v j).books p) l.lanes m :=by
  intro j p
  let z:=l.index.symm j
  simpa only [Banks.book,fromVector,z,Prod.eta,Equiv.apply_symm_apply] using printed z.1 z.2.1 z.2.2 p

end
end Hierarchy.DescentDatedPriorOperand

end OAI
