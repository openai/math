import OAI.Hierarchy.DescentRegisteredAcquiredReferences
import OAI.Hierarchy.DescentRegisteredPriorRoleToken

namespace OAI
/-! Readback of the original W number, through its actual low-host and group transposition. -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentSixParty.Chronology DescentDatedPriorOperand DescentOperandStateBanks
open DescentOrdinaryAtomFieldRAM.ScalarOperand DescentSIMDLookup DescentHaloWalkRAM DescentOperandVectorArena
open PhysicalOrdinary.ArgumentEntry
noncomputable section

theorem onSourceAxes_book {D k K c c' H G G' a n n' b:ℕ} (cap:c=c') (width:n=n')
    (group:Fin G'→Fin G) (x:Values D k K c H G a n b) (N:ℕ) (h:Fin H) (g:Fin G'):
    ((onSourceAxes cap width group x).book N h g).val=(x.book N h (group g)).val:=by
  cases cap;cases width
  rfl

theorem groupValues_book {D k K c H G G' a n b:ℕ} (groups:G=G')
    (v:Values D k K c H G a n b) (N:ℕ) (h:Fin H) (g:Fin G'):
    ((groupValues groups v).book N h g).val=(v.book N h (g.cast groups.symm)).val:=by
  cases groups
  rfl

theorem split_source {S : AtomSchedule} {i k:ℕ} (age:i<S.length) (radix:S.radix=2^k)
    (groups:S.groupCount i=S.groupCount (i+1)*2^k) (y:Fin (S.groupCount (i+1)*2^k)):
    y.cast groups.symm=(S.groupDigits age radix).symm (finProdFinEquiv.symm y):=by
  apply Fin.ext
  have held:=DatePorts.ordinary_source_number age radix ((S.groupDigits age radix).symm (finProdFinEquiv.symm y))
  simpa only [Equiv.apply_symm_apply,Fin.val_cast] using held

/-- The actual registered full scalar word at each W output equals the chosen acquired source
word, after both physical group/block and dense host/low reshapes. -/
theorem acquired_previous_value {D k K c c' G a n n' b:ℕ} (l:DescentDatedPriorOperand.Layout)
    (A:DescentOperandVectorArena.Layout) (ops:l.operands=A.operands) (blocks:l.blocks=A.radix)
    (hosts:l.hosts=A.hosts*A.lows) (groups:l.groups=A.groups) (cap:c=c') (width:n=n')
    (before:G=A.groups*A.radix) (pull:Fin (A.groups*A.radix)→Fin G)
    (order:∀y,y.cast before.symm=pull y)
    (raw:Fin A.pageCount→Fin A.lows→Values D k K c A.hosts G a n b)
    (registered:References.Rows A D k K c a n b) (acquired:References.Rows A D k K c' a n' b)
    (original:∀p low,registered p low=groupValues before (raw p low))
    (actual:(fun p low=>onSourceAxes cap width pull (raw p low))=acquired)
    (p:Pages l.operands) (x:Fin l.blocks) (h:Fin l.hosts) (g:Fin l.groups):
    (previousValues l A ops blocks hosts groups (References.returnedValue A registered l.nodes) p x h g).val=
    (previousValues l A ops blocks hosts groups (References.returnedValue A acquired l.nodes) p x h g).val:=by
  dsimp only [previousValues, References.returnedValue, DescentScalarBookReshape.book]
  rw [original,←actual,groupValues_book,onSourceAxes_book,order]

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
