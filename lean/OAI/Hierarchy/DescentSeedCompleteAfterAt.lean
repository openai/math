import OAI.Hierarchy.DescentSeedNativeCompleteCode
import OAI.Hierarchy.DescentSeedChosenLayoutCore
import OAI.Hierarchy.DescentNativeSocketScale

namespace OAI
/-! # The actual startup programs and their cost at a fixed dyadic height -/
namespace Hierarchy.DescentDatedSeedStartup
open DescentCompiler DescentCompiler.TerminalScale DescentSixParty DescentInitialHost DescentSeedInitialTable
open DescentPackedSeed DescentDyadicSpan DescentColonies Catalyst Filter
open scoped BigOperators
noncomputable section
variable {F : Type} [Field F] (D : PoweredGadget F) (op : RotorSpec)

/-- Only the size of the reset gate dictionary enters the literal initial
palette loader. Later dates may choose other rotor fields. -/
theorem Input.boot_dimension {S : AtomSchedule} {k cp pins H : ℕ}
    (X : Approximation F cp pins) (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k)
    (wide : Fintype.card (DescentSeedRoot.Vertex X)≤H) (l : Layout) (header h Z w : ℕ)
    (next : RotorSpec) (same : next.n=op.n) :
    Input.completeAfter D next X digits wide l header h Z w=Input.completeAfter D op X digits wide l header h Z w ∧
    Input.completeTicks D next X wide l h Z w (k:=k) (S:=S)=
      Input.completeTicks D op X wide l h Z w (k:=k) (S:=S) :=by
  rcases op with ⟨n,a,c,wd,d,r,e,z⟩
  rcases next with ⟨n',a',c',wd',d',r',e',z'⟩
  change n'=n at same
  subst n'
  exact ⟨rfl,rfl⟩

/-- The numerical receipt at one actual dyadic height, with the original
flags, loader, date-zero geometry, and closed source width. -/
def CompleteAfterAt (t f g reset drift degreeMax quota τ B factor h : ℕ) : Prop :=
  let J:=Nat.log 2 h/(2*B)
  ∀M degree w base field wire hist header,let S:=stageNumbers D t J f g reset M (tail τ J)
  let k:=groupBits t J S.hostGain S.capGain (cutRate t f g)
  let q₀:=2^Nat.clog 2 (NativeBranch.localLimit D S)
  let split:=NativeBranch.binLimit (k:=k) S
  let q:=q₀*(D.b^(t*J)*D.b)
  let p:=split*(h/(16*(q*split)))
  let l:=selectedLayout D S h k (tail τ J) g p drift degree f quota base field wire hist
  2^h ≤ M → degree ≤ degreeMax → w+1 ≤ factor*h →
  ∀{cp pin : ℕ} (X : Approximation F cp pin) (wide : Fintype.card (DescentSeedRoot.Vertex X) ≤ span M)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×Block k),
    let n:=rows X S.copies l.seedWidth h
    let Z:=S.grainAt D.b p 0
    let flags:=DescentWideSeedFlags.check X S.copies l.seedWidth h w
    let boot:=Input.completeAfter D op X digits wide l header h Z w
    let amount:=(4+(n+1)*66+7*DescentStaticWordColumn.names flags)+
      (Input.completeTicks D op X wide l h Z w (k:=k) (S:=S)+7*DescentStaticWordColumn.names boot)
    ∀budget E, budget≤w → amount*(budget+1)*2^J≤4*(S.copies*l.seedWidth)*(M+2^J*E)

end
end Hierarchy.DescentDatedSeedStartup

end OAI
