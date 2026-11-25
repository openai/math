import OAI.Hierarchy.DescentNamedOriginalArchive
import OAI.Hierarchy.DescentBundleWorld
import OAI.Hierarchy.DescentOriginalRetainedSeed

namespace OAI
/-! # The original retained bundle at the named seed's actual sites -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentInitialHost DescentColonies DescentKernelHistory Catalyst
open DescentBundleHistory Chronology
open scoped Classical
noncomputable section
variable {F : Type} [Field F] {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ} {k s z wire : ℕ}

def transport_shape {P : Type} {d : ℕ} {bits : P→ℕ} {W W' : MarkedWorld F d P bits}
    (r : Reached W G q ε S k 0 z 3 wire s) (a : Archive W) (eqn : world r=W')
    {p R : ℕ} (shape : WorldShape p R a.bit) :
    let b : Archive W' := Eq.ndrec (motive := fun V => Archive V)
      (renamedArchive a (site r) (edge r)) eqn
    WorldShape p R b.bit := by
  cases eqn
  exact shape.renamed (site r) (edge r)

set_option maxHeartbeats 80000

private def renamedShape {P : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    (a : Archive W) (v : Equiv.Perm W.graph.Site) (e : Equiv.Perm W.graph.Edge)
    {p R : ℕ} (shape : WorldShape p R a.bit) :
    WorldShape p R (renamedArchive a v e).bit :=
  shape.renamed v e

/-- A transport map whose source and destination types can be selected independently. -/
private structure ShapeTransfer where
  source : Type
  destination : Type
  move : source → destination

private def shapeTransfer {P : Type} {d : ℕ} {bits : P → ℕ}
    {W V : MarkedWorld F d P bits} {a : Archive W} (pkg : ArchiveTransport a V)
    (p R : ℕ) : ShapeTransfer where
  source := WorldShape p R a.bit
  destination := WorldShape p R pkg.data.bit
  move := pkg.carry (fun _ b => WorldShape p R b.bit)

namespace Origin
variable {cp pins : ℕ} {X : Approximation F cp pins}
variable {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies≃Fin (S.groupCount 0)×Block k}
    (o : Origin (G:=G) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)

private def originalShape (p R : ℕ) (hp : 0<p) (stride : 1≤R) (width : p∣s) :
    WorldShape p R (Chronology.seedArchive X S.copies s c).bit :=
  (seedRetained X S.copies s hp stride width c).shape

private def physicalShape (p R : ℕ) (hp : 0<p) (stride : 1≤R) (width : p∣s) :
    WorldShape p R
      (renamedArchive (Chronology.seedArchive X S.copies s c) (site o.raw) (edge o.raw)).bit :=
  renamedShape (Chronology.seedArchive X S.copies s c) (site o.raw) (edge o.raw)
    (originalShape (X := X) (S := S) (s := s) (c := c) p R hp stride width)

include o in
private def transferFor (p R : ℕ) : ShapeTransfer := by
  -- Use the eight arguments of the actual seed package before reducing its worlds.
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let origin ← Lean.Meta.getFVarFromUserName `o
      let pkg ← Lean.instantiateMVars (← Lean.Meta.mkAppM ``Origin.archivePackage #[origin])
      let args := pkg.getAppArgs
      let decl ← Lean.getConstInfo ``Origin.archivePackage
      let mut result := decl.type
      for _ in args do
        match result.consumeMData with
        | .forallE _ _ body _ => result := body
        | _ => throwError "unexpected archivePackage telescope"
      let transport := result.consumeMData
      unless transport.isAppOf ``ArchiveTransport && transport.getAppArgs.size == 8 do
        throwError "unexpected archivePackage result type"
      let params := transport.getAppArgs.map fun e => e.instantiateRev args
      let p ← Lean.Meta.getFVarFromUserName `p
      let R ← Lean.Meta.getFVarFromUserName `R
      -- ArchiveTransport a V has its archive before the target world. shapeTransfer
      -- quantifies its target world before its source archive.
      let params := params.extract 0 6 ++ #[params[7]!, params[6]!, pkg, p, R]
      goal.assign (Lean.mkAppN (Lean.mkConst ``shapeTransfer) params)

set_option maxHeartbeats 400000 in
private def transferInput (p R : ℕ) (hp : 0<p) (stride : 1≤R) (width : p∣s) :
    (transferFor o p R).source :=
  physicalShape o p R hp stride width

/-- The complete retained shape of the named archive. The destination projection
reduces to `WorldShape p R o.archive.bit` by selecting a type from the transport. -/
def bundleShape (p R : ℕ) (hp : 0<p) (stride : 1≤R) (width : p∣s) :
    (transferFor o p R).destination :=
  (transferFor o p R).move (transferInput o p R hp stride width)

end Origin

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
