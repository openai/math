import OAI.Hierarchy.DescentPrimitiveBirthProgram
import OAI.Hierarchy.DescentResetRetainedPlacementTariff

namespace OAI
/-! # Instructions and named hardware for the two primitive-origin tables and their physical lift -/
namespace Hierarchy.DescentPrimitiveBirth.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentColonies.SplitRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentStaticWordColumn (names names_seq names_mount)
open scoped Classical Fin.CommRing
noncomputable section
variable (z : DescentPrimitiveBirth.Layout)

private theorem totalWork {ι : Type} (f : ι→Expr) (xs : List ι) (T : ℕ) (h : ∀i,(f i).work≤T) :
    (total f xs).work≤1+xs.length*(T+1):=by
  induction xs with
  | nil=>simp [total,Expr.work]
  | cons a rest ih=>
    simp only [total,Expr.work,List.length_cons,Nat.succ_mul]
    have:=h a
    omega

def rootBudget:=1+(z.residual+1)*20
theorem root_work (base : ℕ) (g : z.Guards) (k : Fin (z.roots*z.nodes)) :
    (z.rootWord base g k).work≤z.rootBudget:=by
  let p : Fin z.roots×Fin z.nodes:=finProdFinEquiv.symm k
  have term (l : Fin (z.residual+1)) : (z.field base p.2 (g p.1 l)).work≤19:=by
    cases g p.1 l <;>simp [field,Tables.read,Expr.work]
  simpa [rootWord,p,rootBudget] using totalWork _ (List.finRange (z.residual+1)) 19 term

def mountBill (cells : ℕ) :=4+10*cells+7*(15*(cells+1))
def invoice:=
  mountBill (z.nodes*(2*2^((z.rootBits*z.stop)*z.sourceLanes)))+
  z.placement.invoice z.batch z.rootBudget+
  mountBill (z.gates*(2*2^(z.aperture*z.placement.lanes)))

theorem price (base w : ℕ) (guard : z.Guards) (cnt inv : Bank)
    (pos : 0<z.sourceLanes) (blocks : 0<z.placement.blocks) (lanes : 0<z.placement.lanes) :
    z.clock base guard cnt inv+7*names (z.program base guard cnt inv w)≤z.invoice:=by
  have p:=z.placement.tariff z.batch (z.liftBase base) w (fun _=>true) (z.rootWord base guard)
    cnt inv z.rootBudget (z.root_work base guard) pos blocks lanes
  simp only [program,rootCode,names_seq,mounts,mountOrigin,Book.install,names_mount,clock,rootTime,invoice,mountBill]
  omega

def argumentBudget (W : ℕ) :=
  let admitted:=2*W+11
  let span:=1+z.arguments*(2*W+12)
  1+(1+z.roots*(admitted+19))+(admitted+span+11)

theorem operand_work (base : ℕ) (n : Fin z.nodes) (x : Fin z.placement.blocks) (cls paid : Expr)
    (spans : Fin z.arguments→Expr) (W : ℕ) (one : 0<W) (hc : cls.work≤W) (hp : paid.work≤W) (hs : ∀j,(spans j).work≤W) :
    (z.bornAt base n x cls paid spans).work≤z.argumentBudget W ∧ (z.relay base n cls paid).work≤z.argumentBudget W:=by
  have cost (i : z.Role) (a b : Expr) : (z.gate base i a b).work=a.work+b.work+11:=by
    simp [gate,Tables.read,Expr.work]; omega
  have ac : (z.active base n cls paid).work≤2*W+11:=by rw [active,cost];omega
  have head : (z.first spans).work≤W:=by unfold first; split <;> simp_all [Expr.work]; omega
  have ss : (z.more base spans).work≤1+z.arguments*(2*W+12):=by
    apply (totalWork _ _ (2*W+11) (fun j=>by rw [cost];have:=hs j;omega)).trans
    simp
  let roots : Fin z.roots→Expr:=fun q=>.lookup (z.rootBank base n x q) .row
  have rs : (z.rotations base (z.active base n cls paid) roots).work≤1+z.roots*((2*W+11)+19):=by
    apply (totalWork _ _ ((2*W+11)+18) (fun j=>by rw [cost]; simp only [roots,Expr.work];omega)).trans
    simp
  constructor
  · change (z.rotations base (z.active base n cls paid) roots).work+
      (z.gate base (.inr 0) (z.active base n cls paid) (z.more base spans)).work+1≤_
    rw [cost]; dsimp only [argumentBudget];omega
  · rw [relay,cost];change _+1+11≤_;dsimp only [argumentBudget];omega

end
end Hierarchy.DescentPrimitiveBirth.Layout

end OAI
