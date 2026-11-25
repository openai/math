import OAI.Hierarchy.DescentOrdinaryFinal
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentDateBillVolume

namespace OAI
/-! # Clock, controller and group-volume bounds for the final ordinary argument publication -/
namespace Hierarchy.DescentOrdinaryFinal.Chart
open DescentPacking.PackedMatch.Local
open DescentSIMDLookup DescentPackedZip DescentStaticWordColumn DescentPackedFlowBatch ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable (B : DescentOrdinaryFinal.Chart)

def work :=14+B.inputs*30

theorem cast_work (s : B.Sources) (floor : ℕ) (p x i) : (B.castArg s floor p x i).work=19:=rfl

theorem read_work (s : B.Sources) (floor : ℕ) (z : ℕ) (hit : z<B.passes) : (B.expr s floor z).work≤B.work :=by
  unfold expr;rw [dite_eq_left hit]
  exact DescentOperandFamilyBook.expr_work B.law B.layout.lanes (B.castEnd floor) _ _ 19 (fun i=>(B.cast_work s floor _ _ i).le)

def cpu :=(4+10*B.castWords)+(4+10*B.tableWords)+(4+B.passes*(4+B.rows*(2*B.work+4)))
def textCost :=15*(B.castWords+1)+15*(B.tableWords+1)+(15+B.passes*(11+4*B.work))

theorem tariff (s : B.Sources) (floor w : ℕ) :
    B.ticks s floor≤B.cpu ∧ names (B.program s floor w)≤B.textCost :=by
  have real (i : ℕ) (hit : i<B.passes):=(B.read_work s floor i hit)
  constructor
  · exact Nat.add_le_add le_rfl (DescentPackedFlowBatch.tariff (B.out floor) B.rows B.rows B.passes (B.expr s floor) B.work real)
  · have install : names (B.castCode floor w)=15*(B.castWords+1):=by
      unfold castCode DescentOperandInputCast.program Book.install
      simp only [names_mount, castWords]
    have book : names (B.lawCode floor w)=15*(B.tableWords+1):=by
      unfold lawCode DescentOperandFamilyBook.program Book.install
      simp only [names_mount, tableWords, DescentOperandFamilyBook.unit]
    unfold program
    rw [names_seq,names_seq,install,book]
    exact Nat.add_le_add le_rfl (DescentOperandVectorArena.names_passes (B.out floor) B.rows B.rows w B.work
      (B.expr s floor) 0 B.passes (fun i _ h=>real i (by omega)))

/-- Both static ROMs are mounted once. Only the bounded receiver argument list enters
its local decoder. Physical rows scan all earlier host/group allocations once per returned field and block. -/
def tickUnits (R : ℕ) :=(4+10*8)+(4+10*((B.inputs+B.outputs)*2))+
  (4+B.passes*(4+R*(2*B.work+4)))
def textUnits :=15*(8+1)+15*((B.inputs+B.outputs)*2+1)+(15+B.passes*(11+4*B.work))

theorem volume (s : B.Sources) (floor w h u ratio R : ℕ) (pos : 0<u) (wide : 2*u≤h) (bus : w≤ratio*h)
    (joinRoom : (B.scalarWidth*B.inputs+B.scalarWidth)*B.layout.lanes≤h/2)
    (rows : B.rows≤R*Stage.DateBill.words B.layout.hosts B.layout.groups h u) :
    w*B.ticks s floor+7*names (B.program s floor w)≤
      (2*((ratio+7)*(B.tickUnits R+B.textUnits)))*Stage.DateBill.volumeBits B.layout.hosts B.layout.groups h u :=by
  let U:=Stage.DateBill.words B.layout.hosts B.layout.groups h u
  have dyadic : 2^(h/2)≤U:=by dsimp [U,Stage.DateBill.words];omega
  have nz : 1≤U :=(Nat.two_pow_pos _).trans_le dyadic
  have up (n : ℕ) : n≤n*U:=by simpa only [Nat.mul_one] using Nat.mul_le_mul_left n nz
  have cg : B.scalarWidth*B.layout.lanes≤h/2:=(Nat.mul_le_mul_right _ (Nat.le_add_left ..)).trans joinRoom
  have c : B.castWords≤8*U:=by
    change 4*(2*2^(B.scalarWidth*B.layout.lanes))≤8*U
    have d:=(Nat.pow_le_pow_right (by decide : 0<2) cg).trans dyadic
    omega
  have b : B.tableWords≤((B.inputs+B.outputs)*2)*U:=by
    unfold tableWords;rw [Nat.mul_assoc (B.inputs+B.outputs) 2 U]
    exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ ((Nat.pow_le_pow_right (by decide) joinRoom).trans dyadic))
  obtain ⟨clocked,printed⟩:=B.tariff s floor w
  have ct : B.cpu≤B.tickUnits R*U:=calc
    _ ≤ (4*U+10*(8*U))+(4*U+10*(((B.inputs+B.outputs)*2)*U))+
      (4*U+B.passes*(4*U+(R*U)*(2*B.work+4))) :=by
      unfold cpu;gcongr <;> first | exact up _
    _ = _:=by unfold tickUnits;ring
  have cn : B.textCost≤B.textUnits*U:=calc
    _ ≤ 15*(8*U+1*U)+15*(((B.inputs+B.outputs)*2)*U+1*U)+(15*U+B.passes*((11+4*B.work)*U)) :=by
      unfold textCost;gcongr <;> first | exact up _
    _ = _:=by unfold textUnits;ring
  have charged:=Nat.mul_le_mul bus (clocked.trans ct)
  have high : 1≤h:=by omega
  have labels : names (B.program s floor w)≤B.textUnits*U*h:=
    (printed.trans cn).trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (B.textUnits*U) high)
  calc
    _ ≤ (ratio*h)*(B.tickUnits R*U)+7*(B.textUnits*U*h):=Nat.add_le_add charged (Nat.mul_le_mul_left _ labels)
    _ = (ratio*B.tickUnits R+7*B.textUnits)*(U*h):=by ring
    _ ≤ (ratio+7)*(B.tickUnits R+B.textUnits)*(U*h):=by
      apply Nat.mul_le_mul_right;simp only [Nat.add_mul,Nat.mul_add];omega
    _ ≤ (ratio+7)*(B.tickUnits R+B.textUnits)*(2*Stage.DateBill.volumeBits B.layout.hosts B.layout.groups h u):=
      Nat.mul_le_mul_left _ (Stage.DateBill.words_bits B.layout.hosts B.layout.groups h u pos wide)
    _ = _:=by ring

end
end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
