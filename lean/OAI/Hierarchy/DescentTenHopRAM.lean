import OAI.Hierarchy.DescentFixedRowProgram
import OAI.Hierarchy.DescentTenHopFields
import OAI.Hierarchy.DescentTenHopRoster
import OAI.Hierarchy.DescentRosterExpressionPrice

namespace OAI
/-! # Publishing the actual dense ten-hop receiver table from the old adjacency bank -/
namespace Hierarchy.DescentTenHopRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open DescentHaloWalkRAM DescentSortedRoster DescentTenHopRoster
open scoped Classical Fin.CommRing
noncomputable section

def paths (D : ℕ) := (D+1)^10
theorem paths_pos (D : ℕ) : 0<paths D := pow_pos (Nat.succ_pos _) _

def operand (bank : Bank) (H D v : ℕ) (p : Fin (paths D)) : Expr :=
  walkExpr bank H D (List.ofFn (finFunctionFinEquiv.symm p : Fin 10→Fin (D+1))) (.lit v)

def cell (bank : Bank) (H D a : ℕ) :=
  pick (operand bank H D (a/paths D)) (.lit (a%paths D)) H (List.finRange (paths D))

def native (bank : Bank) (H D w out : ℕ) :=
  DescentFixedRowProgram.program w out (cell bank H D) (H*paths D)

def ticks (bank : Bank) (H D : ℕ) := DescentFixedRowProgram.clock (cell bank H D) (H*paths D)
def finish {w : ℕ} (bank : Bank) (H D out : ℕ) (m : Memory w) :=
  DescentFixedRowProgram.image out (cell bank H D) m (H*paths D)

theorem cell_fits {w out : ℕ} (bank : Bank) (H D a : ℕ) (low : bank.Fits w out) :
    (cell bank H D a).Fits w out :=
  pick_lit_fits (operand bank H D (a/paths D))
    (fun p=>walk_fits low (List.ofFn (finFunctionFinEquiv.symm p : Fin 10→Fin (D+1)))
      (.lit (a/paths D)) trivial) _ _

theorem run {w : ℕ} (bank : Bank) (H D out : ℕ) (m : Memory w) (low : bank.Fits w out)
    (space : out+H*paths D<2^w) : (native bank H D w out).Exec m (finish bank H D out m) (ticks bank H D) :=
  DescentFixedRowProgram.run _ _ _ _ (fun a _=>cell_fits bank H D a low) space

theorem cheap (bank : Bank) (H D w out : ℕ) : CheapCode (native bank H D w out) :=
  DescentFixedRowProgram.cheap _ _ _ _

theorem frame {w : ℕ} (bank : Bank) (H D out : ℕ) (m : Memory w) (a : ℕ)
    (away : a<out ∨ out+H*paths D≤a) : finish bank H D out m a=m a :=
  DescentFixedRowProgram.frame _ _ _ _ _ away

theorem read {H D w : ℕ} (bank : Bank) (out : ℕ) (near : Fin H→Fin D→Option (Fin H))
    (m : Memory w) (low : bank.Fits w out) (capacity : H*D≤bank.size)
    (hostFits : H<2^w) (pathsFit : paths D<2^w)
    (data : ∀v j,m (bank.base+v.val*D+j.val)=(number (near v j):Word w))
    (v : Fin H) (i : Fin (paths D)) :
    finish bank H D out m (out+(v.val*paths D+i.val))=(number (oldWithin near v i):Word w) := by
  have p : v.val*paths D+i.val<H*paths D := (Nat.add_lt_add_left i.isLt _).trans_le
    (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ v.isLt)
  have row : (v.val*paths D+i.val)/paths D=v.val := by
    rw [Nat.mul_comm v.val (paths D),Nat.mul_add_div (paths_pos D),Nat.div_eq_of_lt i.isLt,Nat.add_zero]
  have slot : (v.val*paths D+i.val)%paths D=i.val := by rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt i.isLt]
  apply (DescentFixedRowProgram.read _ _ _ _ p (cell_fits bank H D _ low)).trans
  unfold cell
  rw [row,slot]
  exact pick_read (endpoints near) m 0 _ v hostFits pathsFit
    (fun q=> walk_read bank near m capacity low.2.1 hostFits data _ 0 (.lit v.val) (some v) rfl)
    (.lit i.val) i (Fin.val_cast_of_lt (i.isLt.trans pathsFit))

theorem cell_work (bank : Bank) (H D a : ℕ) :
    (cell bank H D a).work ≤ 2240*((D+12)^10)^4 := by
  let X:=(D+12)^10
  have xp : 1≤X := Nat.one_le_pow _ _ (by omega)
  have many : paths D≤X := Nat.pow_le_pow_left (by omega : D+1≤D+12) 10
  have bound (p : Fin (paths D)) : (operand bank H D (a/paths D) p).work≤13*X := by
    apply (Nat.le_add_right _ 12).trans
    simpa [operand,Expr.work,X] using walk_work bank H D
      (List.ofFn (finFunctionFinEquiv.symm p : Fin 10→Fin (D+1))) (.lit (a/paths D))
  apply (pick_lit_work _ (13*X) bound _ _).trans
  calc
    _ ≤ 20*(14*X)*(2*X)^3 := Nat.mul_le_mul (Nat.mul_le_mul_left _ (by omega))
      (Nat.pow_le_pow_left (by omega) 3)
    _ = _ := by dsimp only [X]; ring

/-- This includes the names of all compiled instructions, including all literal path choices.
The output is host-major, with the old host count as the hole sentinel. -/
theorem price (bank : Bank) (H D w out : ℕ) :
    ticks bank H D+DescentStaticWordColumn.names (native bank H D w out) ≤
      15000*(H+1)*(D+12)^50 := by
  let X:=(D+12)^10
  have xp : 1≤X := Nat.one_le_pow _ _ (by omega)
  have m₄ : 1≤X^4 := Nat.one_le_pow _ _ xp
  have m₅ : 1≤X^5 := Nat.one_le_pow _ _ xp
  have p : paths D≤X := Nat.pow_le_pow_left (by omega : D+1≤D+12) 10
  apply (DescentFixedRowProgram.bill w out (H*paths D) (cell bank H D) (2240*X^4)
    (fun j _=>cell_work bank H D j)).trans
  calc
    _ ≤ 19*X^5+(H*X)*(13500*X^4) :=
      Nat.add_le_add (by omega) (Nat.mul_le_mul (Nat.mul_le_mul_left H p) (by omega))
    _ ≤ 15000*(H+1)*X^5 := by ring_nf;omega
    _ = _ := by dsimp only [X];rw [←pow_mul]

end
end Hierarchy.DescentTenHopRAM

end OAI
