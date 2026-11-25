import OAI.Hierarchy.DescentTerminalRouteDimensions
import OAI.Hierarchy.DescentTerminalRouteWords

namespace OAI
/-! # The fixed short lookup that accumulates every row of a bin -/
namespace Hierarchy.DescentTerminalRouteLedger
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMSerialization DescentTerminalRouteRows
open scoped Classical
noncomputable section
variable {K W c : ℕ}
local notation "B" => W*c
local notation "n" => K*W

def put (slot : Fin W) (old : Word B) (row : Word c) : Word B :=
  packBin (Function.update (unpackBin old) slot row)
theorem at_put (slot target : Fin W) (old : Word B) (row : Word c) :
    unpackBin (put slot old row) target=if target=slot then row else unpackBin old target := by
  simp only [put,bin_back,Function.update_apply]

def key (slot : Fin W) (old : Word B) (row : Word c) :=
  finProdFinEquiv (slot,finProdFinEquiv (row,old))
def stepROM (i : Fin (radix W c)) : Word B :=
  let a : Fin W × Fin (2^c*2^B):=finProdFinEquiv.symm i
  let k : Word c × Word B:=finProdFinEquiv.symm a.2
  put a.1 k.2 k.1
theorem key_val (slot : Fin W) (old : Word B) (row : Word c) :
    (key slot old row).val=old.val+2^B*(row.val+2^c*slot.val) := by
  change old.val+2^B*row.val+(2^c*2^B)*slot.val=_
  ring
theorem step_at (i : Fin W) (old : Word B) (row : Word c) : stepROM (key i old row)=put i old row := by
  simp only [stepROM,key,Equiv.symm_apply_apply]

def history (rows : Fin n→Word c) : ℕ→Word B
  | 0=>0
  | t+1=>if ok : t<n then put (finProdFinEquiv.symm (⟨t,ok⟩:Fin n)).2 (history rows t) (rows ⟨t,ok⟩) else 0

theorem step (rows : Fin n→Word c) (b : Fin K) (v : Fin W) :
    history rows (b.val*W+v.val+1)=put v (history rows (b.val*W+v.val)) (rows (finProdFinEquiv (b,v))) := by
  have val : (finProdFinEquiv (b,v)).val=b.val*W+v.val := by change v.val+W*b.val=_;ring
  have z: b.val*W+v.val<n := val ▸ (finProdFinEquiv (b,v)).isLt
  have pos : (⟨b.val*W+v.val,z⟩:Fin n)=finProdFinEquiv (b,v):=Fin.ext val.symm
  rw [history,dite_eq_left z,pos,Equiv.symm_apply_apply]

theorem at_end (rows : Fin n→Word c) (b : Fin K) :
    history rows (b.val*W+W)=packBin (fun i=>rows (finProdFinEquiv (b,i))) := by
  apply bin_inj;intro target
  rw [bin_back]
  have earlier : ∀j≤W,target.val<j→
      unpackBin (history rows (b.val*W+j)) target=rows (finProdFinEquiv (b,target)) := by
    intro j;induction j with
    | zero=>omega
    | succ j ih=>
      intro hi loc
      let i:Fin W:=⟨j,by omega⟩
      rw [show b.val*W+(j+1)=b.val*W+i.val+1 by rfl,step,at_put]
      by_cases eqn : target=i
      · simp [eqn]
      · have ne : target.val≠j:=fun h=>eqn (Fin.ext h)
        simpa only [ite_eq_right eqn] using ih (by omega) (by omega)
  exact earlier W le_rfl target.isLt

theorem small {bits z : ℕ} (logW : W≤2^z) (space : z+c+W*c≤bits/2) : radix W c≤2^(bits/2) := by
  calc
    _ ≤ 2^z*(2^c*2^(W*c)):=Nat.mul_le_mul_right _ logW
    _ = 2^(z+c+W*c):=by simp [pow_add,mul_assoc]
    _ ≤ _:=Nat.pow_le_pow_right (by decide) space

end
end Hierarchy.DescentTerminalRouteLedger

end OAI
