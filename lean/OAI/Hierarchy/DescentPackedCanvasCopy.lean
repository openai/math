import OAI.Hierarchy.DescentPackedRegroup
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMCheapCode

namespace OAI
/-! # Copy one old census slab to the fixed pre-estimator site window -/
namespace Hierarchy.DescentSixParty.PackedFlow.Canvas
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w H r M a : ℕ}

def copy (w base number : ℕ) (src : Bank) := scan w base number (.lookup src .row)

theorem copy_original (src : Bank) (base : ℕ) (X : Fin H→Fin r→Cell a) (mem : Memory w)
    (safe : src.Fits w base) (count : H*chunks r M≤ src.size)
    (room : base+H*chunks r M<2^w)
    (source : ∀p:Row H r M,mem (src.base+(row H r M p).val)=((data X p).val:Word w)) :
    let n:=H*chunks r M
    let emit:=copy w base n src
    ∃out : Memory w,emit.Exec mem out (4+18*n) ∧ CheapCode emit ∧
      (∀p:Row H r M,out (base+(row H r M p).val)=((data X p).val:Word w)) ∧
      ∀z,(z<base ∨ base+n≤z)→ out z=mem z := by
  intro n emit
  let e : Expr:=.lookup src .row
  let out:=image base n e mem
  have fit:e.Fits w base:=⟨safe,trivial⟩
  refine ⟨out,?_,@scan_cheap _ _ _ _,?_,fun z h=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ h⟩
  · have cost : 4+n*(2*e.work+4) = 4+18*n := by
      change 4+n*18=4+18*n
      rw [Nat.mul_comm n 18]
    rw [←cost]
    exact @scan_exec w base n e mem fit room
  · intro p
    rw [show out=image base n e mem from rfl,ProtocolRAMGeneratedWrite.read_image]
    exact (DescentPackedZip.bank_read src mem ((row H r M p).isLt.trans_le count) safe).trans (source p)

theorem original_chunks {u l k R : ℕ} (size : 2^(u+l)=R*2^k) (lanes : 2^l=M*2^k) (hm : 0<M) :
    chunks R M=2^u := by
  have group:=chunks_group R M (2^k) hm (Nat.two_pow_pos _)
  have plain:=chunks_group (2^u) 1 (2^l) (by decide) (Nat.two_pow_pos _)
  rw [←size,←lanes] at group
  simpa [pow_add,chunks,ThreeFlat.Routing.poolBatchCount] using group.symm.trans
    (by simpa [pow_add,chunks,ThreeFlat.Routing.poolBatchCount] using plain :
      chunks (2^(u+l)) (2^l)=2^u)

end
end Hierarchy.DescentSixParty.PackedFlow.Canvas

end OAI
