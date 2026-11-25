import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMGeneratedWriteCheap
import OAI.Hierarchy.ProtocolRAMRowText

namespace OAI
/-! # Converting exposed source tags into the inverse permutation consumed by the CT -/
namespace Hierarchy.ProtocolRAM.TagInverse
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open ThreeFlat.RAM PhysicalProcedure
open ProbeStage.Native
open scoped Fin.CommRing

def source (h : ℕ) : Expr := .lookup ⟨0,h⟩ .row

/-- The two scratch columns freeze every target and source ordinal before the scatter
overwrites the original tags. The final scan restores both columns to their incoming zeros. -/
def program (W h S : ℕ) : Procedure W :=
  (ProtocolRAMGeneratedWrite.program W S (S+2^h) (2^h) (source h) .row).seq
    (scan W S (2*(2^h)) (.lit 0))

def ticks (h : ℕ) := ProtocolRAMGeneratedWrite.work (2^h) (source h) .row+(4+6*(2*2^h))

theorem time (h : ℕ) : ticks h=15+48*2^h := by
  simp only [ticks,ProtocolRAMGeneratedWrite.work,source,Expr.work]
  omega

theorem cost (W h S : ℕ) : text (program W h S)=93 := by
  rw [program,text_seq,ProtocolRAMGeneratedWrite.program,text_seq,text_seq,Calendar.text_scan,
    Calendar.text_scan,Calendar.text_scan]
  rfl

theorem cheap (W h S : ℕ) : CheapCode (program W h S) := by
  let stores := ProtocolRAMGeneratedWrite.program W S (S+2^h) (2^h) (source h) .row
  let clearRows := scan W S (2*(2^h)) (.lit 0)
  have storesCheap : CheapCode stores := by
    intro P R K pc reg pub exit i
    exact ProtocolRAMRankCheap.generated W S (S+2^h) (2^h) (source h) .row pc reg pub exit i
  have clearCheap : CheapCode clearRows := by
    intro P R K pc reg pub exit i
    exact scan_cheap W S (2*(2^h)) (.lit 0) pc reg pub exit i
  intro P R K pc reg pub exit i
  exact cheap_seq (A:=stores) (B:=clearRows) (@storesCheap) (@clearCheap) pc reg pub exit i

/-- The incoming raw table agrees with the external tags; the required body state
carries p⁻¹ at precisely those addresses and is unchanged everywhere else. -/
theorem run {W : ℕ} (h S : ℕ) (p : Equiv.Perm (Fin (2^h))) (raw target : ℕ→Word W)
    (low : 2^h≤S) (room : S+2*(2^h)<2^W)
    (input : ∀i:Fin (2^h),raw i.val=((p i).val:Word W))
    (inverse : ∀i:Fin (2^h),target i.val=((p.symm i).val:Word W))
    (outside : ∀a,2^h≤a→ raw a=target a) :
    (program W h S).Exec (initialMemory S raw) (initialMemory S target) (ticks h) := by
  let n:=2^h
  let m:=initialMemory S raw
  let addr:=fun i : Fin n=>(p i).val
  let val:=fun i : Fin n=>(i.val:Word W)
  let mid:=ProtocolRAMGeneratedWrite.image S (S+n) (source h) .row addr val m
  have width : n<2^W:=by omega
  have data (i : Fin n) : (source h).eval m (i.val:Word W)=(addr i:Word W):=by
    have small:=i.isLt.trans width
    change m (0+(i.val:Word W).val%n)=_
    rw [Fin.val_cast_of_lt small,Nat.mod_eq_of_lt i.isLt,Nat.zero_add]
    simpa only [m,initialMemory,ite_eq_left (i.isLt.trans_le low),addr] using input i
  have scatter : (ProtocolRAMGeneratedWrite.program W S (S+n) n (source h) .row).Exec m mid
      (ProtocolRAMGeneratedWrite.work n (source h) .row) :=
    ProtocolRAMGeneratedWrite.run S (S+n) (source h) .row addr val m
      ⟨⟨Nat.two_pow_pos _,width,by simpa only [Bank.size,Nat.zero_add] using low⟩,trivial⟩ trivial
      le_rfl (by omega) data (fun _=>rfl) (fun i=>(p i).isLt.trans width)
      (fun i j=>by have := (p j).isLt;dsimp [addr];omega)
      (fun i j=>by have := (p j).isLt;dsimp [addr];omega)
  let out:=ProtocolRAM.image S (2*n) (.lit 0) mid
  have cleared : (scan W S (2*n) (.lit 0)).Exec mid out (4+6*(2*n)):=by
    intro P R K M pc reg pub exit installed publicData config mem enter starts
    simpa only [Expr.work,show 2*1+4=6 by decide,Nat.mul_comm (2*n) 6] using
      (scan_exec S (2*n) (.lit 0) mid trivial room M pc reg pub exit installed publicData
        config mem enter starts)
  have done : out=initialMemory S target:=by
    funext a
    by_cases used : a<n
    · let j : Fin n:=⟨a,used⟩
      let i:=p.symm j
      have atJ : addr i=a:=congrArg Fin.val (p.apply_symm_apply j)
      have unique : Function.Injective addr:=fun _ _ eq=>p.injective (Fin.ext eq)
      let staged:=ProtocolRAM.image (S+n) n .row (ProtocolRAM.image S n (source h) m)
      have read:=ProtocolRAMIndexedWrite.read_unique addr val staged unique n le_rfl i i.isLt
      have got : mid a=val i:=by simpa only [mid,ProtocolRAMGeneratedWrite.image,atJ] using read
      rw [show out a=mid a from ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl (used.trans_le low)),got]
      simpa only [initialMemory,ite_eq_left (used.trans_le low)] using (inverse j).symm
    · have free : n≤a:=Nat.le_of_not_lt used
      by_cases tmp : S≤a ∧ a<S+2*n
      · let i : Fin (2*n):=⟨a-S,by omega⟩
        have pos : S+i.val=a:=Nat.add_sub_of_le tmp.1
        have clean:=ProtocolRAMGeneratedWrite.read_image S (2*n) (.lit 0) mid i
        simpa only [out,initialMemory,ite_eq_right (not_lt.mpr tmp.1),pos,Expr.eval,Nat.cast_zero] using clean
      · have away : a<S ∨ S+2*n≤a:=by omega
        have eq:=ProtocolRAMGeneratedWrite.frame S (S+n) (source h) .row addr val m a
          (fun i eq=>by have := (p i).isLt;dsimp [addr] at eq;omega) (by omega) (by omega)
        have same : mid a=m a:=eq
        rw [show out a=mid a from ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ away,same]
        simp only [m,initialMemory,outside a free]
  rw [← done]
  intro P R K M pc reg pub exit installed publicData config mem enter starts
  exact (Procedure.Exec.then scatter cleared) M pc reg pub exit installed publicData config mem
    enter starts

end Hierarchy.ProtocolRAM.TagInverse

end OAI
