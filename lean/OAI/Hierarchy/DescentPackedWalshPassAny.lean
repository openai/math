import OAI.Hierarchy.DescentPackedWalshPasses

namespace OAI
/-! # The complete Walsh scan on arbitrary incoming rows -/

namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
noncomputable section
variable {w : ℕ}

private theorem transform_any (root first H u l b : ℕ) (m : Memory w) (z : ℕ)
    (seq : List (Fin (u+l))) (rom : root+(z+seq.length)*span H u l b≤first)
    (limit : first+(z+seq.length+1)*page H u<2^w) :
    (code w root first H u l b z seq).Exec m (after root first H u l b z seq m)
      (duration H u seq.length) := by
  induction seq generalizing z m with
  | nil =>
    have fixed : image first 0 .row m=m := by
      funext i
      exact ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (by omega)
    have run : (scan w first 0 .row).Exec m (image first 0 .row m) (4+0*(2*Expr.row.work+4)) :=
      @scan_exec w first 0 .row m trivial (by omega)
    rw [fixed] at run
    simp only [code,after,duration,List.length_nil,Nat.zero_mul,Nat.zero_add]
    intro P R K machine
    exact run machine
  | cons a seq ih =>
    have next : z+(a::seq).length=z+1+seq.length := by simp only [List.length_cons]; omega
    have view := room root first z H u l b
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (show z+1≤z+(a::seq).length by simp)) _).trans rom)
      ((Nat.add_le_add_left (Nat.mul_le_mul_right _ (show z+2≤z+(a::seq).length+1 by simp only [List.length_cons]; omega)) _).trans_lt limit)
    let B:=shelf root first z H u l b
    let dst:=outPage first H u z
    let mid:=image dst (H*2^u) B.read m
    have safe : B.read.Fits w dst :=
      ⟨view.table,⟨view.sign,trivial⟩,⟨view.old,view.hi,trivial⟩,view.shift,view.old,view.lo,trivial⟩
    have price : 2*B.read.work+4=90:=rfl
    have head : (layerProgram B dst H u w).Exec m mid (4+90*(H*2^u)) := by
      rw [show 4+90*(H*2^u)=4+(H*2^u)*(2*B.read.work+4) by rw [price,Nat.mul_comm 90]]
      exact @scan_exec w dst (H*2^u) B.read m safe view.finish
    have tail : (code w root first H u l b (z+1) seq).Exec mid (after root first H u l b (z+1) seq mid)
        (duration H u seq.length) := ih mid (z+1) (next ▸ rom) (next ▸ limit)
    have ticks : duration H u (a::seq).length=(4+90*(H*2^u))+duration H u seq.length := by
      simp only [duration,List.length_cons,Nat.succ_mul]
      omega
    rw [ticks]
    intro P R K M
    exact Procedure.Exec.then head tail M

/-- The transform performs exactly the announced scans on every original word tape. -/
theorem after_any (root first H u l b : ℕ) (m : Memory w)
    (rom : root+(u+l)*span H u l b≤first)
    (limit : first+(u+l+1)*page H u<2^w) :
    (code w root first H u l b 0 (axesList u l)).Exec m
      (after root first H u l b 0 (axesList u l) m) (duration H u (u+l)) := by
  have len : (axesList u l).length=u+l:=by simp [axesList]
  have go : (code w root first H u l b 0 (axesList u l)).Exec m
      (after root first H u l b 0 (axesList u l) m) (duration H u (axesList u l).length) :=
    @transform_any w root first H u l b m 0 (axesList u l)
      (by simpa only [len,Nat.zero_add] using rom) (by simpa only [len,Nat.zero_add] using limit)
  rw [len] at go
  intro P R K M
  exact go M

end
end Hierarchy.DescentPackedWalsh

end OAI
