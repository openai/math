import OAI.Computability.BorderVNP.RoutingISATypedBatchModel
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Fetch, initialize and publish one typed cell in the native team RAM -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.TypedBatch

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem keepReady {base count i : ℕ} {s m es t mt c}
    (r : Runs pub macros c s m es t mt) (ready : Ready base count i s)
    (keep : c.keeps 40=true ∧ c.keeps 41=true ∧ c.keeps 42=true ∧ c.keeps 43=true ∧ c.keeps 44=true ∧ c.keeps 47=true) :
    Ready base count i t := by
  obtain ⟨h40,h41,h42,h43,h44,h47⟩ := keep
  simpa only [Ready,r.keepsReg h40,r.keepsReg h41,r.keepsReg h42,r.keepsReg h43,r.keepsReg h44,
    r.keepsReg h47] using ready

/-- Load the seven real initializer parameters from this local task row. -/
theorem fetch_run {base count i : ℕ} (a : Task) (s : Bank w) (m : Memory w)
    (ready : Ready base count i s) (row : a.Stored m base i) (hi : i < count)
    (space : base+7*count ≤ 2^w) :
    ∃ es t, Runs pub macros fetch s m es t m ∧ traceCost es ≤ fetch.slots ∧
      Ready base count i t ∧ a.cell.Registers t ∧ (t 46).val = a.callRow := by
  have ⟨width,b0,_,ix,stride,one⟩ := ready
  have two : 2 < 2^w := by have h := (s 44).isLt; rw [stride] at h; omega
  have positive : w ≠ 0 := by rintro rfl; simp at two
  change readings s 40 = w at width
  change readings s 41 = base at b0
  change readings s 43 = i at ix
  change readings s 44 = 7 at stride
  change readings s 47 = 1 at one
  have safe : fetch.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [fetch,Code.block,Code.safeReadOnly,Code.evalNat,addressOp,addressOpFits,
      b0,ix,stride,one]
    omega
  obtain ⟨es,t,r,c,hr⟩ := fetch.runReadOnly pub macros m s safe
  obtain ⟨a0,a1,a2,a3,a4,a5,a6⟩ := row
  refine ⟨es,t,r,c,keepReady r ready (by decide),?_⟩
  have fields : readings t 0=0 ∧ readings t 1=1 ∧ readings t 18=2 ∧
      readings t 2=a.cell.descriptorBase ∧ readings t 3=a.cell.descriptorBase+3*a.cell.chunks.length ∧
      readings t 4=a.cell.externalBase ∧ readings t 5=a.cell.external.length ∧
      readings t 6=a.cell.scratchBase ∧ readings t 7=a.cell.burstBase ∧ readings t 8=w ∧
      readings t 20=a.cell.scratchBase ∧ readings t 46=a.callRow := by
    rw [hr]
    simp (config := {decide := true}) [fetch,Code.block,Code.evalNat,addressOp,
      b0,ix,stride,one,width,Nat.add_assoc,Nat.mul_comm] at a0 a1 a2 a3 a4 a5 a6 ⊢
    exact ⟨a0,a1,a2,a3,a4,a5,a4,a6⟩
  obtain ⟨h0,h1,h18,h2,h3,h4,h5,h6,h7,h8,h20,h46⟩ := fields
  exact ⟨⟨⟨h0,h1,h18⟩,h2,h3,h4,h5,h6,h7,h8,h20⟩,h46⟩

private theorem publish_run {base count i : ℕ} (a : Task) (s : Bank w) (m : Memory w)
    (ready : Ready base count i s) (hi : i < count) (fit : a.callRow+2 < 2^w)
    (row : (s 46).val=a.callRow) (dst : (s 5).val=a.cell.burstBase)
    (num : (s 15).val=(a.cell.burst w).length) :
    ∃ es t, Runs pub macros publish s m es t (a.publish m) ∧ traceCost es ≤ publish.slots ∧
      Ready base count (i+1) t := by
  obtain ⟨width,bas,ct,ix,stride,one⟩ := ready
  let u := Function.update s (45 : Reg) (BinaryOp.add.eval (s 46) (s 47))
  let z := Function.update u (45 : Reg) (BinaryOp.add.eval (u 45) (u 47))
  let last := Function.update z (43 : Reg) (BinaryOp.add.eval (z 43) (z 47))
  have a1 : (u 45).val = a.callRow+1 := by
    simp only [u,Function.update_self,BinaryOp.eval,Fin.val_add,row,one,Nat.mod_eq_of_lt (by omega : a.callRow+1 < 2^w)]
  have a2 : (z 45).val = a.callRow+2 := by
    have oneU : (u 47).val = 1 := (congrArg Fin.val (Function.update_of_ne (by decide : (47:Reg) ≠ 45) ..)).trans one
    simp only [z,Function.update_self,BinaryOp.eval,Fin.val_add,a1,oneU,Nat.mod_eq_of_lt fit]
  have v1 : u 5 = DiagonalResidueRAM.word w a.cell.burstBase := by
    rw [← dst]
    apply Fin.ext
    simp (config := {decide := true}) [u,DiagonalResidueRAM.word]
  have v2 : z 15 = DiagonalResidueRAM.word w (a.cell.burst w).length := by
    rw [← num]
    apply Fin.ext
    simp (config := {decide := true}) [u,z,DiagonalResidueRAM.word]
  have add₁ : Runs pub macros (.binary .add 45 46 47) s m [tick w] u m := .localStep m rfl rfl
  have store₁ := Runs.store pub macros 45 5 u m
  rw [a1,v1] at store₁
  let m₁ := Function.update m (a.callRow+1) (DiagonalResidueRAM.word w a.cell.burstBase)
  have add₂ : Runs pub macros (.binary .add 45 45 47) u m₁ [tick w] z m₁ := .localStep m₁ rfl rfl
  have store₂ := Runs.store pub macros 45 15 z m₁
  rw [a2,v2] at store₂
  have advance : Runs pub macros (.binary .add 43 43 47) z (a.publish m) [tick w] last (a.publish m) :=
    .localStep _ rfl rfl
  refine ⟨_,last,add₁.seq (store₁.seq (add₂.seq (store₂.seq advance))),le_rfl,?_⟩
  have room := ct ▸ (s 42).isLt
  simp (config := {decide := true}) [Ready,last,z,u,BinaryOp.eval,Fin.val_add,width,bas,ct,ix,stride,one,
    Nat.mod_eq_of_lt (by omega : i+1 < 2^w)]

/-- Execute a real directory read, a genuine fixed private-packet initializer and the
stores publishing its actual output registers. No argument pointer or count is guessed. -/
theorem body_run {base count i : ℕ} (a : Task) (s : Bank w) (m : Memory w)
    (ready : Ready base count i s) (stored : a.Stored m base i) (hi : i < count)
    (space : base+7*count ≤ 2^w) (fit : a.callRow+2 < 2^w) (data : a.cell.Stored m)
    (room : a.cell.Room w) :
    ∃ es t, Runs pub macros body s m es t (a.publish (a.cell.image m)) ∧
      traceCost es ≤ fetch.slots+a.cell.cost w+publish.slots ∧ Ready base count (i+1) t := by
  obtain ⟨gs,x,rx,cx,hx,entry,row⟩ := fetch_run (pub := pub) (macros := macros) a s m ready stored hi space
  obtain ⟨hs,y,mt,ry,cy,dst,num,mem⟩ := CellPacket.initializer_run pub macros a.cell x m entry data room
  have he : mt = a.cell.image m := funext fun k => Fin.ext (congrFun mem k)
  subst mt
  obtain ⟨fs,z,rz,cz,hz⟩ := publish_run (pub := pub) (macros := macros) a y (a.cell.image m)
    (keepReady ry hx (by decide)) hi fit
    ((congrArg Fin.val (ry.keepsReg (by decide : CellPacket.initializer.keeps 46=true))).trans row) dst num
  refine ⟨_,z,rx.seq (ry.seq rz),?_,hz⟩
  simp only [traceCost,VPVNP.RAMBuckets.cost_append] at *
  omega

end RoutingISA.TypedBatch

end BorderVNP
end Computability
end OAI
