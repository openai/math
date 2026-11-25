import OAI.ThreeFlat.RAM.PhysicalInputPhases
import OAI.ThreeFlat.Diagonal.TickScratchRegion

namespace OAI
/-! # Native receiver-local copy of all eight published fields into S44 -/

namespace ThreeFlat.Diagonal.NavigationPass.NodePublication
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.PhysicalProcedure

/-- Only these three immediate public operands vary with the receiver chart. -/
def receiverCopy (W age source n : ℕ) : Procedure W :=
  PhysicalInputPhases.copying W source (8*n) (TickWorkspace.base age 44)

theorem receiverCopy_hardware (W age source n : ℕ) :
    (receiverCopy W age source n).labels=10 ∧ (receiverCopy W age source n).registers=5 ∧
      (receiverCopy W age source n).slots=3 := ⟨rfl,rfl,rfl⟩

structure CopiedNodes {W : ℕ} (age source n : ℕ) (before after : Memory W) : Prop where
  exactState : after=PhysicalInputCopy.copied source (8*n) (TickWorkspace.base age 44) before
  column : ∀ id<n, ∀ j : Fin 8,
    after (TickWorkspace.base age 44+8*id+j.val)=before (source+8*id+j.val)
  outside : ∀ x, x<TickWorkspace.base age 44 ∨ TickWorkspace.base age 44+8*n≤x → after x=before x

/-- The source is the independently emitted physical array in the receiver's own preceding state. -/
theorem receiverCopy_spec {W : ℕ} (age source n : ℕ)
    (sourceFits : source+8*n<2^W) (dstFits : TickWorkspace.base age 44+8*n<2^W)
    (ordered : TickWorkspace.base age 44≤ source) :
    (receiverCopy W age source n).Spec (fun _=>True) (CopiedNodes age source n) (6+40*n) := by
  intro p r k machine labels regs rom exit installed data config input pc _
  obtain ⟨steps,clock,st,out,advance,finish,copy⟩ :=
    PhysicalInputPhases.copying_spec source (8*n) (TickWorkspace.base age 44)
      sourceFits dstFits (Or.inl ordered) machine labels regs rom exit installed data config input pc trivial
  subst out
  refine ⟨steps,by omega,st,_,advance,finish,rfl,?_,
    PhysicalInputCopy.copied_outside source (8*n) (TickWorkspace.base age 44) input⟩
  intro id small j
  simpa only [Nat.add_assoc] using PhysicalInputCopy.copied_at source (8*n) (TickWorkspace.base age 44)
    input (8*id+j.val) (by have := j.isLt; omega)

/-- The copy fits between the legacy join/cache arena and the high retained physical sectors.
The complete eight-word copy of the published roots is covered by the common `2^(4w/5)` startup. -/
theorem receiverCopy_chart {w age n : ℕ} (hw : 40≤w) (lower : 3*w≤age^10)
    (upper : age^10≤5*w) (count : n≤2^(3*w/5)) :
    let source:=16*2^(32*w)+16*(2^w)^4
    TickWorkspace.base age 44+8*n≤TickWorkspace.base age 45 ∧
      TickWorkspace.base age 45≤16*2^(32*w) ∧ source+8*n<2^(64*w) ∧ 6+40*n≤2^(4*w/5) := by
  intro source
  have u4 : (2^w)^4=2^(4*w) := by rw [←pow_mul,Nat.mul_comm w 4]
  have v4 : TickWorkspace.stride age=2^(4*(age^10)) := by
    unfold TickWorkspace.stride
    rw [←pow_mul,Nat.mul_comm (age^10) 4]
  have extent : 8*n≤2^(4*w) := calc
    _ ≤ 2^3*2^(3*w/5) := Nat.mul_le_mul_left _ count
    _ = 2^(3+3*w/5) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have resident : 8*n≤TickWorkspace.stride age := by
    rw [v4]
    exact extent.trans (Nat.pow_le_pow_right (by decide) (by omega))
  have fitV : TickWorkspace.stride age≤2^(20*w) := by
    rw [v4]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have disj : 46*TickWorkspace.stride age≤2^(32*w) := calc
    _ ≤ 2^6*2^(20*w) := Nat.mul_le_mul (by decide) fitV
    _ = 2^(6+20*w) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have short : 2^(4*w)≤2^(32*w) := Nat.pow_le_pow_right (by decide) (by omega)
  have budget : 6+40*n≤2^(4*w/5) := calc
    _ ≤ 2^6*2^(3*w/5) := by have := Nat.two_pow_pos (3*w/5); omega
    _ = 2^(6+3*w/5) := (pow_add ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  refine ⟨?_,?_,?_,budget⟩
  · change 45*TickWorkspace.stride age+8*n≤46*TickWorkspace.stride age
    omega
  · change 46*TickWorkspace.stride age≤16*2^(32*w)
    omega
  · dsimp only [source]
    rw [u4]
    calc
      _ ≤ 2^6*2^(32*w) := by omega
      _ = 2^(6+32*w) := (pow_add ..).symm
      _ < _ := Nat.pow_lt_pow_right (by decide) (by omega)

theorem receiverCopy_high_spec {w age n : ℕ} (hw : 40≤w) (lower : 3*w≤age^10)
    (upper : age^10≤5*w) (count : n≤2^(3*w/5)) :
    let source:=16*2^(32*w)+16*(2^w)^4
    (receiverCopy (64*w) age source n).Spec (fun _=>True)
      (fun initial out=>CopiedNodes age source n initial out ∧
        ∀ x,16*2^(32*w)≤x → out x=initial x) (2^(4*w/5)) := by
  intro source
  obtain ⟨outEnd,above,srcEnd,clock⟩:=receiverCopy_chart hw lower upper count
  have order : TickWorkspace.base age 44≤ source := by
    dsimp only [source]
    omega
  have dstFit : TickWorkspace.base age 44+8*n < 2^(64*w) := by omega
  intro p r k machine labels regs rom exit installed data config input pc _
  obtain ⟨steps,cost,st,out,advance,finish,copied⟩ :=
    receiverCopy_spec age source n srcEnd dstFit order
      machine labels regs rom exit installed data config input pc trivial
  exact ⟨steps,cost.trans clock,st,out,advance,finish,copied,
    fun x hx=>copied.outside x (Or.inr (by omega))⟩

end ThreeFlat.Diagonal.NavigationPass.NodePublication

end OAI
