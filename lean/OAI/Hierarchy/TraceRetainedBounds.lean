import OAI.ThreeFlat.Diagonal.PhysicalBlockLength
import OAI.Hierarchy.TraceNativePorts
import OAI.Hierarchy.TraceRetainedScale
import OAI.Hierarchy.PhysicalTracePlan
import OAI.ThreeFlat.Diagonal.ProgramDirectory
import OAI.ThreeFlat.Diagonal.PhysicalRunWidth
import OAI.ThreeFlat.Diagonal.PhysicalBlockWidthCost

namespace OAI
/-! # Uniform bounds on the actual predecessor widths and heap allocations -/

noncomputable section
namespace Hierarchy.TraceAdmission
open ThreeFlat Diagonal Diagonal.PhysicalStage
open TraceDistribution NavigationDirectory Filter
open scoped BigOperators Classical

variable {F : Type} [Field F] (B : Block F)

private theorem recast_ceiling {d l l' b : ℕ} (e : l=l') (A : State d l)
    (r : Run F (e ▸ A : State d l')) (bounded : r.WidthCeiling b) :
    (Program.recast e A r).WidthCeiling b := by cases e; exact bounded

theorem native_width_ceiling {k : ℕ} (hk : 2≤k+1) (low offsets slots n : ℕ)
    (fits : B.blockCharge*n≤k+1) :
    (Physical.run B hk low offsets slots n fits).WidthCeiling
      (((B.cursorState hk low offsets slots).maxWidth+1)*B.widthBase^n) := by
  let P := B.repeat n
  let rem := k+1-P.charge
  have e : k+1=P.charge+rem := by
    dsimp [rem,P]; rw [B.charge_repeat]; omega
  let A := B.cursorState hk low offsets slots
  change (Program.recast e A (P.run rem (e ▸ A))).WidthCeiling _
  apply recast_ceiling
  simpa only [P,State.maxWidth_cast_lanes,B.widthCost_repeat_eq_pow] using
    P.run_widthCeiling rem (e ▸ A)

/-- Every predecessor on every adaptive history has a valid width file for the
writer. This bound includes both terminal leaves and the pre-branch states. -/
theorem eventual_width_ceiling {u s : ℕ→ℕ} (scale : Scale u s) (a b : ℕ) :
    ∀ᶠ w : ℕ in atTop, ∀ {k} (hk : 2≤k+1) (offsets slots : ℕ)
      (_ports : offsets*slots*3≤a*(w+1)^b) (fits : B.blockCharge*s w≤k+1),
      (Physical.run B hk (w/2) offsets slots (s w) fits).WidthCeiling ((2^w)^4) := by
  filter_upwards [multiplicity_small scale 1 a b B.widthBase] with w bounded
  intro k hk offsets slots ports fits
  let A := B.cursorState hk (w/2) offsets slots
  have old : A.maxWidth≤2^(w/2)*(a*(w+1)^b) := A.maxWidth_le fun i=>by
    rw [B.cursorState_width]
    exact Nat.mul_le_mul_left _ ports
  have step : (A.maxWidth+1)*B.widthBase^s w ≤ 2^(3*w/5) :=
    (Nat.mul_le_mul_right _ (Nat.add_le_add_right old 1)).trans (by simpa only [one_mul] using bounded)
  apply (Physical.run B hk (w/2) offsets slots (s w) fits).widthCeiling_mono _
    (native_width_ceiling B hk (w/2) offsets slots (s w) fits)
  exact step.trans ((Nat.pow_le_pow_right (by decide) (by omega : 3*w/5≤w)).trans
    (Nat.le_self_pow (by decide) _))

/-- The predecessor width ceiling for the actual machine trace table, allowing
the gate text and register counts to vary with the word width. -/
theorem eventual_native_width_ceiling [Fintype F] {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ {pc regs words k : ℕ} (_pcSize : pc≤64*w)
      (_regSize : regs≤64*w) (_wordSize : words≤64*w) (hk : 2≤k+1)
      (_axes : k+1=u w+1-w/2) (M : Computability.VPVNP.BurstRAM.PrivateRAM.Machine (64*w) pc regs words)
      {N base fuel : ℕ} (fit : NativeTrace.Fits M N base ((k+1)+w/2) fuel)
      (q : Fintype.card F≤2^(64*w)) (st : Computability.VPVNP.BurstRAM.Word (64*w))
      (blocks : B.blockCharge*s w≤k+1),
      let slots := (TraceStaticRow.gateTable q fit.width fit.labels base fuel st regs words
        ((k+1)+w/2)).cells
      let offsets := 1+(((k+1)+w/2)+((k+1)+w/2))
      (Physical.run B hk (w/2) offsets slots (s w) blocks).WidthCeiling ((2^w)^4) := by
  filter_upwards [eventual_width_ceiling B scale (3*5*10^26*65^14) 15,
    eventual_native_port_count (F:=F) scale] with w bounded ports
  intro pc regs words k pcSize regSize wordSize hk axes M N base fuel fit q st blocks slots offsets
  exact bounded hk offsets slots (ports pcSize regSize wordSize axes M fit q st) blocks

theorem repeated_length (n : ℕ) : (B.repeat n).length=(B.levels+1)*n :=
  B.length_repeat n

/-- The sum of all real chronological allocations fits in one archive segment,
including adaptive graph, width, child and parent files. -/
theorem eventual_stage_heap {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ _fits : B.blockCharge*s w ≤ u w+1-w/2,
      let k:=u w+1-w/2
      let P:=B.repeat (s w)
      ((P.directory (k-P.charge) k).map Stage.heapWords).sum ≤ 2^(3*w/5) := by
  filter_upwards [record_room scale ((B.levels+1)*B.allocations.sum)] with w room
  intro fit k P
  have split : P.charge+(k-P.charge)=k := by
    have : P.charge≤k := by simpa [P,B.charge_repeat] using fit
    omega
  have heap := P.allocation_words B.allocations.sum (B.allocation_bound (s w)) (k-P.charge) k
  rw [split,show P.length=(B.levels+1)*s w from repeated_length B (s w)] at heap
  calc
    _ ≤ (B.levels+1)*s w*B.allocations.sum*(1+k*2^k) := heap
    _ = ((B.levels+1)*B.allocations.sum)*s w*(1+k*2^k) := by ring
    _ ≤ ((B.levels+1)*B.allocations.sum)*(s w+1)*(1+k*2^k)*(64*w+1) := by
      apply le_trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.le_succ _)))
      exact Nat.le_mul_of_pos_right _ (by omega)
    _ ≤ _ := room

theorem eventual_stage_headers {u s : ℕ→ℕ} (scale : Scale u s) :
    ∀ᶠ w : ℕ in atTop, ∀ rem axes : ℕ,
      64*((((B.repeat (s w)).directory rem axes).length)+2) ≤ 2^(3*w/5) := by
  filter_upwards [record_room scale (64*(B.levels+3))] with w room
  intro rem axes
  rw [Program.directory_length,repeated_length]
  let v := 1+(u w+1-w/2)*2^(u w+1-w/2)
  have h : 64*((B.levels+1)*s w+2) ≤ (64*(B.levels+3))*(s w+1) := by ring_nf; omega
  exact (h.trans (Nat.le_mul_of_pos_right _ (show 0<v by dsimp [v]; omega))).trans
    ((Nat.le_mul_of_pos_right _ (by omega : 0<64*w+1)).trans room)

end Hierarchy.TraceAdmission

end
end OAI
