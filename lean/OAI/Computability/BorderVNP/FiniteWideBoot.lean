import OAI.Computability.BorderVNP.GeometryAdviceStripe

/-! # Deinterleaving the first finite-field startup frame for any batch size

The small-batch proof needs the 81 extended-frame words even when there is
only one processor in a team. Three initialized boot-frame fields suffice to
read the occupied bits in consecutive literal stripes. The width is computed
from the actual bit count and processor count by one division.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteBoot

open GeometryAdvice RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

/-- Number of occupied positions per processor, allowing a final partial stripe. -/
def width (count processors : ℕ) := (count-1)/processors + 1

/-- At every positive team size, all bits fit, including the entire frame
on the single processor when the batch size is one. -/
theorem capacity (count processors : ℕ) (hp : 0 < processors) : count ≤ processors * width count processors := by
  have h : (count-1)/processors < width count processors := Nat.lt_succ_self _
  have hh := (Nat.div_lt_iff_lt_mul hp).mp h
  rw [Nat.mul_comm] at hh
  omega

/-- Any interval large enough in aggregate also fits the rounded local stripe. -/
theorem width_le {count processors bound : ℕ} (hc : 0 < count) (hp : 0 < processors)
    (h : count ≤ processors*bound) : width count processors ≤ bound := by
  unfold width
  apply (Nat.div_lt_iff_lt_mul hp).mpr
  rw [Nat.mul_comm]
  omega

/-- The literal address, bit count, and dense destination from the original
31-word boot frame. The memory word length fixes the serialized field length. -/
def bootStripe (a : AdviceLayout) (f : BroadcastFrame) (words : ℕ) : Stripe :=
  ⟨a.offset,width a.count f.processors,a.dst,words⟩

/-- Compute the real stripe width, processor stride, and loop bounds solely
from initial frame fields 1–4 and 26–28. -/
def setup : Code := .block [
  .constant 0 0,.constant 1 1,.constant 17 2,
  readFrame 2 62 63 1,readFrame 3 62 63 2,readFrame 4 62 63 3,readFrame 5 62 63 4,
  readFrame 6 62 63 26,readFrame 12 62 63 27,readFrame 8 62 63 28,
  .binary .sub 11 2 1,.binary .mul 11 11 5,.binary .mul 16 4 17,.binary .add 11 16 11,
  .binary .sub 7 12 1,.binary .div 7 7 3,.binary .add 7 7 1,.copy 13 0]

/-- The fixed all-batch startup loop uses the same native bit-copy table as the
later geometry reader, at its own initialized frame addresses. -/
def readWideLiteralAdvice : Code := .seq setup (.whileLt 13 12 copyStripeBit)

private theorem read_fit {w : ℕ} (d : Reg) (field : Word 8) (pub : Arg → ℕ) (mem : ℕ → ℕ)
    (s : Reg → ℕ) : (readFrame d 62 63 field).safeReadOnly w pub mem s ↔ pub 0 + field.val < 2^w := by
  simp (config := { decide := true }) [readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits]
  omega

/-- Actual startup instructions set the bit-copy loop registers. The computation
needs no previously installed extended-frame word. -/
theorem setup_run {w : ℕ} (a : AdviceLayout) (f : BroadcastFrame) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (frame : f.At (readings pub) (readings m)) (layout : a.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (hc : 0 < a.count) (bound : a.dst + a.count < 2^w) :
    ∃ es t, Runs pub mac setup s m es t m ∧ traceCost es ≤ setup.slots ∧
      readings t 1 = 1 ∧ readings t 6 = a.offset ∧ readings t 7 = width a.count f.processors ∧
      readings t 8 = a.dst ∧ readings t 11 = f.stride ∧ readings t 12 = a.count ∧ readings t 13 = 0 := by
  obtain ⟨_,R,procs,lit,link,_,_⟩ := frame
  obtain ⟨o,count,dest⟩ := layout
  have room : readings pub 0 + 31 < 2^w := fit.frame.trans_lt ((Nat.le_add_right f.dst f.header).trans_lt fit.out)
  have sr : 2*f.literal+(f.teams-1)*f.link < 2^w :=
    (Nat.le_mul_of_pos_left f.stride fit.procs).trans_lt (fit.input.trans_lt (pub 0).isLt)
  have hw : w ≠ 0 := by rintro rfl; simp at room
  have widthFit : (a.count-1)/f.processors + 1 < 2^w := by
    have h := Nat.div_le_self (a.count-1) f.processors
    omega
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := { decide := true }) [setup,Code.block,Code.safeReadOnly,Code.evalNat,
      read_fit,readFrameFixed,addressOpFits,addressOp,R,procs,lit,link,count,hw]
    have := fit.three
    have := fit.procs
    omega
  obtain ⟨es,z,run,ct,hz⟩ := setup.runReadOnly pub mac m s safe
  refine ⟨es,z,run,ct,?_⟩
  rw [hz]
  simp (config := {decide := true}) [setup,Code.block,Code.evalNat,readFrameFixed,addressOp,
    BroadcastFrame.stride,width,R,procs,lit,link,o,dest,count,Nat.mul_comm]

end FiniteBoot

end BorderVNP
end Computability
end OAI
