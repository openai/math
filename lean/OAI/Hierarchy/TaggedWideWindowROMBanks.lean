import OAI.Hierarchy.ProtocolRAMFrozenWindowROM
import OAI.Hierarchy.TaggedWideFrozenSeries
import OAI.Hierarchy.TaggedWideWindowLayout

namespace OAI
/-! # Immutable bank bounds of each purchased format -/

noncomputable section
namespace Hierarchy
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAMReportedPorts TaggedShorterReportAdvice
open scoped Classical

namespace ProtocolRAMFrozenWindow

/-- The thirteen selector columns and the four internal input operands end at
the public advice boundary. Even when that boundary is at the word modulus,
each individual bank size is strictly smaller. -/
theorem Format.rom_banks (f : Format) (W floor : ℕ) (args : Inputs)
    (endBefore : f.adviceEnd≤floor) (word : floor≤2^W) :
    (∀ j : Fin 13,(bank f.rom f.bits j).Fits W floor) ∧
      ∀ b∈[(f.publicInputs args).bias,(f.publicInputs args).classes,
        (f.publicInputs args).weights,(f.publicInputs args).origins],b.Fits W floor := by
  let page:=2^f.bits
  let group:=2^f.gb
  have groupPos : 0<group:=Nat.two_pow_pos _
  have endPos : f.rom+13*page+group+group≤floor:=endBefore
  have pageFit : page<2^W:=by omega
  have groupFit : group<2^W:=by omega
  have numeric (j : Fin 13) : (bank f.rom f.bits j).Fits W floor := by
    have lastColumn:=Nat.mul_le_mul_right page j.isLt
    rw [Nat.succ_mul] at lastColumn
    exact ⟨Nat.two_pow_pos _,pageFit,by change f.rom+j.val*page+page≤floor;omega⟩
  refine ⟨numeric,?_⟩
  intro b member
  simp only [List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl|rfl|rfl|rfl
  · exact ⟨groupPos,groupFit,by change f.rom+13*page+group≤floor;omega⟩
  · exact numeric 3
  · exact numeric 4
  · exact ⟨groupPos,groupFit,endPos⟩

/-- The external receipt can be stated solely on the live directory, translated
socket slots and width column. The fixed public format supplies the other operands. -/
theorem Format.resident_of_external (f : Format) (W floor : ℕ) (args : Inputs)
    (endBefore : f.adviceEnd≤floor) (word : floor≤2^W)
    (owner : args.owner.Fits W floor)
    (external : ∀b∈[args.directory,args.offset,args.left,args.right,args.width],b.Fits W floor) :
    f.Resident W floor (f.publicInputs args) := by
  obtain ⟨selectors,internal⟩:=f.rom_banks W floor args endBefore word
  refine ⟨owner,?_,selectors⟩
  intro b member
  change b∈[args.directory,args.offset,args.left,args.right,args.width,
    (f.publicInputs args).bias,(f.publicInputs args).classes,(f.publicInputs args).weights,
    (f.publicInputs args).origins] at member
  change b∈[args.directory,args.offset,args.left,args.right,args.width]++
    [(f.publicInputs args).bias,(f.publicInputs args).classes,(f.publicInputs args).weights,
      (f.publicInputs args).origins] at member
  exact (List.mem_append.mp member).elim (external b) (internal b)

end ProtocolRAMFrozenWindow

namespace ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe Tagged ProtocolRAMFrozenWindow
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  {κ A : ℝ} (x : WideParent κ A) (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)

/-- Apply the joint format-end estimate to any one of the original height classes. -/
theorem wideWindow_rom_banks (cap start W floor : ℕ) (i : Fin (m+1)) (args : Inputs)
    (endBefore : start+(m+1)*v.wideWindowStride x ell cap≤floor) (word : floor≤2^W) :
    let f:=v.wideWindow x m ell short u δ ξ cap start i
    (∀ j : Fin 13,(bank f.rom f.bits j).Fits W floor) ∧
      ∀ b∈[(f.publicInputs args).bias,(f.publicInputs args).classes,
        (f.publicInputs args).weights,(f.publicInputs args).origins],b.Fits W floor := by
  intro f
  exact f.rom_banks W floor args
    ((v.wideWindow_rom_bound x m ell short u δ ξ cap start i).trans endBefore) word

end ProtocolRAM.Calendar.FixedProtocolFormat
end Hierarchy
end

end OAI
