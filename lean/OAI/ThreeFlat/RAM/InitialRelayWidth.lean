import OAI.ThreeFlat.RAM.HeaderScanProcedure

namespace OAI
/-! # Constant width bootstrap for every physical edge of the initial cursor
The seed header stores the width base in word two and the total number of
outgoing lifted edges in word three. Each edge carries one bit per tag. -/

namespace ThreeFlat.RAM.InitialRelayWidth

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing

variable {W : ℕ}

def width (d low slots : ℕ) := (1+(d+d))*(2^low*(slots*3))

theorem width_card (d low slots : ℕ) :
    width d low slots = Fintype.card (Fin (1+(d+d)) × Fin (2^low) × Fin slots × Fin 3) := by
  simp [width]

def procedure (current : Word W) (t : ℕ) : Procedure W :=
  HeaderScan.procedure current 2 3 (.literal (t : Word W))

theorem size (current : Word W) (t : ℕ) :
    (procedure current t).labels=17 ∧ (procedure current t).registers=5 ∧ (procedure current t).slots=0 :=
  ⟨rfl,rfl,rfl⟩

def loaded (current : Word W) (base count : ℕ) (m : Memory W) : Prop :=
  m (m current.val+2).val=(base : Word W) ∧ m (m current.val+3).val=(count : Word W)

def image (base count t : ℕ) (m : Memory W) : Memory W :=
  fillSegment base count (fun _ => (t : Word W)) m

theorem spec (current : Word W) (base count t : ℕ) (fit : base+count<2^W) :
    (procedure current t).Spec (loaded current base count)
      (fun m out => out=image base count t m) (13+count*6) := by
  apply HeaderScan.spec current 2 3 (.literal (t : Word W)) _ (fun _ => base) (fun _ => count)
    (fun _ _ => (t : Word W))
  · exact fun _ _ => ⟨fit,le_rfl⟩
  · exact fun _ h => h
  · intros
    rfl

theorem image_word (base count t : ℕ) (m : Memory W) (j : Fin count) :
    image base count t m (base+j.val)=(t : Word W) := by
  have := j.isLt
  simp [image,fillSegment,show base≤base+j.val by omega,show base+j.val<base+count by omega]

theorem image_outside (base count t : ℕ) (m : Memory W) (a : ℕ) (h : a<base ∨ base+count≤a) :
    image base count t m a=m a := by
  simp [image,fillSegment,show ¬(base≤a ∧ a<base+count) by omega]

end ThreeFlat.RAM.InitialRelayWidth

end OAI
