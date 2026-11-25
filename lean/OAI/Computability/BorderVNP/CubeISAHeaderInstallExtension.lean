import OAI.Computability.BorderVNP.GeometryAdviceAllocation
import OAI.Computability.BorderVNP.TransmissionJointHeaderBoot
import OAI.Computability.BorderVNP.CubePhysicalDeclarationWords

/-! # Pinned operands for the cube's secondary-header constructor

The additional three scalar words in the ordinary 81-word extension hold
the block count, the length of the geometry profile, and the physical
declaration cap. The cube uses its existing alphabet, dimension, block
width and header-pointer words. The geometry reader installs its own
disjoint fields on the same extension.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CubeHeaderInstall

open VPVNP.BurstRAM DiagonalResidueRAM TeamContraction.JointHeader
open TeamContraction.ProcessorSlots

/-- Scalar values used by the secondary header bootstrap, indexed by their
absolute primary frame field. -/
def operand (header d a bc blocks profile cap field : ℕ) : Option ℕ :=
  match field with
  | 59 => some d
  | 60 => some a
  | 61 => some bc
  | 63 => some header
  | 109 => some blocks
  | 110 => some profile
  | 111 => some cap
  | _ => none

/-- Fill the seven cube scalar fields, retaining all other physical operands
including the power table in field 62. -/
def pinFields {w : ℕ} (old : Fin 81 → Word w) (header d a bc blocks profile cap : ℕ)
    (j : Fin 81) : Word w :=
  match operand header d a bc blocks profile cap (j.val+31) with
  | some v => word w v
  | none => old j

/-- All other extension slots, including the power table and placement arrays,
retain the values supplied by the caller. -/
theorem pinFields_other {w : ℕ} (old : Fin 81 → Word w) (header d a bc blocks profile cap : ℕ)
    (j : Fin 81) (outside : j.val+31 ∉ [59,60,61,63,109,110,111]) :
    pinFields old header d a bc blocks profile cap j = old j := by
  have h : operand header d a bc blocks profile cap (j.val+31) = none := by
    unfold operand
    split <;> simp_all
  simp [pinFields,h]

/-- Put the secondary header immediately after the geometry allocation and
fill both parts of the actual processor's extended frame. -/
def jointFields {w : ℕ} (old : Fin 81 → Word w) (fresh profile gates outputs width off ell : ℕ)
    (d n blocks b h s : ℕ) : Fin 81 → Word w :=
  GeometryAdvice.Allocation.fields
    (pinFields old (GeometryAdvice.Allocation.stop fresh profile gates outputs width w)
      d (n+1) (h*b) blocks profile (Cube.Physical.declarationCap n d blocks b h s))
    fresh profile gates outputs width off ell

/-- Any resident copy of the chosen joint extension supplies the prescribed cube scalars. -/
theorem resident_operand_at {w : ℕ} (pub : Arg → Word w) (m : Memory w)
    (old : Fin 81 → Word w) (fresh profile gates outputs width off ell d n blocks b h s : ℕ)
    {field value : ℕ}
    (installed : ∀ j : Fin 81, 31+j.val=field → m ((pub 0).val+31+j.val) =
      jointFields old fresh profile gates outputs width off ell d n blocks b h s j)
    (chosen : operand (GeometryAdvice.Allocation.stop fresh profile gates outputs width w)
      d (n+1) (h*b) blocks profile (Cube.Physical.declarationCap n d blocks b h s) field = some value)
    (fit : value < 2^w) : readings m ((pub 0).val+field) = value := by
  have hfield : field ∈ [59,60,61,63,109,110,111] := by
    unfold operand at chosen
    split at chosen <;> simp_all
  have fieldBounds : 31 ≤ field ∧ field ≤ 111 := by simp at hfield; omega
  let j : Fin 81 := ⟨field-31,by omega⟩
  have e : j.val+31 = field := by dsimp [j]; omega
  have hgeo : j.val+31 ∉ [96,97,98,99,100,101,104,105,106,107,108] := by
    simp [e] at hfield ⊢
    omega
  have raw := installed j (by omega)
  unfold jointFields at raw
  rw [GeometryAdvice.Allocation.fields_other _ _ _ _ _ _ _ _ j hgeo] at raw
  simp only [pinFields,e,chosen] at raw
  have eqn : (pub 0).val+31+j.val = (pub 0).val+field := by omega
  rw [eqn] at raw
  exact (congrArg Fin.val raw).trans (word_val w value fit)

/-- Read from a complete freshly installed extension. -/
theorem resident_operand {w : ℕ} (pub : Arg → Word w) (m : Memory w)
    (old : Fin 81 → Word w) (fresh profile gates outputs width off ell d n blocks b h s : ℕ)
    (installed : ∀ j : Fin 81, m ((pub 0).val+31+j.val) =
      jointFields old fresh profile gates outputs width off ell d n blocks b h s j)
    {field value : ℕ} (chosen : operand (GeometryAdvice.Allocation.stop fresh profile gates outputs width w)
      d (n+1) (h*b) blocks profile (Cube.Physical.declarationCap n d blocks b h s) field = some value)
    (fit : value < 2^w) : readings m ((pub 0).val+field) = value :=
  resident_operand_at pub m old fresh profile gates outputs width off ell d n blocks b h s (fun j _ => installed j) chosen fit

/-- Readback of any pinned cube scalar from the real processor startup,
after the residue, reference and geometry extensions have been jointly installed. -/
theorem boot_operand {w D : ℕ} {L : Pins.Layout} {F : Pins.ProcessorFields L}
    {f : BroadcastFrame} {A : AdviceLayout} {p : ReferencePacket w D}
    {pub : Arg → Word w} {bits : List Bool} {reg : Bank w} {m : Memory w}
    (boot : BootHeaderState F f A p pub bits reg m)
    (old : Fin 81 → Word w) (fresh profile gates outputs width off ell d n blocks b h s : ℕ)
    (pins : p.extension = jointFields old fresh profile gates outputs width off ell d n blocks b h s)
    {field value : ℕ} (chosen : operand (GeometryAdvice.Allocation.stop fresh profile gates outputs width w)
      d (n+1) (h*b) blocks profile (Cube.Physical.declarationCap n d blocks b h s) field = some value)
    (fit : value < 2^w) : readings m ((pub 0).val+field) = value := by
  exact resident_operand pub m old fresh profile gates outputs width off ell d n blocks b h s
    (fun j => (boot.extension j).trans (congrFun pins j)) chosen fit

end RoutingISA.CubeHeaderInstall

end BorderVNP
end Computability
end OAI
