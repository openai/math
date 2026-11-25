import OAI.Computability.BorderVNP.CubeScatterPaddingFit
import OAI.Computability.BorderVNP.CubeScatterPaddingSetup
import OAI.Computability.BorderVNP.CubeISAHeaderInstallGeometry
import OAI.Computability.BorderVNP.CubeISAHeaderDecodeReadout
import OAI.Computability.BorderVNP.RoutingISACubePowers

/-! # The padding verifier's operands in the actual primary and secondary headers -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Padding

open RoutingISA RoutingISA.CubeHeaderInstall VPVNP.BurstRAM DiagonalResidueRAM Tally

/-- Native allocations whose pointers are read from the literal primary extension. -/
structure Pointers where
  /-- The base-d powers array. -/
  powers : ℕ
  /-- One owner number per grouping symbol. -/
  owners : ℕ
  /-- One occupied width per directed pair. -/
  widths : ℕ
  /-- Three native address fields per directed pair. -/
  triples : ℕ
  /-- First word of the complete singleton reservation. -/
  singles : ℕ

/-- Padding and host-scatter extension fields shared by the actual 81-word decoder. -/
def Pointers.operand (P : Pointers) (n d b h K s : ℕ) : ℕ → Option ℕ
  | 56 => some (d^(n+1)) | 57 => some P.widths | 62 => some P.powers | 77 => some P.owners
  | 88 => some P.singles | 91 => some P.triples | 93 => some (bankWidth n b h K s)
  | 94 => some (selectorWidth n K h) | _ => none

/-- Decode any of these eight real scalar words through both overlays in the supplied
literal stream. This lemma also applies when another frame builder spells the same words. -/
theorem Pointers.resident_at {w : ℕ} (P : Pointers) (pub : Arg → Word w) (m : Memory w)
    (old : Fin 81 → Word w) (fresh profile gates outputs width off ell d n blocks b h K s : ℕ)
    {field v : ℕ}
    (installed : ∀ j : Fin 81, 31+j.val=field → m ((pub 0).val+31+j.val) =
      jointFields old fresh profile gates outputs width off ell d n blocks b h s j)
    (literal : ∀ j : Fin 81, ∀ v, P.operand n d b h K s (31+j.val) = some v → (old j).val = v)
    (chosen : P.operand n d b h K s field = some v) :
    readings m ((pub 0).val+field) = v := by
  have active : field ∈ [56,57,62,77,88,91,93,94] := by unfold operand at chosen; split at chosen <;> simp_all
  have bounds : 31 ≤ field ∧ field ≤ 111 := by simp at active; omega
  let j : Fin 81 := ⟨field-31,by omega⟩
  have e : j.val+31 = field := by dsimp [j]; omega
  have raw := installed j (by omega)
  unfold jointFields at raw
  rw [GeometryAdvice.Allocation.fields_other _ _ _ _ _ _ _ _ j (by simp [e] at active ⊢; omega),
    pinFields_other _ _ _ _ _ _ _ _ j (by simp [e] at active ⊢; omega)] at raw
  have addr : (pub 0).val+31+j.val = (pub 0).val+field := by omega
  rw [addr] at raw
  exact (congrArg Fin.val raw).trans (literal j v (by simpa only [Nat.add_comm 31,e] using chosen))

/-- Read from a complete freshly installed extension. -/
theorem Pointers.resident {w : ℕ} (P : Pointers) (pub : Arg → Word w) (m : Memory w)
    (old : Fin 81 → Word w) (fresh profile gates outputs width off ell d n blocks b h K s : ℕ)
    (installed : ∀ j : Fin 81, m ((pub 0).val+31+j.val) =
      jointFields old fresh profile gates outputs width off ell d n blocks b h s j)
    (literal : ∀ j : Fin 81, ∀ v, P.operand n d b h K s (31+j.val) = some v → (old j).val = v)
    {field v : ℕ} (chosen : P.operand n d b h K s field = some v) :
    readings m ((pub 0).val+field) = v :=
  Pointers.resident_at P pub m old fresh profile gates outputs width off ell d n blocks b h K s (fun j _ => installed j) literal chosen

/-- The dynamic declaration decoder preserves its static block-count and packet pointer,
including when either packet rectangle is empty. -/
theorem secondary_banks (stat : CubeHeaderInstall.Inputs) (n bits broadcast : ℕ) (old : ℕ → ℕ) :
    let final := (stat.decoder broadcast).finalImage (stat.image n bits old)
    final (stat.header+7) = stat.blocks ∧ final (stat.header+8) = stat.packetBase := by
  intro final
  have preserve (j : ℕ) (lo : 7 ≤ j) (hi : j ≤ 8) :
      final (stat.header+j) = stat.value n bits j := by
    change (stat.decoder broadcast).finalImage _ _ = _
    rw [HeaderDecode.Layout.finalOutside _ _ (by change _ ≠ stat.header+5; omega)
      (Or.inl (by change _ < stat.header+13+stat.entries; omega))
      (Or.inl (by change _ < stat.header+13+2*stat.entries; omega))]
    simp [Inputs.image,show stat.header+j < stat.header+13 by omega]
  exact ⟨preserve 7 le_rfl (by decide),preserve 8 (by decide) le_rfl⟩

/-- Read the selected coordinate divisor from the actual image of the native powers install. -/
theorem installed_power {n d base : ℕ} (old : ℕ → ℕ) (i : Fin (n+1)) :
    CubePowers.image d base (n+1) old (base+i.val) = d^i.val := by simp [CubePowers.image,i.isLt]

end Cube.Padding

end BorderVNP
end Computability
end OAI
