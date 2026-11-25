import OAI.Computability.BorderVNP.CubeRouteProfileInputs
import OAI.Computability.BorderVNP.PackedHistoryRoutingControls
import OAI.Computability.BorderVNP.RoutingISASignedTaskArena

/-! # Secondary cell-bank controls in the published demand directory

The geometry circuit emits the control vector past its original and live placement
tables. The private slot writer touches only earlier counters and slots. Compaction
writes into the demand workspace reserved before the geometry output. Thus the
bank and stride read through frame 92 are the selected task arena's actual words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit

open VPVNP BurstRAM VerifierNetwork RoutingISA GeometryFrameEncoding DiagonalResidueRAM ParseBatchSort
open Packing Packing.RoutingOutputs Diagonal.ExternalSew.FieldExport

variable {W frame origin edges cells entries desc gap live next : ℕ} {before placed : Memory W}

/-- Every addressed secondary control survives private-slot assignment and publication
of the positive-width directory in its reserved interval before the geometry output. -/
theorem directoryPublished_control (rows : List Directory.Row)
    (place : (privateLayout frame origin edges cells entries desc gap).Image (readings before) entries (readings placed))
    (lower : frame+112 ≤ next) (room : next+7*rows.length ≤ origin) (j : ℕ) :
    let c := controlsBase origin edges cells entries live+j
    Directory.ISA.publish placed frame next rows c = before c := by
  intro c
  have large : origin ≤ c := by dsimp [c,controlsBase,bases]; omega
  rw [CableTriples.published_outside placed frame next rows c (by omega) (Or.inr (by omega))]
  apply Fin.ext
  apply place.outside
  · intro j' hj
    dsimp [c,controlsBase,privateLayout,bases]
    omega
  · right
    dsimp [c,controlsBase,privateLayout,bases,PrivatePlacement.Layout.scratch,PrivatePlacement.Layout.supplied]
    omega

/-- The original indirect pointer and every physical control word at the actual
pre-schedule memory, including both cell-bank controls. -/
theorem directoryPublished_controls (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ)
    (values : Fin 28 → ℕ) (lower : frame+112 ≤ next) (room : next+7*D.candidates ≤ origin)
    (place : (privateLayout frame origin edges cells D.entries D.description gap).Image
      (readings before) D.entries (readings placed))
    (pointer : readings before (frame+92) = controlsBase origin edges cells D.entries (D.teams*D.sites))
    (words : ∀ j : Fin 28, readings before (controlsBase origin edges cells D.entries (D.teams*D.sites)+j.val) = values j) :
    let mem := readings (Directory.ISA.publish placed frame next (D.directory pp lp))
    mem (frame+92) = controlsBase origin edges cells D.entries (D.teams*D.sites) ∧
      ∀ j : Fin 28, mem (mem (frame+92)+j.val) = values j := by
  intro mem
  have p := (congrArg Fin.val (directoryPublished_low (D.directory pp lp) place (by omega : next ≤ origin)
    (frame+92) (by omega) (by omega))).trans pointer
  change mem (frame+92) = controlsBase origin edges cells D.entries (D.teams*D.sites) at p
  refine ⟨p,fun j => ?_⟩
  rw [p]
  have size := Nat.mul_le_mul_left 7 (D.directory_length_le pp lp)
  exact (congrArg Fin.val (directoryPublished_control (live := D.teams*D.sites) (D.directory pp lp) place lower
    (by omega) j.val)).trans (words j)

/-- The selected task allocator supplies the actual finite words referenced by the
geometry control emitter. -/
noncomputable def taskControlVector (task : SignedTaskArena.Layout) (bits : ℕ)
    (fits : ∀ i : Fin 28, task.controls i.val < 2^bits) (i : Fin 28) : Fin (2^bits) :=
  ⟨task.controls i.val,fits i⟩

/-- With the real geometry evaluator's terminal words, the published directory exposes
frame 92 and its two cell-bank operands at their original physical addresses. -/
theorem profile_cellBank_controls {S Z : Type*} [Fintype S] [Fintype Z] {s n d k b o : ℕ}
    (D : Directory.Layout) (pp lp : ℕ → ℕ × ℕ) (task : SignedTaskArena.Layout)
    (fits : ∀ i : Fin 28, task.controls i.val < 2^b)
    (F : CellAddressCircuit.Fields s edges n cells d k b (S ⊕ Bool)) (hk : k ≤ b)
    (old : Fin D.entries → Fin s) (ports : Fin (D.teams*D.sites) → Fin n)
    (rest : VerifierNetwork.Frame (S ⊕ Bool) (Outputs o b)) (source : VerifierNetwork.Frame Z S) (input : Z → Bool)
    (width : b ≤ W) (lower : frame+112 ≤ next) (room : next+7*D.candidates ≤ origin)
    (place : (privateLayout frame origin edges cells D.entries D.description gap).Image
      (readings before) D.entries (readings placed))
    (pointer : readings before (frame+92) = controlsBase origin edges cells D.entries (D.teams*D.sites))
    (out : ∀ i, readings before (origin+i.val) =
      value (fun j => (controlEmitter F hk old ports rest source (taskControlVector task b fits)).eval input (i,j))) :
    let mem := readings (Directory.ISA.publish placed frame next (D.directory pp lp))
    let addr := controlsBase origin edges cells D.entries (D.teams*D.sites)
    mem (frame+92) = addr ∧ mem (addr+9) = task.cube.cellBank ∧ mem (addr+10) = task.cube.cellStride := by
  intro mem addr
  have words := (profile_controls F hk old ports rest source (taskControlVector task b fits) input origin before width out).2.2
  obtain ⟨ptr,read⟩ := directoryPublished_controls D pp lp (fun i => task.controls i.val) lower room place pointer words
  change ∀ i : Fin 28, mem (mem (frame+92)+i.val) = _ at read
  change mem (frame+92) = addr at ptr
  rw [ptr] at read
  exact ⟨ptr,(read 9).trans task.consumer_words.2.2.1,(read 10).trans task.consumer_words.2.2.2.1⟩

end PackedHistoryCircuit

end BorderVNP
end Computability
end OAI
