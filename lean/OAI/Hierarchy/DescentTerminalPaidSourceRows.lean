import OAI.Hierarchy.DescentTerminalPaidCandidate
import OAI.Hierarchy.DescentTerminalEmittedChip
import OAI.Hierarchy.DescentTerminalEmitterAllocFrames

namespace OAI
/-! # Joined hidden and public streams at the chip's concrete physical raw bank -/
namespace Hierarchy.DescentTerminalCompiledPrefix.AddressPlan
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalVertexFields DescentTerminalRowArena
open DescentTerminalEmitter DescentTerminalDenseGraphRead DescentTerminalDenseWindow Computability.BorderVNP.Crossing
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {P : Type} [Fintype P] {bits : P → ℕ} {blocks K W q piece w : ℕ}
variable (S : DescentTerminalCompiledPrefix.Shape) (I : Input) (base : ℕ)
local notation "s" => S.terminal.plane
local notation "B" => q*(W*piece)
local notation "origin" => takeOff S I base
local notation "body" => bodyPlane S I base
local notation "E" => emitter S I base

/-- Every cell of the joined bank remains below both successive width scans
and the seven remaining output arenas. This includes the padding after the last public word. -/
theorem paid_source_frame (j : ℕ) (hj : j<(bodyPlane S I base).raw.size) :
    Later E ((bodyPlane S I base).raw.base+j) ∧ (bodyPlane S I base).raw.base+j<(bodyPlane S I base).header.rem.base := by
  let h := DescentTerminalDataPlane.Arena.headerBase s origin
  let a := DescentTerminalDataPlane.Arena.size S.terminal.plane.headerRows
  have lo : (bodyPlane S I base).raw.base+j<h := Nat.add_lt_add_left hj _
  constructor
  · apply Allocation.protected S.terminal I.indexEvents I.formatEvents _ (inputs S I base)
      body (publicHeader S I base) I.blank
    · change (bodyPlane S I base).raw.base+j<h+4*a+4*a
      omega
    · change (bodyPlane S I base).raw.base+j<(h+4*a)+0*a
      omega
  · change (bodyPlane S I base).raw.base+j<h+0*a
    omega

/-- A published stable public flight supplies the exterior words. The original
paid choice supplies the hidden words at its own mounted bank; all remaining
capacities and frames follow from the actual allocation. -/
theorem paid_sources (F : MaskedShelf blocks) (old : Earlier S I base F w)
    (z : DescentTerminalPaidBoot.Input K W q piece S.terminal.plane.rawRows → Bool)
    (codes front empty : ℕ) (m : Memory w) (ext : P ↪ ℕ) (outer : Ports bits)
    (alias_ : I.candidate = DescentTerminalPaidBoot.candidate K W q piece codes S.terminal.plane.rawRows front)
    (kept : ∀ j < DescentTerminalPaidBoot.total K W q piece codes S.terminal.plane.rawRows,
      m (front+j) = DescentTerminalPaidBoot.back z w codes j)
    (volume : (∑ a,bits a) ≤ S.terminal.plane.publicRows*B)
    (published : ∀ i : Fin S.terminal.plane.publicRows, DescentTerminalDataPlane.exteriorRows s body m ((bodyPlane S I base).output.base+i.val) =
      ((dense B (publicStream ext outer) i.val).val : Word w)) :
    SourceRows (W:=W) (q:=q) (piece:=piece) S.terminal E m ext (z ∘ Sum.inr) outer
      (DescentTerminalChipBootWords.chipBanks (K:=K) (W:=W) (q:=q) (p:=piece) codes E front empty) := by
  refine ⟨rfl,volume,?_,?_,?_,paid_hidden S I base F old z codes front m alias_ kept,published,
    paid_source_frame S I base⟩
  · have enough := DescentTerminalDataPlane.Arena.room (S.terminal.plane.rawRows+2+(S.terminal.plane.publicRows+2))
    exact (by omega : S.terminal.plane.rawRows+2+S.terminal.plane.publicRows ≤
      S.terminal.plane.rawRows+2+(S.terminal.plane.publicRows+2)).trans enough.le
  · change S.terminal.plane.rawRows≤I.candidate.size
    rw [alias_]
    exact DescentTerminalPaidBoot.candidate_size K W q piece codes S.terminal.plane.rawRows front
  · have enough := DescentTerminalDataPlane.Arena.room (S.terminal.plane.publicRows+2)
    change S.terminal.plane.publicRows≤DescentTerminalDataPlane.Arena.size (S.terminal.plane.publicRows+2)
    omega

end
end Hierarchy.DescentTerminalCompiledPrefix.AddressPlan

end OAI
