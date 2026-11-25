import OAI.Hierarchy.DescentTerminalMeterSuffix
import OAI.Hierarchy.DescentTerminalEmitterFrames
import OAI.Hierarchy.DescentTerminalFixedHeaders

namespace OAI
/-! # The final mask program reports the actual number of cable-assignment bits -/

namespace Hierarchy.DescentTerminalCompiledPrefix
open Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM DescentTerminalHeaderGroups
open DescentTerminalCableOrder DescentTerminalDenseHeaderRAM DescentTerminalEmitter
open scoped BigOperators
noncomputable section
set_option quotPrecheck false
variable {blocks bw q p geo sites : ℕ} {P : Type} [Fintype P] {bits : P→ℕ}
variable (S : Shape) (L : Layout) (F : DescentTerminalVertexFields.MaskedShelf blocks)
local notation "stage" => S.terminal.plane
local notation "banks" => L.emit.plane
local notation "widths" => (banks).header
local notation "entries" => (stage).headerRows
local notation "last_" => entries-1
def wholeAddress := L.emit.plane.header.whole.base+(S.terminal.plane.headerRows-1)
def tailAddress := L.emit.plane.header.rem.base+(S.terminal.plane.headerRows-1)

theorem emitted_mass (ev : Memory bw) (room : DescentTerminalEmitter.Room S.terminal L.emit bw) (hasRecord : 0<entries)
    (protectW : Later L.emit (wholeAddress S L)) (protectR : Later L.emit (tailAddress S L))
    (N : Network geo P bits) (home : N.Site→Fin sites) (old : N.Edge↪Fin (Fintype.card N.Edge))
    (ext : P↪ℕ) (node : N.Site↪ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v↪ℕ)
    (hq : 0<q) (hp : 0<p) (bound : ℕ) (all : ∀e,pairIndex N home e<bound)
    (space : (stream N home old ext node ops q hp bound).length≤entries)
    (read : Reads widths (padded (n:=entries) (stream N home old ext node ops q hp bound))
      (DescentTerminalDataPlane.file stage banks ev))
    (roomW : (∑e,N.width e)/(q*p)<2^bw) (roomR : (∑e,N.width e)%(q*p)<2^bw) :
    (DescentTerminalEmitter.result S.terminal L.emit ev (wholeAddress S L)).val=(∑e,N.width e)/(q*p) ∧
      (DescentTerminalEmitter.result S.terminal L.emit ev (tailAddress S L)).val=(∑e,N.width e)%(q*p) := by
  have h := native_headers_eof_fixed N home old ext node ops widths _ hq hp bound space room.plane.widths read
  have eofState := physical widths _ room.plane.widths h
  have sumEq:=beforePair_all N home bound all
  have a:=eofState.1.1
  have b:=eofState.1.2
  rw [sumEq] at a b
  rw [eof,ite_eq_right (Nat.ne_of_gt hasRecord)] at a b
  rw [after_plane _ _ _ room protectW,after_plane _ _ _ room protectR]
  exact ⟨(congrArg Fin.val a).trans (Fin.val_cast_of_lt roomW),
    (congrArg Fin.val b).trans (Fin.val_cast_of_lt roomR)⟩

theorem mask_mass (input : Memory bw) (room : Room S L bw) (hasRecord : 0<entries)
    (protectW : Later L.emit (wholeAddress S L)) (protectR : Later L.emit (tailAddress S L))
    (N : Network geo P bits) (home : N.Site→Fin sites) (old : N.Edge↪Fin (Fintype.card N.Edge))
    (ext : P↪ℕ) (node : N.Site↪ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v↪ℕ)
    (hq : 0<q) (hp : 0<p) (bound : ℕ) (all : ∀e,pairIndex N home e<bound)
    (space : (stream N home old ext node ops q hp bound).length≤entries)
    (read : Reads widths (padded (n:=entries) (stream N home old ext node ops q hp bound))
      (DescentTerminalDataPlane.file stage banks (maskEvents S L F input)))
    (roomW : (∑e,N.width e)/(q*p)<2^bw) (roomR : (∑e,N.width e)%(q*p)<2^bw) :
    (maskResult S L F input (wholeAddress S L)).val=(∑e,N.width e)/(q*p) ∧
      (maskResult S L F input (tailAddress S L)).val=(∑e,N.width e)%(q*p) :=
  emitted_mass S L _ room.emit hasRecord protectW protectR N home old ext node ops hq hp bound all space read roomW roomR

theorem suffix_mass (input : Memory bw) (room : Suffix.Fits S L F bw) (hasRecord : 0<entries)
    (protectW : Later L.emit (wholeAddress S L)) (protectR : Later L.emit (tailAddress S L))
    (N : Network geo P bits) (home : N.Site→Fin sites) (old : N.Edge↪Fin (Fintype.card N.Edge))
    (ext : P↪ℕ) (node : N.Site↪ℕ) (ops : ∀v,DescentKernelHistory.Boundary N v↪ℕ)
    (hq : 0<q) (hp : 0<p) (bound : ℕ) (all : ∀e,pairIndex N home e<bound)
    (space : (stream N home old ext node ops q hp bound).length≤entries)
    (read : Reads widths (padded (n:=entries) (stream N home old ext node ops q hp bound))
      (DescentTerminalDataPlane.file stage banks (Suffix.events S L F input)))
    (roomW : (∑e,N.width e)/(q*p)<2^bw) (roomR : (∑e,N.width e)%(q*p)<2^bw) :
    (Suffix.output S L F input (wholeAddress S L)).val=(∑e,N.width e)/(q*p) ∧
      (Suffix.output S L F input (tailAddress S L)).val=(∑e,N.width e)%(q*p) :=
  emitted_mass S L _ room.issuer hasRecord protectW protectR N home old ext node ops hq hp bound all space read roomW roomR

end
end Hierarchy.DescentTerminalCompiledPrefix

end OAI
