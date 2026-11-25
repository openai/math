import OAI.Hierarchy.DescentTerminalInitialGrains
import OAI.Hierarchy.DescentWideFullPins

namespace OAI
/-! # Physical profile shelf entries in the short-dictionary full header -/
namespace Hierarchy.DescentTerminalFullPins
open DescentInitialHost DescentPackedProfileInstall DescentGL Computability.BorderVNP.Crossing
open ThreeFlat Routing Diagonal CorrectionBatch
open DescentTerminalChipPins DescentTerminalPorts DescentExteriorShelf DescentExterior
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentPackedProfileTape DescentPackedEpochFold
open DescentTerminalEpochHeader DescentPackedEpochShelves DescentSeedRoot DescentCompiler Catalyst CatalystSubstitution
open ThreeFlat.Diagonal Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F A : Type} [Field F] {cp data j r t K W q piece rows : ℕ}
variable (X : Approximation F cp data)
local notation "E" => ExteriorCount X

variable (R s payload w : ℕ) (seed : Select X R s→A) (lo C grain : ℕ) (ss : List (Source A))
local notation "lastWord" => end_ (lo+extent grain ss) C grain
local notation "front" => lastWord+17*span j r t E
variable (publicRows codes : ℕ)

open DescentPackedProfileTape
variable (outer : Catalyst.Port (2^(j+(j+r))*t*data)
    (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width) → Bool)
    (z : Candidate (A ⊕ Hidden (ExteriorCount X) j r t) K W q piece rows → Bool)
local notation "raw" => DescentTerminalFullPins.wideHeader X R s payload w seed lo C grain ss publicRows codes outer z
local notation "votes" => ((z∘history)∘Sum.inl)

/-- The original bit tape has the requested field at its original shelf address,
before the selector-count checksum or any subsequent date has run. -/
theorem wide_header_grain (shelf : DescentPackedEpochShelves.Shelf A) (present : shelf∈shelves grain lo 0 ss)
    (i : Fin (slots shelf.src.seats grain)) :
    raw (shelf.base+i.val)=((packed shelf.src.pin votes grain i.val).val:Word w) := by
  let seedMem:=DescentWideSeedFlags.initial X R s payload w seed votes
  let x := @DescentExterior.publicRows F cp data X j r t outer
  have bounds:=shelf_bounds (lo:=lo) (C:=C) (grain:=grain) (ss:=ss) shelf present i
  have whereAt:=placed grain lo 0 ss shelf present
  have extent_:=DescentDyadicSpan.span_ge (slots shelf.src.seats grain)
  have idx:=i.isLt
  dsimp only [space] at whereAt
  have early : shelf.base+i.val<lo+extent grain ss:=by omega
  have before_:=DescentPackedProfileInstall.before (lo+extent grain ss) C grain (rawTape grain votes lo ss seedMem) early
  have word:=(raw_reads grain lo 0 votes ss shelf present seedMem).1 i
  unfold DescentTerminalFullPins.wideHeader
  rw [Root.append_low _ _ _ _ (show shelf.base+i.val<front by omega),
    Root.widePacked_original X R s payload w seed lo C grain ss lastWord x (z∘history) le_rfl bounds.2]
  exact before_.trans word

end
end Hierarchy.DescentTerminalFullPins

end OAI
