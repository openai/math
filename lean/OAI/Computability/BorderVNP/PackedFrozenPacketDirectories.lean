import OAI.Computability.BorderVNP.FragmentTaskPublishedRanks
import OAI.Computability.BorderVNP.PackedTerminalSignedGridEmitterCost
import OAI.Computability.BorderVNP.DiagonalSignedBundleBankRoom
import OAI.Computability.BorderVNP.PackedRetainedProfileImage

/-! # Fixed descriptor and original-bundle addresses of the signed geometry -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.History

open CellSparse Packet Packing.Inherited Packing.BankPacket Packing.Word FrozenTape LiveWords SiteWords

variable {a C cap d t : ℕ} {R B U V E Orig : Type}
variable (S : Schema R B) (L : Schema U V) (boxes : Fin a → List (Source.Box Orig))
variable (sh : ∀ r, (S.tags r).length≤cap) (lh : ∀ r, (L.tags r).length≤cap)
variable (priv : Fin (C+1) → E) (rep : Fin (C+1) → List (List E))

/-- The native descriptor range uses the static number of chunk labels.
Every possible geometry, field assignment and anchored row order has exactly
this many reference rows, including the real spare-cell reservations. -/
theorem directory_reference_count (args : E → ℕ) (x : Pins R B d → Bool) (y : Pins U V t → Bool)
    (cells : Fin a → Fin C) (off box : Fin a → ℕ)
    (ptr : Orig → (template S L boxes sh lh priv rep).Fields) :
    ((directory S L boxes sh lh priv rep args x y cells off box).referenceRows ptr).length =
      (template S L boxes sh lh priv rep).chunkLabels.length := by
  let T := template S L boxes sh lh priv rep
  let labels := cellOf S L x y cells
  let words := fun i => scalarArgs (cap := cap) S L x y off box ((roster a S L).get i)
  let G := T.directory labels args words
  have h := (T.chunkLabels_eval labels args words ptr).trans ((G.regroup_owners (anchor S L x y) ptr).symm)
  simpa only [directory,G,T,labels,words,List.length_map] using (congrArg List.length h).symm

end CellPacketGeometry.History

namespace PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

open CellPacketGeometry LiveWords RoutingISA.SignedTaskArena Packing.RoutingOutputs GeometryAdvice
open Retained

variable {E I Orig : Type} {slots cells : ℕ} (tpl : Template E I Orig slots (cells+1))
    (origin cables originals live bundleBits : ℕ)

/-- The fixed native directory of the two signed geometry sorts and both
appended bundle banks. The descriptor stream includes its spare receiver.
The 37 controls and the six-word bundle reader count the real receivers. -/
def frozenPacketDirectories : GeometryDirectories :=
  GeometryDirectories.published (packetBase origin cables cells originals live 37)
    tpl.publicDepth tpl.chunkDepth (cells+1) tpl.chunkLabels.length
    (controlsBase origin cables cells originals live) (Total tpl.publicDepth tpl.chunkDepth) bundleBits

local notation3 (prettyPrint := false) "dirs" => frozenPacketDirectories tpl origin cables originals live bundleBits
local notation "start" => packetBase origin cables cells originals live 37
local notation3 (prettyPrint := false) "ordinary" =>
  TerminalCells.signedGridOutputCount cables cells originals live 37 (Total tpl.publicDepth tpl.chunkDepth)

/-- All five bases are positions in the one fixed output of the signed
terminal. The two bundle arrays follow the ordinary emitter consecutively. -/
theorem frozenPacketDirectories_locations :
    (dirs).sorted=descriptorBank start tpl.publicDepth ∧ (dirs).padded=2^tpl.chunkDepth ∧
    (dirs).stops=cells+1+3*tpl.chunkLabels.length ∧ (dirs).bundlePayload=origin+ordinary ∧
    (dirs).bundleInverse=origin+ordinary+2^bundleBits := by
  refine ⟨rfl,rfl,rfl,?_,?_⟩ <;>
    dsimp only [frozenPacketDirectories,GeometryDirectories.published,TerminalCells.signedGridOutputCount,
      controlsBase,bases,count] <;> omega

/-- The raw ordinal of each of the two sort markers has the exact rank-bank
address consumed by the native task. The rank of a spare-cell marker is not
used by any of the real receivers. -/
theorem frozenPacketDirectories_markers (c : Fin cells) :
    let room := tpl.sort_rooms.2.1
    (dirs).sorted+(dirs).padded+c.val = descriptorBank start tpl.publicDepth+2^tpl.chunkDepth+
      (Markers.start room c.castSucc).val ∧
    (dirs).sorted+(dirs).padded+((dirs).stops+c.val)=descriptorBank start tpl.publicDepth+2^tpl.chunkDepth+
      (Markers.stop room c.castSucc).val ∧ (dirs).stops+cells≤(dirs).padded := by
  intro room
  obtain ⟨first,last,fit⟩ := GeometryDirectories.published_markers start tpl.publicDepth
    (controlsBase origin cables cells originals live) (Total tpl.publicDepth tpl.chunkDepth) bundleBits c.castSucc room
  exact ⟨first,last,(Nat.add_le_add_left (Nat.le_succ _) _).trans fit⟩

/-- A readback of the physical inverse permutation gives the two bounds used
by the task builder for every real cell. The start and exclusive stop in each
read use the spare-inclusive order of the actual descriptor sort. -/
theorem frozenPacketDirectories_of_inverse (mem : ℕ → ℕ)
    (rank : ∀ i : Fin (2^tpl.chunkDepth),
      mem (descriptorBank start tpl.publicDepth+(2^tpl.chunkDepth+i.val)) < 2^tpl.chunkDepth) :
    (dirs).MarkerBounds cells mem := by
  have h := tpl.sort_rooms.2.1
  rw [CellPacketGeometry.Schema.coords_length] at h
  have span : cells ≤ (dirs).stops ∧ (dirs).stops+cells ≤ (dirs).padded := by
    change cells ≤ cells+1+3*tpl.chunkLabels.length ∧ cells+1+3*tpl.chunkLabels.length+cells ≤ 2^tpl.chunkDepth
    omega
  refine ⟨span,fun c hc => ?_⟩
  let cell : Fin cells := ⟨c,hc⟩
  obtain ⟨a,b,_⟩ := frozenPacketDirectories_markers tpl origin cables originals live bundleBits cell
  change mem ((dirs).sorted+(dirs).padded+cell.val) < (dirs).padded ∧ mem ((dirs).sorted+(dirs).padded+((dirs).stops+cell.val)) < (dirs).padded
  have read (i : Fin (2^tpl.chunkDepth)) :
      mem (descriptorBank start tpl.publicDepth+2^tpl.chunkDepth+i.val) < 2^tpl.chunkDepth :=
    (congrArg mem (Nat.add_assoc (descriptorBank start tpl.publicDepth) (2^tpl.chunkDepth) i.val)).le.trans_lt (rank i)
  rw [a,b]
  exact ⟨read _,read _⟩

end PackedHistoryCircuit.Normalized.SelectedSchedule.SeedPlan

end BorderVNP
end Computability
end OAI
