import OAI.Hierarchy.DescentDatedSeedCompleteCode
import OAI.Hierarchy.DescentDatedSeedWideGrain
import OAI.Hierarchy.DescentWideSeedTokenInput

namespace OAI
/-! # Original profile grains after the complete native seed loader -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentSeedInitialTable DescentRotor DescentColonies DescentSIMDLookup
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExteriorShelf DescentExterior DescentTerminalFullPins Computability.BorderVNP.Crossing
open ThreeFlat Routing CorrectionBatch DescentGL DescentTerminalChipPins DescentTerminalPorts
open Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.Diagonal
open ThreeFlat.RAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F A : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
    {k cp p H w j r t K W q piece rows : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies ≃ Fin (S.groupCount 0)×Block k) (publicWide : Fintype.card (Vertex X)≤H)
    (l : Layout) (header payload Z : ℕ)
local notation "g₀" => S.groupCount 0
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "finish" => (chart).seedEnd top
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "flag" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload

private theorem lower_floor : l.base≤top ∧ top≤finish ∧ finish≤cap :=by
  have a:=fences X l H g₀ k
  have b:=Primitive.fences X S.copies l.seedWidth payload k H g₀ lanes finish
  exact ⟨a.1.trans (a.2.1.trans a.2.2),(Nat.le_add_right ..).trans (Nat.le_add_right ..),b.1.trans b.2⟩

/-- The data constructor, private budget initialization, node pages and role transposition
all preserve the original words strictly below the private budget header. -/
theorem complete_before_header (m : Memory w) (early : header<l.base)
    (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish) (live : 0<lanes) (native : payload≤w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w) (fields : l.operandBits*l.operandLanes≤w)
    (space : cap<2^w) (a : ℕ) (low : a<header) :
    completeImage D op X digits publicWide l header payload Z m a=m a :=by
  have f:=lower_floor (S:=S) (k:=k) (H:=H) D op X l payload Z
  have before : a<top:=(low.trans early).trans_le f.1
  have room : finish<2^w:=f.2.2.trans_lt space
  let built:=output X (Equiv.refl _) digits hs l m
  let cleared:=DescentPrivateHeader.initialized header built
  have role:=(Primitive.any X D op S.copies l.seedWidth Z payload k H g₀ lanes finish hs
    (afterCountImage X digits publicWide l header m) sourceSpace space native live).2.2 a
    (.inl (before.trans_le f.2.1))
  have node:=((chart).seedIssued top (nodeArities X publicWide l) cleared room).2.1 a (.inl before)
  exact role.trans (node.trans ((DescentPrivateHeader.initialized_frame header built a low.ne).trans
    (retain X (Equiv.refl _) digits hs l m signed fields (f.2.1.trans_lt room) a (.inl (low.trans early)))))

variable (seed : Select X S.copies l.seedWidth→A) (lo C grain : ℕ) (ss : List (Source A))
    (publicRows codes : ℕ)
local notation "E" => ExteriorCount X
local notation "origin" => end_ (lo+extent grain ss) C grain
local notation "front" => origin+17*DescentExteriorShelf.span j r t E
local notation "extra" => DescentTerminalPublicIdentity.total K W q piece codes rows publicRows
variable (outer : Catalyst.Port (2^(j+(j+r))*t*p)
    (CorrectionFrame.copiesWidth (2^(j+(j+r))*t) X.width) → Bool)
    (ballot : Candidate (A ⊕ Hidden (ExteriorCount X) j r t) K W q piece rows → Bool)
local notation "raw" => DescentTerminalFullPins.wideHeader X S.copies l.seedWidth payload w seed lo C grain ss publicRows codes outer ballot
local notation "votes" => ((ballot∘history)∘Sum.inl)
local notation "counted" => DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed votes raw
local notation "done" => completeImage D op X digits publicWide l header payload Z counted

/-- The entire shelf allocation ends before the private header and the complete seed floor. -/
theorem complete_shelf_room (privateAfter : front+extra≤header) (early : header<l.base) :
    lo+extent grain ss≤header ∧ header<cap :=by
  have f:=lower_floor (S:=S) (k:=k) (H:=H) D op X l payload Z
  have stop : lo+extent grain ss≤origin:=by dsimp only [end_,DescentPackedProfileInstall.dict];omega
  exact ⟨by omega,early.trans_le (f.1.trans (f.2.1.trans f.2.2))⟩

/-- The counted ballot and every seed-loader phase preserve the entire original shelf
interval, including the unused words in a power-of-two allocation. -/
theorem complete_shelf_frame (width : 16*digitsNeeded l.seedWidth≤payload)
    (live : 0<lanes) (native : payload≤w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w) (fields : l.operandBits*l.operandLanes≤w)
    (seedFits : flag+(entries+1)<2^w) (seedBefore : flag+(entries+1)≤lo)
    (privateAfter : front+extra≤header) (early : header<l.base) (space : cap<2^w)
    (a : ℕ) (lower : lo≤a) (upper : a<lo+extent grain ss) : done a=raw a :=by
  have f:=lower_floor (S:=S) (k:=k) (H:=H) D op X l payload Z
  have shore : lo+extent grain ss≤origin:=by dsimp only [end_,DescentPackedProfileInstall.dict];omega
  have below : a<header:=by omega
  have source:=(Root.counted_role_source X S.copies l.seedWidth payload w seed lo C grain ss origin
    (@DescentExterior.publicRows F cp p X j r t outer) (ballot∘history) raw (fun _ h=>Root.append_low _ _ _ _ h)
    width seedFits seedBefore le_rfl).1
  have input : publicWords X+DescentDyadicSpan.span jobs≤finish:=by omega
  have clear:=complete_before_header D op X digits publicWide l header payload Z counted early input
    live native signed fields space a below
  have outside : ¬(flag≤a ∧ a<flag+(entries+1)):=by omega
  exact clear.trans (ite_eq_right outside)

theorem complete_header_grain (width : 16*digitsNeeded l.seedWidth≤payload)
    (live : 0<lanes) (native : payload≤w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w) (fields : l.operandBits*l.operandLanes≤w)
    (seedFits : flag+(entries+1)<2^w) (seedBefore : flag+(entries+1)≤lo)
    (privateAfter : front+extra≤header) (early : header<l.base) (space : cap<2^w)
    (shelf : DescentPackedEpochShelves.Shelf A) (present : shelf∈shelves grain lo 0 ss) (idx : Fin (DescentPackedProfileTape.slots shelf.src.seats grain)) :
    done (shelf.base+idx.val)=((DescentPackedProfileTape.packed shelf.src.pin votes grain idx.val).val:Word w) :=by
  have placed_:=placed grain lo 0 ss shelf present
  have count:=DescentDyadicSpan.span_ge (DescentPackedProfileTape.slots shelf.src.seats grain)
  have pos:=idx.isLt
  dsimp only [DescentPackedEpochShelves.space] at placed_
  exact (complete_shelf_frame D op X digits publicWide l header payload Z seed lo C grain ss publicRows codes
    outer ballot width live native signed fields seedFits seedBefore privateAfter early space
    (shelf.base+idx.val) (by omega) (by omega)).trans
    (DescentTerminalFullPins.wide_header_grain X S.copies l.seedWidth payload w seed lo C grain ss
      publicRows codes outer ballot shelf present idx)

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
