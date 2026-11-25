import OAI.Hierarchy.DescentSeedProposalExecution
import OAI.Hierarchy.DescentSeedVenueTokenPhase

namespace OAI
/-! # One fixed initialization on the entire original proposal, including malformed data -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentInitialHost DescentCompiler DescentSixParty DescentSixParty.SeedNamed DescentColonies
open DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
open DescentExterior DescentGL DescentTerminalEpochChart DescentPackedEpochShelves DescentExteriorShelf
open DescentPackedProfileInstall Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
  {k cp p H e j r t w : ℕ} (X : Approximation F cp p) (radix : S.radix=2^k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
  (seed : Select X S.copies l.seedWidth → P) (lo C grain : ℕ) (ss : List (Source P)) (origin extra : ℕ)
  (ex : Fin e → Plane j r → Fin t → Bool) (z : P⊕Hidden e j r t → Bool) (back : Memory w)
local notation "g₀" => S.groupCount 0
local notation "digits" => S.initialDigits radix
set_option quotPrecheck false
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H g₀ k
local notation "chart" => nodeChart l k H g₀
local notation "finish" => (chart).seedEnd top
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "front" => origin+17*DescentExteriorShelf.span j r t e
local notation "raw" => Root.appended front extra (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z) back
local notation "flag" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H g₀ lanes finish
variable {q ε : ℝ} {wire z₀ : ℕ} {c : (initialGroup X S.copies l.seedWidth).Choice}
  (o : Origin X (s:=l.seedWidth) (G:=D) (S:=S) (q:=q) (fee:=ε) (z:=z₀) (wire:=wire) c (S.initialDigits radix))
  (wide : @Fintype.card o.raw.V o.raw.finite ≤ H)

local notation "selectedVenue" =>
  AtVenue (W := (DescentSixParty.SeedNamed.initial X S.copies l.seedWidth g₀ k digits).state c)
    (G:=D) (S:=S) (q:=q) (ε:=ε) (k:=k) (z:=z₀) (wire:=wire) (s:=l.seedWidth) (H:=H) (w:=w)
    (Origin.source (X:=X) (c:=c) («digits»:=digits) o)
    (source_hosts (c:=c) («digits»:=digits) X o wide) (operands X l k H g₀)

private theorem combine_execution_and_venue
    {execution hardware clear accepted exterior venue metadata frame : Prop}
    (issued : execution ∧ hardware ∧ clear ∧ accepted ∧ exterior ∧ frame)
    (held : venue ∧ metadata) :
    execution ∧ hardware ∧ clear ∧ accepted ∧ exterior ∧ venue ∧ metadata ∧ frame :=
  ⟨issued.1, issued.2.1, issued.2.2.1, issued.2.2.2.1, issued.2.2.2.2.1,
    held.1, held.2, issued.2.2.2.2.2⟩

private theorem observed_venue_pages {program zero venue pages frame : Prop}
    (issued : program ∧ zero ∧ venue ∧ pages ∧ frame) : venue ∧ pages :=
  ⟨issued.2.2.1, issued.2.2.2.1⟩

private theorem proposal_flag_below {flagBase rows lo_ shelfEnd origin_ exteriorSize more first : ℕ}
    (firstShelf : flagBase+(rows+1) ≤ lo_) (shelf : lo_ ≤ shelfEnd)
    (exterior : shelfEnd ≤ origin_) (late : origin_+exteriorSize+more ≤ first) : flagBase ≤ first :=
  (Nat.le_add_right flagBase (rows+1)).trans (firstShelf.trans
    (shelf.trans (exterior.trans ((Nat.le_add_right origin_ exteriorSize).trans
      ((Nat.le_add_right (origin_+exteriorSize) more).trans late)))))

include o wide in
set_option maxHeartbeats 1200000 in
private theorem reached_venue_pages (entry : Memory w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w)
    (fields : l.operandBits*l.operandLanes ≤ w) (early : header < l.base)
    (sourceSpace : publicWords X+DescentDyadicSpan.span jobs ≤ finish)
    (live : 0 < lanes) (machine : payload ≤ w) (space : cap < 2^w) :
    let finalMem : Memory w := completeImage D op X digits publicWide l header payload Z entry
    selectedVenue l.packedLanes l.fieldBits cap (roster X hs) finalMem ∧
    ∀(f : Fin 2) (x : Block k), Reads ((chart).seedBank top f x)
      ((chart).seedField (nodeArities X publicWide l) f) l.operandLanes finalMem := by
  exact observed_venue_pages (complete_after_count D op X digits publicWide l header payload Z
    (s:=l.seedWidth) (c:=c) (q:=q) (ε:=ε) (wire:=wire) (z₀:=z₀) o wide entry
    signed fields early sourceSpace live machine space)

include o wide in
set_option maxHeartbeats 1200000 in
theorem execute_complete (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (live : 0 < lanes) (machine : payload ≤ w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w) (fields : l.operandBits*l.operandLanes ≤ w)
    (seedFits : flag+(entries+1) < 2^w) (seedBefore : flag+(entries+1) ≤ lo)
    (shelves : lowEnd ≤ origin) (privateAfter : front+extra ≤ header) (early : header < l.base) (space : cap < 2^w) :
    let rawMem : Memory w := raw
    let entry : Memory w := DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) rawMem
    let finalMem : Memory w := completeImage D op X digits publicWide l header payload Z entry
    let cpu := completeProgram D op X publicWide l header payload Z radix (w:=w)
    cpu.Exec rawMem finalMem (4+(entries+1)*66+completeTicks (S:=S) (k:=k) D op X publicWide l payload Z w) ∧
    ProtocolRAM.CheapCode cpu ∧ finalMem header=0 ∧
    (finalMem (flag+entries)=0 ↔ valid X ((z∘Sum.inl)∘seed)) ∧
    Loaded origin (fun _=>LinearEquiv.refl _ _) ex (z∘Sum.inr) finalMem ∧
    selectedVenue l.packedLanes l.fieldBits cap (roster X hs) finalMem ∧
    (∀(f : Fin 2) (x : Block k), Reads ((chart).seedBank top f x)
      ((chart).seedField (nodeArities X publicWide l) f) l.operandLanes finalMem) ∧
    ∀a,a≠header → (a < flag ∨ flag+(entries+1) ≤ a) → (a < l.base ∨ cap ≤ a) → finalMem a=rawMem a := by
  intro rawMem entry finalMem cpu
  have flagBelow : flag ≤ header := proposal_flag_below seedBefore
    (profile_start_le_end lo C grain ss) shelves privateAfter
  have source := role_space_after_header X l (S:=S) (k:=k) (H:=H) header payload width flagBelow early
  apply combine_execution_and_venue
  · exact execute_proposal D op X radix publicWide l header payload Z seed lo C grain ss origin extra ex z back
      width live machine signed fields seedFits seedBefore shelves privateAfter early space
  · exact reached_venue_pages D op X radix publicWide l header payload Z o wide entry
      signed fields early source live machine space

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
