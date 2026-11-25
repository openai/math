import OAI.Hierarchy.DescentDatedSeedRetainedGrain

namespace OAI
/-! # The registered profile on the actual counted exterior ballot and terminal appendix -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentSixParty DescentCompiler DescentInitialHost DescentSeedRoot DescentPackedSeed
open DescentTerminalEpochChart DescentPackedEpochShelves DescentPackedProfileInstall
open DescentExteriorShelf DescentExterior DescentTerminalFullPins DescentGL Computability.BorderVNP.Crossing
open DescentPackedProfileTape Catalyst ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F A : Type} [Field F] {S : AtomSchedule} (G : PoweredGadget F) (op : RotorSpec)
    {k cp p H w e j r t : ℕ} (X : Approximation F cp p)
    (digits : Fin S.copies≃Fin (S.groupCount 0)×DescentColonies.Block k) (hosts : Fintype.card (Vertex X)≤H)
    (l : Layout) (header payload Z : ℕ)
local notation "top" => endAddress X l H (S.groupCount 0) k
local notation "finish" => (nodeChart l k H (S.groupCount 0)).seedEnd top
local notation "M" => Primitive.paletteLanes G op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H (S.groupCount 0) M finish
section GivenSource
variable (s : ℕ)
variable (seed : Select X S.copies s→A) (lo C pitch : ℕ) (ss : List (Source A))
    (origin extra : ℕ) (ex : Fin e→Plane j r→Fin t→Bool) (z : A⊕Hidden e j r t→Bool) (back : Memory w)
local notation "stop" => lo+extent pitch ss
local notation "lowEnd" => end_ stop C pitch
local notation "front" => origin+17*DescentExteriorShelf.span j r t e
local notation "flag" => DescentWideSeedFlags.endInput X S.copies s payload
local notation "rows_" => DescentPackedSeed.rows X S.copies s payload
local notation "pre" => Root.widePackedImage X S.copies s payload w seed lo C pitch ss origin ex z
local notation "raw" => Root.appended front extra pre back
local notation "votes" => (z∘Sum.inl)
local notation "checked" => DescentWideSeedFlags.countedAt X S.copies s payload seed votes raw
local notation "done" => completeImage G op X digits hosts l header payload Z checked

/-- Both the seed host and the funded-date reader read this same complete image.
The exterior assignment and terminal appendix are unrestricted. -/
theorem complete_appended_profile_after (width : 2*digitsNeeded s≤payload)
    (sourceSpace : publicWords X+DescentDyadicSpan.span
      (DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload)≤finish)
    (live : 0<M) (native : payload≤w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w) (fields : l.operandBits*l.operandLanes≤w)
    (seedBefore : flag+(rows_+1)≤lo) (placedEnd : lowEnd≤origin)
    (privateAfter : front+extra≤header) (early : header<l.base) (space : cap<2^w) :
    stop≤header ∧ header<cap ∧ ∀shelf∈shelves pitch lo 0 ss,∀i : Fin (slots shelf.src.seats pitch),
      done (shelf.base+i.val)=((packed shelf.src.pin votes pitch i.val).val:Word w) :=by
  have toDict : stop≤lowEnd:=by dsimp only [end_,dict];omega
  have first:=fences X l H (S.groupCount 0) k
  have last:=Primitive.fences X S.copies l.seedWidth payload k H (S.groupCount 0) M finish
  have baseBound : l.base≤top:=first.1.trans (first.2.1.trans first.2.2)
  have nodeEnd : top≤finish:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have finalBound : finish≤cap:=last.1.trans last.2
  have head : header<cap:=early.trans_le (baseBound.trans (nodeEnd.trans finalBound))
  have booked : stop≤header:=by omega
  have checkFit : flag+(rows_+1)<2^w:=by omega
  have rawBelow : ∀a<front,raw a=pre a:=fun _ ha=>Root.append_low _ _ _ _ ha
  have countedFrame:=(Root.wideCounted_on X S.copies s payload w seed lo C pitch ss origin ex z raw
    rawBelow width checkFit seedBefore placedEnd).2.2.2.2
  refine ⟨booked,head,?_⟩
  intro shelf listed i
  let a:=shelf.base+i.val
  have bank:=placed pitch lo 0 ss shelf listed
  have size:=DescentDyadicSpan.span_ge (slots shelf.src.seats pitch)
  have idx:=i.isLt
  dsimp only [DescentPackedEpochShelves.space] at bank
  have active : a<stop:=by dsimp [a];omega
  have low : lo≤a:=by dsimp [a];omega
  have seedRun:=complete_before_header G op X digits hosts l header payload Z checked early
    sourceSpace live native signed fields space a (active.trans_le booked)
  have checksum : checked a=raw a:=countedFrame _ (.inr (seedBefore.trans low))
  have exterior:=Root.widePacked_original X S.copies s payload w seed lo C pitch ss origin ex z
    placedEnd (active.trans_le toDict)
  let tape:=DescentWideSeedFlags.initial X S.copies s payload w seed votes
  have original:=DescentPackedProfileInstall.before stop C pitch (rawTape pitch votes lo ss tape) active
  exact seedRun.trans (checksum.trans ((rawBelow _ (by omega)).trans (exterior.trans (original.trans
    ((raw_reads pitch lo 0 votes ss shelf listed tape).1 i)))))

end GivenSource

variable (seed : Select X S.copies l.seedWidth→A) (lo C pitch : ℕ) (ss : List (Source A))
    (origin extra : ℕ) (ex : Fin e→Plane j r→Fin t→Bool) (z : A⊕Hidden e j r t→Bool) (back : Memory w)
local notation "stop" => lo+extent pitch ss
local notation "lowEnd" => end_ stop C pitch
local notation "front" => origin+17*DescentExteriorShelf.span j r t e
local notation "flag" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "rows_" => DescentPackedSeed.rows X S.copies l.seedWidth payload
local notation "pre" => Root.widePackedImage X S.copies l.seedWidth payload w seed lo C pitch ss origin ex z
local notation "raw" => Root.appended front extra pre back
local notation "votes" => (z∘Sum.inl)
local notation "checked" => DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed votes raw
local notation "done" => completeImage G op X digits hosts l header payload Z checked

/-- On the selected layout, the actual primitive seed source fits below the checked ballot header. -/
theorem complete_appended_profile (width : 16*digitsNeeded l.seedWidth≤payload)
    (live : 0<M) (native : payload≤w)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes≤w) (fields : l.operandBits*l.operandLanes≤w)
    (seedBefore : flag+(rows_+1)≤lo) (placedEnd : lowEnd≤origin)
    (privateAfter : front+extra≤header) (early : header<l.base) (space : cap<2^w) :
    stop≤header ∧ header<cap ∧ ∀s∈shelves pitch lo 0 ss,∀i : Fin (slots s.src.seats pitch),
      done (s.base+i.val)=((packed s.src.pin votes pitch i.val).val:Word w) :=by
  have toDict : stop≤lowEnd:=by dsimp only [end_,dict];omega
  have fc:=fences X l H (S.groupCount 0) k
  have end_ : l.base≤finish:=(fc.1.trans (fc.2.1.trans fc.2.2)).trans
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have last:=Primitive.fences X S.copies l.seedWidth payload k H (S.groupCount 0) M finish
  have seedFits : flag+(rows_+1)<2^w:=by have roof:=end_.trans (last.1.trans last.2);omega
  have source:=(Root.counted_role_source X S.copies l.seedWidth payload w seed lo C pitch ss
    origin ex z raw (fun _ ha=>Root.append_low _ _ _ _ ha) width seedFits seedBefore placedEnd).1
  exact complete_appended_profile_after G op X digits hosts l header payload Z l.seedWidth seed lo C pitch
    ss origin extra ex z back (by omega) (source.trans (by omega)) live native signed fields
    seedBefore placedEnd privateAfter early space

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
