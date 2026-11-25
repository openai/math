import OAI.Hierarchy.DescentOriginalSectorRetention
import OAI.Hierarchy.DescentResetStemOriginalSlots
import OAI.Hierarchy.DescentResetPublicParentPosted
import OAI.Hierarchy.DescentPhysicalRankSheetIntake
import OAI.Hierarchy.DescentPhysicalMixedSectors

namespace OAI
/-! # All four chronological word sectors at the single reached ranking input -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM DescentDatedAddressBook DescentCompiler DescentColonies DescentDenseHostOrder DescentResetLocalRoster
open DescentPackedPrivateMenu DescentResetPeerUnionRAM DescentPackedColony DescentSIMDLookup
open DescentGroupPeerOrder DescentSortedRoster DescentContactOutputShape DescentPacking.PackedMatch.Local.Stage
open ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist : ℕ}
  {input : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
set_option hygiene false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "A" => input.placement
local notation "H" => S.hostSize i
local notation "J" => 2^(T).commonDepth
local notation "r" => (Z).k-(T).commonDepth
local notation "ht" => GroupStage.depthBound D n f g
local notation "shelf" => (DescentDenseHostOrder.roster (Z).graph r ht).card
local notation "gs" => S.groupCount (i+1)
local notation "cap₀" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(ht+1))
local notation "oldWidth" => DescentPackedPrivateMenu.fieldBits (Z).graph r ht (2^r*(2*(A).cap))
    (DescentRecordedRotorLayers.width f (A).cap) C (Z).width
variable (oldBatch batch : ℕ) (calendar : List ℕ) (paid : (A).cap=(calendar.take i).prod*256)
local notation "cap" => (calendar.take i).prod*256
local notation "field₀" => ResetMiddle.fieldWidth D cap n k ht
local notation "table₀" => CandidateSheets.fromBoard S ctl.board k tail i D f g cap batch
local notation "meta₀" => (table₀).metaBits
local notation "month" => CandidateFront.menu S ctl.board k tail i D f g oldBatch batch C ctl.bitsR calendar
local notation "good" => contactOutputs B H oldBatch field₀ (Nat.clog 2 (D+2)) (Nat.clog 2 (D+3)) gs (2^k)
    batch (month).contact.outputBits meta₀
local notation "deck" => privateProjection («H»:=H) (field:=oldWidth) B oldBatch batch meta₀
variable {date : PhysicalReset} {floor bw : ℕ} (I : date.DateInputs floor bw)
local notation "v₀" => date.successor
local notation "base₀" => date.rebased floor
local notation "phys₀" => (v₀).front
local notation "peer₀" => (phys₀).peer
local notation "pitch₀" => (phys₀).contactLayout ((v₀).actorEnd base₀)
local notation "Q₀" => (v₀).privateShape
local notation "K₀" => (v₀).contactShape
local notation "don₀" => (phys₀).donorStart ((v₀).actorEnd base₀)
local notation "used" => Fintype.card B.next.V
local notation "rawSize" => H*shelf
local notation "L" => 2^(S.groupWidth k tail i+k-(T).commonDepth)
local notation "K" => 2*(A).cap
local notation "F₀" => DescentOldContactSender.count (A).degree L (A).cap (Z).n r
variable (cal : MixedGeometry B oldBatch batch calendar v₀ base₀) (pad : Fintype.card input.V≤H)
local notation "portChart" => input.vertex.trans (Fin.castLEEmb pad)
local notation "adj_" => hostRotor portChart (hostRoster (A) ((portChart).trans Fin.valEmbedding))
variable {keyBits : ℕ} (prior : PriorPeerWords B H oldWidth keyBits)
    (xs : Fin H→Fin J→Fin F₀→Cell field₀) (raw : Fin L→Fin K→Fin H→Fin J→Cell field₀)
    (near : Fin rawSize→Fin 3→Option (Fin rawSize))

open DescentResetRankedWindows DescentResetCandidatePair DescentPackedZip DescentResetFieldAssembler
local notation "s₀" => (v₀).sheets
variable (bound : used≤(s₀).hosts) (geo : PhysicalReset.DateInputs.SheetGeometry I)
local notation "dense₀" => ((Z).denseHostRank T ((B.frame.host.symm.toEmbedding.trans input.vertex).trans
    (Fin.castLEEmb pad))).trans (Fin.castLEEmb bound)
local notation "rack₀" => rackOf B dense₀
local notation "gx" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "bx" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation "cx" => geo.contacts.trans (congrArg DescentContactOutputShape.Shape.sockets cal.contactDeck)
local notation "px" => geo.privates.trans (congrArg DescentPrivateMaskDeck.Shape.keys cal.privateDeck)
local notation "pos" => CandidateSheet.index (stemsCount B) (contactCount B) (privateCount B)
local notation "meter" => DescentResetFieldAssembler.raw (s₀).metaBits


open DescentResetOriginalSlots
local notation "sx" => (v₀).sheets
local notation "area" => ((v₀).remap base₀).endAddress
local notation "o" => (sx).original area
local notation "blk" => 2^k
local notation "gt" => S.groupCount (i+1)
local notation "units" => originalBits D k n ht (A).cap (programCount ctl.board ht) g
local notation "T₀" => I.numbered.stemSide area
local notation "P₀" => I.numbered.publicSide area
local notation "D₀" => I.numbered.privateSide area
local notation "packed" x:arg j:arg => (.lookup (bank o (sx).rows (sx).candidates x j) .row:Expr)
local notation "start" m:arg => I.masked.image (I.privateResult m)
local notation "Pout" m:arg => (P₀).dst (I.numbered.prefixOutput area (start m))
local notation "Tout" m:arg => (T₀).image (Pout m)

private theorem shaped_number {X X' s s' c c' p p' : ℕ} (hx:X=X') (hs:s=s') (hc:c=c') (hp:p=p')
    (src : ℕ→ℕ→Expr) (x : Fin X') (j : CandidateSheet.Sector s' c' p') :
    shaped hx hs hc hp (fun v a=>src v.val ((CandidateSheet.index s c p) a).val) x j=
      src x.val ((CandidateSheet.index s' c' p') j).val:=by
  subst X';subst s';subst c';subst p';rfl

private theorem measured_groups {w hostsCount a n n' M : ℕ} {m : Computability.VPVNP.BurstRAM.Memory w} {e : Expr}
    (group : n=n') (v : Fin hostsCount→Fin n'→Cell a) (seen : Source e (fun h g=>v h (g.cast group)) M m) :
    Source e v M m:=by subst n';exact seen

variable (hx : (v₀).receiver.blocks=blk) (hs : I.sectors.stems=stemsCount B)
    (hc : I.sectors.contacts=contactCount B) (hp : I.sectors.privates=privateCount B)
local notation "groupAt" => congrArg DescentPrivateMaskDeck.Shape.groups cal.privateDeck
local notation "blockAt" => congrArg DescentPrivateMaskDeck.Shape.blocks cal.privateDeck
local notation "values" x:arg j:arg => (fun v g₀=>(actualParentNumber B rack₀ x j v g₀:Cell units))
local notation "word" x:arg j:arg => (fun v (gr:Fin (sx).groups)=>(actualParentNumber B rack₀ x j v (gr.cast groupAt):Cell units))
local notation "reg" x:arg j:arg => shaped hx hs hc hp I.sectors.original x j

/-- Every later write is executed. In particular, a trunk and a contact are
read back through both the stem and private passes. -/
theorem reached_original_words (ok : I.Ready) (m : Computability.VPVNP.BurstRAM.Memory bw)
    (nStem : I.numbered.stems=stemsCount B)
    (stemAt : ∀j,(I.numbered.stemShelf j).val=j.val)
    (publicAt : ∀j,(I.numbered.publicShelf j).val=stemsCount B+j.val)
    (privateAt : ∀j,(I.numbered.privateShelf j).val=stemsCount B+1+contactCount B+j.val)
    (stem : ∀(x:Fin blk) (j:Fin (stemsCount B)),
      Source (packed x.val (I.numbered.stemShelf (j.cast nStem.symm)).val)
        (word x (pos (.inl j))) (sx).lanes (Tout m))
    (trunk : ∀x:Fin blk,Source (packed x.val (I.numbered.publicShelf 0).val)
      (word x (pos (.inr (.inl 0)))) (sx).lanes (Pout m))
    (contact : ∀(x:Fin blk) (j:Fin (contactCount B)),
      Source (packed x.val (I.numbered.publicShelf (j.cast hc.symm).succ).val)
        (word x (pos (.inr (.inr (.inl j))))) (sx).lanes (Pout m))
    (privateRows : ∀(x:Fin blk) (j:Fin (privateCount B)),
      Source (packed x.val (I.numbered.privateShelf (j.cast hp.symm)).val)
        (word x (pos (.inr (.inr (.inr j))))) (sx).lanes
        ((D₀).dst (DescentUniformSlotOperands.result ((sx).stemFormatEnd area) (sx).privates
          (sx).hosts (sx).groups (sx).lanes (sx).argBits (Tout m)))) :
    ∀x j,Source (reg x j) (values x (pos j)) (sx).lanes (I.sheetsEntry ok m):=by
  intro x j
  have code : reg x j=packed x.val (pos j).val:=
    shaped_number hx hs hc hp (fun x q=>packed x q) x j
  have groups : (sx).groups=gt:=groupAt
  have entryMem : I.sheetsEntry ok m = I.numbered.output area (start m) := rfl
  rw [code,entryMem]
  apply measured_groups groups
  change Source (packed x.val (pos j).val) (word x (pos j)) (sx).lanes (I.numbered.output area (start m))
  have transport {a b : ℕ} {values₀ : Fin (sx).hosts → Fin (sx).groups → Cell units} (same : a = b)
      (read : Source (packed x.val a) values₀ (sx).lanes (I.numbered.output area (start m))) :
      Source (packed x.val b) values₀ (sx).lanes (I.numbered.output area (start m)) := same ▸ read
  have before (a : Fin I.numbered.stems) (b : Fin ((sx).contacts+1)) :
      I.numbered.stemShelf a≠I.numbered.publicShelf b:=by
    intro bad
    have n:=congrArg Fin.val bad
    rw [stemAt,publicAt] at n
    have bounds:=a.isLt
    omega
  have after (a : Fin (sx).privates) (b : Fin ((sx).contacts+1)) :
      I.numbered.privateShelf a≠I.numbered.publicShelf b:=by
    intro bad
    have n:=congrArg Fin.val bad
    rw [privateAt,publicAt] at n
    have lt:b.val<contactCount B+1:=by
      have counts : (sx).contacts = contactCount B := hc
      exact b.isLt.trans_le (Nat.add_le_add_right counts.le 1)
    omega
  rcases j with j|j
  · have separate (t : Fin (sx).privates) : I.numbered.privateShelf t≠I.numbered.stemShelf (j.cast nStem.symm):=by
      intro h
      have z:=congrArg Fin.val h
      rw [privateAt,stemAt] at z
      have h₀:=j.isLt
      change _=j.val at z
      omega
    have seen:=I.numbered.return_stem area (start m) ok.numbers (x.cast (blockAt).symm) (j.cast nStem.symm)
      (word x (pos (.inl j))) separate (stem x j)
    exact transport ((stemAt _).trans (CandidateSheet.stem_val j).symm) seen
  rcases j with j|j
  · have z:j=0:=Subsingleton.elim _ _
    subst j
    have seen:=I.numbered.return_public area (start m) ok.numbers (x.cast (blockAt).symm) 0
      (word x (pos (.inr (.inl 0)))) (fun a=>before a _) (fun a=>after a _) (trunk x)
    exact transport (by rw [publicAt, CandidateSheet.trunk_val]; exact Nat.add_zero _) seen
  rcases j with j|j
  · have seen:=I.numbered.return_public area (start m) ok.numbers (x.cast (blockAt).symm) (j.cast hc.symm).succ
      (word x (pos (.inr (.inr (.inl j))))) (fun a=>before a _) (fun a=>after a _) (contact x j)
    have coord : (I.numbered.publicShelf (j.cast hc.symm).succ).val = (pos (.inr (.inr (.inl j)))).val := calc
      _ = stemsCount B + (j.cast hc.symm).succ.val := publicAt _
      _ = stemsCount B + 1 + j.val := by change stemsCount B + (j.val + 1) = _; omega
      _ = _ := (CandidateSheet.contact_val j).symm
    exact transport coord seen
  · exact transport (by rw [privateAt, CandidateSheet.private_val]; rfl) (privateRows x j)

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
