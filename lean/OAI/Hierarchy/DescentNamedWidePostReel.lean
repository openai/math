import OAI.Hierarchy.DescentNamedWidePlacedSeed

namespace OAI
/-! The original selector fold and the actual routed 17-column source refer to the same late memory. -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice
open DescentTerminalEpochChart DescentTerminalEpochDecoder DescentSeedRoot Catalyst Computability.BorderVNP.Crossing
open DescentPackedEpochShelves DescentPackedEpochFold DescentPackedProfileTape DescentPackedProfileInstall
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ThreeFlat.RAM PhysicalProcedure
open DescentExterior DescentExteriorShelf DescentExteriorMatrixUpdate CorrectionBatch CatalystSubstitution
open DescentTerminalCompiledPrefix
open DescentTerminalVertexFields.MaskAllocation
open ThreeFlat Routing Diagonal
open Computability.VPVNP.RAMMemory (initialMemory)
open scoped Classical
open scoped Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b ≤ 2^S.capGain) (positive : 0 < p) (room : 10*(X.size+1) ≤ S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds ≤ 1/2)
attribute [local irreducible] Procedure.Exec ProtocolRAM.CheapCode Origin.source Branch.publicLayout Loaded
set_option maxHeartbeats 600000
set_option quotPrecheck false
local notation "rs" => (normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten).choose
local notation "ow" => inputOrder X G S ordinary reset branch positive room shorten
local notation "q" => S.firstWidth G.b p
variable (w payloadBits : ℕ) (fit : S.firstWidth G.b p < 2^w)
local notation "ch" => normalizedPackedChart X G S ordinary reset branch positive room shorten w fit
variable (z : (normalizedPackedChart X G S ordinary reset branch positive room shorten w fit).Pin→ Bool)
local notation "choice_" => (normalizedRoute X G S ordinary reset branch positive room shorten w fit).follow z
local notation "path_" => (SeedNamed.issued X G S ordinary reset branch positive room shorten choice_).path.selections

local notation "seedBase" => DescentWideSeedFlags.endInput X S.copies q payloadBits
local notation "seedRows" => DescentPackedSeed.rows X S.copies q payloadBits
local notation "seedAt" => seedBase+seedRows
local notation "initial" => DescentWideSeedFlags.initial X S.copies q payloadBits w (ch).seed z
local notation "seedCode" => DescentWideSeedFlags.check X S.copies q payloadBits w

local notation "chosen" => SeedNamed.issued X G S ordinary reset branch positive room shorten choice_
local notation "E" => Fintype.card (Port nP X.width)
variable {blocks ν bound : ℕ} (V : Home.Format) (U : Shape) (I : AddressPlan.Input)
    (R : DescentTerminalVertexFields.MaskAllocation.Channels blocks) (begin_ privateAt : ℕ)
    (short : ν*DescentTerminalVertexFields.span V.publicArity V.roles V.privateWords V.nodes V.addresses V.piece ≤ bound)
    (literal : DescentTerminalEmitter.Compact.Literals I.sources)
local notation "headBits" => U.terminal.plane.headBits
local notation "rest" => U.terminal.plane.restBits
local notation "laneCount" => U.terminal.plane.bitLanes
local notation "B" => S.groupWidth k tail 0+k
local notation "Port₀" => Catalyst.Port ((2^(headBits+(headBits+rest))*laneCount)*nP) (CorrectionFrame.copiesWidth (2^(headBits+(headBits+rest))*laneCount) X.width)
local notation "imageAt" => AddressPlan.afterMeter V U R begin_
local notation "origin" => AddressPlan.takeOff U I imageAt
local notation "sink" => AddressPlan.output V U I R begin_ privateAt short literal
local notation "suffix" => AddressPlan.clock V U I R begin_ privateAt short literal (bw:=w)
local notation "mix" => fun c=>Branch.publicLayout X G S
  (SeedNamed.issued X G S ordinary reset branch positive room shorten c) positive reset.base
variable (width : S.groupWidth k tail 0+k=U.terminal.plane.headBits+(U.terminal.plane.headBits+U.terminal.plane.restBits)) (outer : Catalyst.Port ((2^(U.terminal.plane.headBits+(U.terminal.plane.headBits+U.terminal.plane.restBits))*U.terminal.plane.bitLanes)*nP) (CorrectionFrame.copiesWidth (2^(U.terminal.plane.headBits+(U.terminal.plane.headBits+U.terminal.plane.restBits))*U.terminal.plane.bitLanes) X.width)→Bool) (guesses : Hidden (Fintype.card (Port nP X.width)) U.terminal.plane.headBits U.terminal.plane.restBits U.terminal.plane.bitLanes→Bool)
local notation "x" => DescentExterior.publicRows X outer
local notation "packed" => Sum.elim z guesses
local notation "survives" => (∃c,(ch).read z=some c)
local notation "compact" => fun (lo grain : ℕ)=>end_ (lo+extent grain (ch).layout) G.C grain
local notation "tape" => fun (lo grain : ℕ)=>Root.widePackedImage X S.copies q payloadBits w (ch).seed lo G.C grain (ch).layout (compact lo grain) x packed
local notation "frontSize" => fun (lo grain : ℕ)=>compact lo grain+17*span headBits rest laneCount E
local notation "raw" => fun (lo grain extra : ℕ) (back : Memory w)=>Root.appended (frontSize lo grain) extra (tape lo grain) back
local notation "work" => fun (lo grain extra : ℕ)=>frontSize lo grain+extra
theorem wide_post_reel (lo grain fence extra : ℕ) (back : Memory w) (count : ℕ→ℕ) (plan : Reel)
    (m : Memory w)
    (wideSeed : 2*digitsNeeded q ≤ payloadBits) (wide : 0 < w) (fitsSeed : seedBase+(seedRows+1) < 2^w)
    (topSeed : seedBase+(seedRows+1) ≤ lo) (positiveGrain : 0 < grain)
    (below : work lo grain extra ≤ fence)
    (before : finalAt (work lo grain extra) lo grain (ch).layout < origin)
    (low : ∀p∈shelves grain lo 0 (ch).layout,count p.ordinal < lo)
    (words : ∀s∈(ch).layout,slots s.seats grain*grain < 2^w)
    (fits : finalAt (work lo grain extra) lo grain (ch).layout+1 < 2^w)
    (geometry : plan.Room w B S.length fence origin)
    (top : origin+span headBits rest laneCount E+E < 2^w)
    (apart : end_ (lo+extent grain (ch).layout) G.C grain+32*span headBits rest laneCount E ≤ origin)
    (copySpace : origin+17*span headBits rest laneCount E < 2^w)
    (archive : ∀a,lo ≤ a→a < end_ (lo+extent grain (ch).layout) G.C grain→
      m a=DescentWideSeedFlags.countedAt X S.copies q payloadBits (ch).seed z (raw lo grain extra back) a)
    (exterior : ∀(col : Fin 17) (u : ℕ),u < span headBits rest laneCount E→
      m ((bank headBits rest laneCount E (compact lo grain) col.val).base+u)=DescentWideSeedFlags.countedAt X S.copies q payloadBits (ch).seed z (raw lo grain extra back) ((bank headBits rest laneCount E (compact lo grain) col.val).base+u))
    (issued : survives→(chosen).path.savedRotations plan fence tail m)
    : let copied:=relocated headBits rest laneCount E (compact lo grain) origin m
      let keep:=plan.result headBits rest laneCount E B S.length origin copied
      let dst:=finalAt (work lo grain extra) lo grain (ch).layout
      let o:=oldStateAt (work lo grain extra) lo G.C grain seedAt (ch).layout count z keep
      (survives → Loaded origin (Branch.publicLayout X G S chosen positive reset.base width) x guesses o) ∧
        (∀a,a<fence → a<work lo grain extra ∨ dst<a → o a=m a) := by
  intro copied keep dst o
  let start_:=raw lo grain extra back
  let page := compact lo grain
  let firstFree := work lo grain extra
  have loFit : lo ≤ page := by dsimp only [page, end_, dict]; omega
  have prior : page ≤ firstFree := by dsimp only [page,firstFree]; omega
  have seedLow : seedAt < lo := by omega
  have firstWord : ∀a < frontSize lo grain, start_ a=tape lo grain a :=
    fun a ha=>Root.append_low _ _ _ _ ha
  have checked := Root.wideCounted_on X S.copies q payloadBits w (ch).seed lo G.C grain
    (ch).layout page x packed start_ firstWord wideSeed fitsSeed topSeed le_rfl
  have copy := relocate_run (j:=headBits) (r:=rest) (t:=laneCount) (e:=E) page origin m apart copySpace
  have reel := plan.run (j:=headBits) (r:=rest) (t:=laneCount) (e:=E) B S.length fence origin copied geometry wide top
  have keep_word (a : ℕ) (ha : a < fence) : keep a=m a :=
    (reel.2.2 a ha).trans (copy.2.2.2 a (.inl (ha.trans_le (geometry.boot.trans geometry.startLow.le))))
  have active : Loaded origin (fun _=>LinearEquiv.refl _ _) x guesses copied := by
    have loaded := checked.2.2.2.1
    unfold Loaded at loaded ⊢
    intro col i hi
    exact (copy.2.2.1 col i hi).trans ((exterior col i hi).trans (loaded col i hi))
  have same := SeedNamed.uniform G _ _ X S.copies q w fit (S.initialDigits ordinary.radix) rs ow
  have archiveWords : ∀a,lo ≤ a → a < page →
      keep a=header lo G.C grain (ch).layout z initial a := by
    intro a ha hb
    have inFront : a < frontSize lo grain := by change a < page+_; omega
    exact (keep_word a (hb.trans_le (prior.trans below))).trans ((archive a ha hb).trans
      ((checked.2.2.2.2 a (.inr (by omega))).trans ((firstWord a inFront).trans
        (Root.widePacked_original X S.copies q payloadBits w (ch).seed lo G.C grain (ch).layout
          page x packed le_rfl hb))))
  have emitted : survives → Loaded origin (Branch.publicLayout X G S chosen positive reset.base width) x guesses o := by
    intro accepted
    have moved := (chosen).path.savedRotations_move plan fence (issued accepted)
      (fun a ha=>copy.2.2.2 a (.inl (ha.trans_le (geometry.boot.trans geometry.startLow.le))))
    have placed := Branch.reel_layout X G S chosen positive reset.base width origin fence plan copied x guesses
      active moved geometry
    unfold Loaded at placed ⊢
    intro col u hu
    have later : dst < (bank headBits rest laneCount E origin col.val).base+u := by
      change dst < origin+col.val*span headBits rest laneCount E+u
      exact before.trans_le ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
    exact (oldStateAt_frame ch z initial keep firstFree lo G.C grain seedAt count same positiveGrain seedLow
      low prior words fits archiveWords _ (.inr later)).trans (placed col u hu)
  have protect (a : ℕ) (ha : a < fence) (outside : a < firstFree ∨ dst < a) : o a=m a :=
    (oldStateAt_frame ch z initial keep firstFree lo G.C grain seedAt count same positiveGrain seedLow
      low prior words fits archiveWords a outside).trans (keep_word a ha)
  exact ⟨emitted,protect⟩

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
