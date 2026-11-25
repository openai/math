import OAI.Hierarchy.DescentIssuedSeedArchiveStart
import OAI.Hierarchy.DescentRegisterArchiveClaim
import OAI.Hierarchy.DescentNamedStartupArchiveTags

namespace OAI
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentLocalArchiveOrder DescentPrimitivePalette DescentSixParty.Chronology
open DescentInitialHost DescentCompiler DescentSixParty DescentSixParty.SeedNamed DescentColonies
open Chronology RegisterTimeline DescentRotor DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
open DescentExterior DescentGL DescentTerminalEpochChart DescentPackedEpochShelves DescentExteriorShelf
open DescentPackedProfileInstall Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
  {k cp p H e j r t w : ℕ} (X : Approximation F cp p) (radix : S.radix=2^k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
  (seed : Select X S.copies l.seedWidth → P) (lo C grain : ℕ) (ss : List (Source P)) (origin extra : ℕ)
  (ex : Fin e → Plane j r → Fin t → Bool) (z : P⊕Hidden e j r t → Bool) (back : Memory w)
local notation "G" => S.groupCount 0
local notation "digits" => S.initialDigits radix
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage issuedSeedArchiveClaim issuedSeedClaimAtFirst
local notation "hs" => (Fintype.equivFin (Vertex X)).toEmbedding.trans (Fin.castLEEmb publicWide)
local notation "top" => endAddress X l H G k
local notation "chart" => nodeChart l k H G
local notation "finish" => (chart).seedEnd top
local notation "lowEnd" => end_ (lo+extent grain ss) C grain
local notation "front" => origin+17*DescentExteriorShelf.span j r t e
local notation "raw" => Root.appended front extra (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z) back
local notation "counted" => DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) raw
local notation "flag" => DescentWideSeedFlags.endInput X S.copies l.seedWidth payload
local notation "entries" => DescentPackedSeed.rows X S.copies l.seedWidth payload
local notation "jobs" => DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload
local notation "lanes" => Primitive.paletteLanes D op l.seedWidth Z payload k
local notation "cap" => Primitive.initialEnd X S.copies l.seedWidth payload k H G lanes finish
local notation "done" => completeImage D op X digits publicWide l header payload Z counted
variable {q ε : ℝ} {wire : ℕ} {c : (initialGroup X S.copies l.seedWidth).Choice}
  (o : Origin X (s:=l.seedWidth) («G»:=D) (S:=S) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) c (S.initialDigits radix))
  (wide : Fintype.card o.raw.V ≤ H)


local notation "ports" => DatePorts.initial D op X S.copies l k H G payload Z
variable (menu : Runnable F op) (number : Local o.archive.bit) (register : DatePorts.RangeRoom (DatePorts.initial D op X S.copies l k H (S.groupCount 0) payload Z) o.source o.archive.bit)
  {a R : ℕ} (hp : 0<a) (units : 1≤R) (whole : a∣l.seedWidth)
local notation "shape_" => o.bundleShape a R hp units whole
local notation "label" => (Palette.originEncoding (p:=a) o op menu).atNode
local notation "names" => Reached.argumentPointer o.source o.archive.bit number shape_ hp
  (fun y : (Σ _ : Fin S.copies,Fin (Fintype.card (Port p X.width)))=>y.1.val) (ports).argumentsPerNode

local notation "pins" => Σ _ : Fin S.copies,Fin (Fintype.card (Port p X.width))
variable {epoch z' degree':ℕ} {targetWorld:MarkedWorld F 0 (Σ _ : Fin S.copies,Fin (Fintype.card (Port p X.width))) (fun _=>l.seedWidth*1)}
  (target:Reached targetWorld D q ε S k epoch z' degree' wire l.seedWidth) (path:Path o.source target)
local notation "trace" => (⟨(initial X S.copies l.seedWidth (S.groupCount 0) k digits).state c, targetWorld, Z, 3, z', degree', o.source, target, path⟩:
  RunTrace D q ε S k wire l.seedWidth epoch (fun _ : pins=>l.seedWidth*1) 0)
local notation "pos₀" => (⟨ports,cap⟩:RegisterTimeline.Position)
local notation "pinWidth" => (fun _ : pins=>by simpa only [Nat.mul_one] using whole)
open Lean Elab Term in
local elab "archivedHere" posTerm:term:arg memTerm:term:arg : term => do
  let posArg ← elabTerm posTerm none
  let memArg ← elabTerm memTerm none
  let mut expression := Lean.mkConst ``issuedSeedClaimAtFirst
  let mut formals := (← Lean.getConstInfo ``issuedSeedClaimAtFirst).type
  while let .forallE name dom rest kind := formals do
    let arg ← if name == `pos then pure posArg else if name == `mem then pure memArg
      else if kind.isInstImplicit then Lean.Meta.synthInstance dom else Lean.Meta.getFVarFromUserName name
    expression := Lean.mkApp expression arg
    formals := rest.instantiate1 arg
  return expression

open Lean Elab Term in
local elab "readFirstRegister" : term => do
  let mut expression := Lean.mkConst ``issued_startup_register
  let mut formals := (← Lean.getConstInfo ``issued_startup_register).type
  while let .forallE name dom rest kind := formals do
    let arg ← if kind.isInstImplicit then Lean.Meta.synthInstance dom else Lean.Meta.getFVarFromUserName name
    expression := Lean.mkApp expression arg
    formals := rest.instantiate1 arg
  return expression

include D op X radix l Z o wide menu number register hp units whole target path in
set_option maxHeartbeats 400000 in
theorem issued_startup_tagged {cw : ℕ} (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (live : 0 < lanes) (machine : payload ≤ w) (bits : DescentPrimitivePalette.printedBits D l.seedWidth Z op*lanes ≤ w)
    (fit : l.seedWidth < 2^cw) (decoded : decode X ((z∘Sum.inl)∘seed)=some c)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w) (fieldRoom : l.operandBits*l.operandLanes ≤ w)
    (seedFits : flag+(entries+1) < 2^w) (seedBefore : flag+(entries+1) ≤ lo)
    (shelves : lowEnd ≤ origin) (privateAfter : front+extra ≤ header) (early : header < l.base) (space : cap < 2^w)
    (sourceSpace : publicWords X+DescentDyadicSpan.span jobs≤finish)
    (wordRoom : 3<2^l.operandBits) (copies : S.copies≤2^l.operandBits) (quota : l.groupsPerNode≤2^l.operandBits)
    (pieces : l.groupsPerNode=l.seedWidth/a) :
    (ports).held o.source cap done ∧ archivedHere pos₀ done ∧ (ports).ArchiveTags done:=by
  have stored := readFirstRegister
  have storedTags:=issued_startup_tags D op X radix publicWide l header payload Z seed lo C grain ss
    origin extra ex z back fieldRoom early sourceSpace live machine space wordRoom
  refine ⟨stored.1, ?_, storedTags⟩
  unfold issuedSeedClaimAtFirst atFirstRegister
  exact stored.2

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
