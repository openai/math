import OAI.Hierarchy.DescentDatedSeedActualTokens
import OAI.Hierarchy.DescentSeedCompleteArchive

namespace OAI
/-! # The complete original two-plus-seven field archive after the real seed prelude -/
namespace Hierarchy.DescentDatedSeedStartup.Input
open DescentLocalArchiveOrder DescentPrimitivePalette DescentSixParty.Chronology
open DescentInitialHost DescentCompiler DescentSixParty DescentSixParty.SeedNamed DescentColonies
open DescentRotor DescentSeedRoot DescentPackedSeed DescentPackedColony DescentSIMDLookup DescentSeedInitialTable
open DescentExterior DescentGL DescentTerminalEpochChart DescentPackedEpochShelves DescentExteriorShelf
open DescentPackedProfileInstall Computability.VPVNP.BurstRAM PrivateRAM Catalyst Computability.BorderVNP.Crossing
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {S : AtomSchedule} (D : PoweredGadget F) (op : RotorSpec)
  {k cp p H e j r t w : ℕ} (X : Approximation F cp p) (radix : S.radix=2^k)
  (publicWide : Fintype.card (Vertex X) ≤ H) (l : Layout) (header payload Z : ℕ)
  (seed : Select X S.copies l.seedWidth → P) (lo C grain : ℕ) (ss : List (Source P)) (origin extra : ℕ)
  (ex : Fin e → Plane j r → Fin t → Bool) (z : P⊕Hidden e j r t → Bool) (back : Memory w)
variable {q ε : ℝ} {wire : ℕ} {c : (initialGroup X S.copies l.seedWidth).Choice}
  (o : Origin X (s:=l.seedWidth) (G:=D) (S:=S) (q:=q) (fee:=ε) (z:=Z) (wire:=wire) c (S.initialDigits radix))
  (wide : @Fintype.card o.raw.V o.raw.finite ≤ H)


open private DatePorts.originalGeometry DatePorts.OrderedSlotGeometry.ordering DatePorts.OrderedSlotGeometry.room
  from OAI.Hierarchy.DescentDatedSeedSlotGeometry
variable (menu : Runnable F op) (number : DatePorts.OrderedSlotGeometry.ordering (DatePorts.originalGeometry X (S.initialDigits radix) publicWide op l payload Z o))
  (register : DatePorts.OrderedSlotGeometry.room (DatePorts.originalGeometry X (S.initialDigits radix) publicWide op l payload Z o))
  {a R : ℕ} (hp : 0<a) (units : 1≤R) (whole : a∣l.seedWidth)
private structure ArchiveEvidence where
  statement : Prop
  checked : statement

variable {cw : ℕ} (width : 16*digitsNeeded l.seedWidth ≤ payload)
    (live : 0 < (Primitive.paletteLanes D op l.seedWidth Z payload k)) (machine : payload ≤ w) (bits : DescentPrimitivePalette.printedBits D l.seedWidth Z op*(Primitive.paletteLanes D op l.seedWidth Z payload k) ≤ w)
    (fit : l.seedWidth < 2^cw) (decoded : decode X ((z∘Sum.inl)∘seed)=some c)
    (signed : DescentSignedCableCodec.width 3 256*l.packedLanes ≤ w) (fieldRoom : l.operandBits*l.operandLanes ≤ w)
    (seedFits : (DescentWideSeedFlags.endInput X S.copies l.seedWidth payload)+((DescentPackedSeed.rows X S.copies l.seedWidth payload)+1) < 2^w) (seedBefore : (DescentWideSeedFlags.endInput X S.copies l.seedWidth payload)+((DescentPackedSeed.rows X S.copies l.seedWidth payload)+1) ≤ lo)
    (shelves : (end_ (lo+extent grain ss) C grain) ≤ origin) (privateAfter : (origin+17*DescentExteriorShelf.span j r t e)+extra ≤ header) (early : header < l.base) (space : (Primitive.initialEnd X S.copies l.seedWidth payload k H (S.groupCount 0) (Primitive.paletteLanes D op l.seedWidth Z payload k) (((nodeChart l k H (S.groupCount 0))).seedEnd (endAddress X l H (S.groupCount 0) k))) < 2^w)
    (sourceSpace : publicWords X+DescentDyadicSpan.span (DescentPackedSeed.Primitive.Source.jobs X S.copies l.seedWidth payload)≤(((nodeChart l k H (S.groupCount 0))).seedEnd (endAddress X l H (S.groupCount 0) k)))
    (wordRoom : 3<2^l.operandBits) (copies : S.copies≤2^l.operandBits) (quota : l.groupsPerNode≤2^l.operandBits)
    (pieces : l.groupsPerNode=l.seedWidth/a)
section
include D op X radix publicWide l header payload Z seed lo C grain ss origin extra ex z back o wide menu number register hp units whole width live machine bits fit decoded signed fieldRoom seedFits seedBefore shelves privateAfter early space sourceSpace wordRoom copies quota pieces
set_option maxHeartbeats 2500000
open Lean Elab Term Meta in
local elab "issuedArchiveRead" ds:term:arg mem:term:arg : term => do
  let chosenDigits ← elabTerm ds none
  let initialMemory ← elabTerm mem none
  -- Use the original dependent types for both the token reader and its archive consumer.
  let specialize : Lean.Name → Lean.Name → Option Lean.Expr → Lean.MetaM (Lean.Expr × Lean.Expr) := fun decl stop tokenRead => do
    let info ← Lean.getConstInfo decl
    let mut proof := Lean.mkConst info.name (info.levelParams.map Lean.Level.param)
    let mut result := info.type
    for _ in [:90] do
      let .forallE parameterName dom tail bi := result.consumeMData | break
      if parameterName == stop then break
      let actual ← if parameterName == `tokens then
        match tokenRead with
        | some h => pure h
        | none => throwError "expected the original token reader"
      else if parameterName == `digits then pure chosenDigits
      else if parameterName == `m then pure initialMemory
      else if bi.isInstImplicit then Lean.Meta.synthInstance dom else do
        let localName := match parameterName with
          | `G => `D
          | `choice => `c
          | `ord => `number
          | `ready => `register
          | `fields => `fieldRoom
          | `z₀ => `Z
          | name => name
        Lean.Meta.getFVarFromUserName localName
      proof := Lean.mkApp proof actual
      result := tail.instantiate1 actual
    return (proof, result)
  let (tokens, tokenType) ← specialize ``original_tokens `x none
  unless tokenType.isForall do throwError "expected the original token reader over blocks"
  let (paid, statement) ← specialize ``DatePorts.seed_archive .anonymous (some tokens)
  unless statement.consumeMData.getAppFn.isConst do
    throwError "expected the complete seed archive proposition"
  return Lean.mkApp2 (Lean.mkConst ``ArchiveEvidence.mk) statement paid

omit wide in
theorem issued_startup_archive :
    (issuedArchiveRead (S.initialDigits radix) (DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) (Root.appended (origin+17*DescentExteriorShelf.span j r t e) extra (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z) back))).statement :=
  (issuedArchiveRead (S.initialDigits radix) (DescentWideSeedFlags.countedAt X S.copies l.seedWidth payload seed (z∘Sum.inl) (Root.appended (origin+17*DescentExteriorShelf.span j r t e) extra (Root.widePackedImage X S.copies l.seedWidth payload w seed lo C grain ss origin ex z) back))).checked

end

end
end Hierarchy.DescentDatedSeedStartup.Input

end OAI
