import OAI.Hierarchy.DescentSeedHeaderLayout
import OAI.Hierarchy.DescentChosenExteriorHeadWidths
import OAI.Hierarchy.DescentTerminalNativeLimits
import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentBundleTagKeys
import OAI.Hierarchy.DescentTerminalScalarHeader

namespace OAI
/-! # The original cut supplies its actual appendix and initial circuit -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentPrimitivePalette
open DescentTerminalEpochChart DescentDatedSeedStartup Catalyst
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (op : RotorSpec) (drift : ℕ)

def headArity (S : AtomSchedule) :=2^(headChunk G S)*(G.b^(S.rounds*S.height)*G.b)

def chosenSeedAppendix (S : AtomSchedule) (k h bins raw : ℕ) : SeedHeader.Appendix :=
  let W:=NativeBranch.binLimit (k:=k) S
  let q:=headArity G S
  let piece:=h/(16*(q*W))
  let p:=W*piece
  let cap:=NativeBranch.privateSlotCapacity G S drift
  let tags:=DescentBundleTagKeys.capacity (colors G (S.firstWidth G.b p) (S.grainAt G.b p 0) op)
    (max 8 (2^S.capGain)) cap p drift
  let codes:=DescentTerminalScalarHeader.range q tags cap (S.epochPower^S.localTokenExponent) cap p
    (S.groupCount S.length*2^k)
  {bins:=bins,binWidth:=W,arity:=q,piece:=piece,codes:=codes,raw:=raw}

def originalSeedHead {cp pins : ℕ} (X : Approximation F cp pins) {A : Type} (steps : List (Source A))
    (S : AtomSchedule) (k tail h hosts degree wire hist bins raw : ℕ) : SeedHeader.Input F where
  arity:=cp
  pins:=pins
  circuit:=X
  labels:=A
  steps:=steps
  appendix:=chosenSeedAppendix G op drift S k h bins raw
  schedule:=S
  k:=k
  tail:=tail
  p:=headGrain G S k h
  degree:=degree
  wire:=wire
  hist:=hist
  hosts:=hosts
  j:=headChunk G S
  rest:=headRest G S k tail

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
