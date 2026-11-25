import OAI.Hierarchy.DescentPrimitiveView
import OAI.Hierarchy.DescentPrimitivePaletteCounts
import OAI.Hierarchy.DescentPrimitiveRolePrice
import OAI.Hierarchy.DescentOccurrenceAllowance
import OAI.Hierarchy.DescentNormalizedBundle
import OAI.Hierarchy.DescentArchivePalette

namespace OAI
/-! # Branch-independent primitive keys at the true terminal position -/
namespace Hierarchy.DescentPrimitivePalette
open DescentKernelHistory DescentSixParty DescentCompiler DescentInitialHost DescentMixedRouter
open DescentResetInvoice DescentBundleHistory Catalyst Computability.BorderVNP.Crossing
open DescentRotor DescentResetGates DescentEpochTagKeys
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]


variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
local notation "cert" => normalized_epochs_issued_joint X G S ordinary reset branch positive room shorten
local notation "s" => S.firstWidth G.b p
local notation "Z" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "leaf" => normalizedIssuedRows X G S ordinary reset branch positive room shorten
local notation "menu" => dictionary («s»:=s) («Z»:=Z) G rot reset.menu p

def atLeaf (c : (Epochs.finish G _ _ (cert).choose).Choice) :
    Encoding (Label G s Z rot) menu (NativeBranch.archive X G S (leaf c) positive).bit :=
  encodePath rot reset.menu (leaf c).path positive _ (normalizedIssuedRotor X G S ordinary reset branch positive room shorten c)
    (Chronology.seedArchive X S.copies s _) (seeded rot reset.menu X _)

theorem readLeaf (c : (Epochs.finish G _ _ (cert).choose).Choice) (tag : (NativeBranch.archive X G S (leaf c) positive).bit.Tag) :
    indexed (p:=p) rot reset.menu ((codec (G:=G) rot).store ((atLeaf X G S ordinary reset branch positive room shorten c).code tag))=
      (NativeBranch.archive X G S (leaf c) positive).bit.scalar tag :=
  indexed_read rot reset.menu _ _

def leafShape (c : (Epochs.finish G _ _ (cert).choose).Choice) :
    WorldShape p (max 1 (max reset.bitsR (C*reset.bitsR)))
      ((atLeaf X G S ordinary reset branch positive room shorten c).view menu) :=
  Encoding.viewShape menu _ (normalizedIssuedShape X G S ordinary reset branch positive room shorten c)

def freshCode {T : ℕ} (op : RotorSpec) (z : Fin (T+1)) (a : Profile G.C) (role : Fin 6) :
    Fin (colors G s T op) :=
  (codec (G:=G) op).store (Sum.inr (Sum.inl (z,a,role)))

theorem freshCode_val {T : ℕ} (op : RotorSpec) (z : Fin (T+1)) (a : Profile G.C) (role : Fin 6) :
    (freshCode G S (p:=p) op z a role).val=censusCount s+((gadget T G.C).store (z,a,role)).val := rfl

end
end Hierarchy.DescentPrimitivePalette

end OAI
