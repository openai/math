import OAI.Hierarchy.DescentNamedSeedEncoding
import OAI.Hierarchy.DescentArchivePalette
import OAI.Hierarchy.DescentPrimitiveView
import OAI.Hierarchy.DescentNamedHistoryShape

namespace OAI
/-! # A single primitive coefficient dictionary for all physically named terminal branches -/
namespace Hierarchy.DescentSixParty.SeedNamed.Palette
open DescentCompiler DescentKernelHistory DescentBundleHistory DescentInitialHost DescentColonies
open DescentRotor DescentResetGates DescentEpochTagKeys DescentPrimitivePalette Chronology
open DescentMixedRouter DescentResetInvoice Catalyst Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

attribute [local irreducible] Origin.archivePackage Origin.source

private def renameEncoding {P U : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {dict : U → List (List Bool) → F} (a : Archive W) (site : Equiv.Perm W.graph.Site)
    (edge : Equiv.Perm W.graph.Edge) (e : Encoding U dict a.bit) :
    Encoding U dict (renamedArchive a site edge).bit := ⟨e.code, e.correct⟩

private def carryEncoding {P U : Type} {d : ℕ} {bits : P → ℕ} {W V : MarkedWorld F d P bits}
    {dict : U → List (List Bool) → F} {a : Archive W} (pkg : ArchiveTransport a V)
    (e : Encoding U dict a.bit) : Encoding U dict pkg.data.bit :=
  pkg.carry (fun _ a => Encoding U dict a.bit) e

private def changeEncoding {P U : Type} {d : ℕ} {bits : P → ℕ} {W : MarkedWorld F d P bits}
    {dict : U → List (List Bool) → F} (a b : Archive W) (h : a = b)
    (e : Encoding U dict a.bit) : Encoding U dict b.bit := h ▸ e

open private Origin.archive_eq from OAI.Hierarchy.DescentNamedHistoryShape in
private def encodedOrigin {cp pins : ℕ} {X : Approximation F cp pins} {G : PoweredGadget F} {S : AtomSchedule}
    {q ε : ℝ} {k s z wire p : ℕ}
    {c : (initialGroup X S.copies s).Choice} {digits : Fin S.copies ≃ Fin (S.groupCount 0) × Block k}
    (o : Origin (G:=G) (S:=S) (s:=s) (q:=q) (fee:=ε) (z:=z) (wire:=wire) X c digits)
    (op : RotorSpec) (menu : Runnable F op) : Encoding (Label G s z op) (dictionary G op menu p) o.archive.bit :=
  changeEncoding o.archivePackage.data o.archive (Origin.archive_eq o).symm <|
    carryEncoding o.archivePackage <| renameEncoding (seedArchive X S.copies s c) (site o.raw) (edge o.raw)
      (seeded (G := G) (Z := z) (p := p) op menu X c)

variable {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k cut tail n h C f g p : ℕ}
variable (ordinary : OrdinaryRates G S k cut) (reset : ResetRates G S k (atRound S.rounds) n h C f g cut tail)
variable (branch : G.b≤2^S.capGain) (positive : 0<p) (room : 10*(X.size+1)≤S.initialSites)
variable (shorten : reentryRate h C*(1-(2-G.rate)/4)^S.rounds≤1/2)
set_option quotPrecheck false
local notation "cert" => SeedNamed.normalized_epochs_issued_joint (p:=p) X G S ordinary reset branch positive room shorten
local notation "last" => Epochs.finish G _ _ (cert).choose
local notation "initialWidth_" => S.firstWidth G.b p
local notation "initialGrain_" => S.grainAt G.b p 0
local notation "rot" => RotorSpec.ofRates reset
local notation "R" => max 1 (max reset.bitsR (C*reset.bitsR))
local notation "menu" => dictionary (s:=initialWidth_) (Z:=initialGrain_) G rot reset.menu p
local notation "selectAt" v_:arg => ((cert).choose_spec.2.2.choose_spec.choose_spec v_).choose
local notation "archiveAt" v_:arg => Branch.archive X G S (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (p:=p) (r:=(cert).choose) (c:=v_) (selectAt v_) positive

private def chosenArchive (c : (last).Choice) : Archive ((last).state c) := archiveAt c
local notation "namedArchive_" c_:arg => chosenArchive X G S ordinary reset branch positive room shorten c_
def atLeaf (c : (last).Choice) : Encoding (Label G initialWidth_ initialGrain_ rot) menu (namedArchive_ c).bit :=
  encodePath rot reset.menu (selectAt c).path positive ((selectAt c).path.recorded_whole p (selectAt c).recorded)
    ((cert).choose_spec.2.2.choose_spec.choose_spec c).choose_spec.2.2.1.2 (selectAt c).origin.archive
    (encodedOrigin (p := p) (selectAt c).origin rot reset.menu)

attribute [local irreducible] chosenArchive atLeaf
local notation "encodingAt" v_:arg => atLeaf X G S ordinary reset branch positive room shorten v_

theorem readLeaf (c : (last).Choice) (tag : (namedArchive_ c).bit.Tag) :
    indexed (G:=G) (s:=initialWidth_) (Z:=initialGrain_) (p:=p) rot reset.menu ((codec (G:=G) (s:=initialWidth_) (Z:=initialGrain_) rot).store ((encodingAt c).code tag))=(namedArchive_ c).bit.scalar tag :=
  indexed_read (G:=G) (s:=initialWidth_) (Z:=initialGrain_) (p:=p)
    (B:=(namedArchive_ c).bit) rot reset.menu (encodingAt c) tag


attribute [local semireducible] chosenArchive

/-- This recipe family interprets every normalized branch in the same `Label` type. -/
def relabel (c : (last).Choice) : BitDescription ((last).state c) :=
  Encoding.view (W := (last).state c) (B := (namedArchive_ c).bit) menu (encodingAt c)

local notation "outputAt" v_:arg => relabel X G S ordinary reset branch positive room shorten v_

theorem correct (c : (last).Choice) : ReadsBits ((last).state c).graph menu (outputAt c).recipe ((last).state c).tables :=
  (outputAt c).correct

def leafShape (c : (last).Choice) : WorldShape (F := F) (W := (last).state c) p R (outputAt c) :=
  Encoding.viewShape (W := (last).state c) (B := (namedArchive_ c).bit) (p := p) («R» := R) menu (encodingAt c)
    (Branch.bundleShape (k:=k) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=(cert).choose) (c:=c) (p:=p) X G S (selectAt c) positive (Nat.le_max_left ..))

theorem labels (c : (last).Choice) (v : ((last).state c).graph.Site) (u : ((outputAt c).recipe v).Node) :
    (codec (G:=G) (s:=initialWidth_) (Z:=initialGrain_) rot).fits (((outputAt c).recipe v).tag u) :=
  all_fit (G := G) (s := initialWidth_) (Z := initialGrain_) rot _


end
end Hierarchy.DescentSixParty.SeedNamed.Palette

end OAI
