import OAI.Hierarchy.DescentSeedLocalEnumeration
import OAI.Hierarchy.DescentLocalArchiveOrder
import OAI.Hierarchy.DescentNormalizedEpochs

namespace OAI
/-! # Iterating the physical per-site scalar order along a reached path -/
namespace Hierarchy.DescentLocalArchiveOrder
open DescentKernelHistory DescentSixParty DescentSixParty.Chronology DescentCompiler DescentSharedCableNames
open DescentInitialHost Catalyst DescentRotor
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} {S : AtomSchedule} {k : ℕ}

def unmixed {W : MarkedWorld F d P bits} : Normalize W → Prop
  | .done _=>True
  | @Normalize.merge ..=>False
  | .split _ _ _ _ rest=>unmixed rest
  | .named _ _ _ rest=>unmixed rest

def follow {W : MarkedWorld F d P bits} (n : Normalize W) (B : BitDescription W)
    (order : Local B) (ok : unmixed n) : Local (B.follow n) :=
  match n,ok with
  | .done _,_=>order
  | @Normalize.merge ..,bad=>False.elim bad
  | .split _ q m fit rest,h=>follow rest (B.pieces m q fit) order h
  | .named _ s e rest,h=>follow rest (B.renamed s e) (fun v=>order (s.symm v)) h

theorem seed_zero {cp ports : ℕ} (X : Approximation F cp ports) (R size : ℕ) (c : (initialGroup X R size).Choice)
    (v : ((initialGroup X R size).state c).graph.Site) (a : ((seedArchive X R size c).bit.recipe v).Node) :
    (seed X R size c v a).val=0 := by
  rcases v with ⟨v,u|u⟩ <;> have h:=(seed X R size c _ a).isLt <;> change _ < Fintype.card Unit at h <;> simp at h <;> omega

variable {i z D n h C f g cut tail wire hist : ℕ}
variable {cap : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}

def reset (b : ClosedReset cap ctl) (p : ℕ) (hp : 0<p) (whole : p∣b.reset.unit)
    (a : Archive W) (order : Local a.bit) : Local (resetArchive b p hp whole a).bit := by
  let split := BitDescription.granular W b.count (z*G.b) b.fit a.bit
  let key := DescentOrderedReset.grains W b.count b.order
  have fit : b.reset.unit=b.reset.unit/p*p := (Nat.div_mul_cancel whole).symm
  let loc := b.reset.physicalLocalOrder split b.terminals key _ p hp fit (resetMenu b)
    (cap.placement.site cap.vertex cap.valid.coordinates) (fun v=>(order v).toEmbedding.trans Fin.valEmbedding)
  exact follow b.reblock _ loc (by trivial)

def trajectory {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i₁ z₁ D₁ w t : ℕ}
    {start : Reached W₀ G q ε S k i₀ z₀ D₀ w t} {last : Reached W₁ G q ε S k i₁ z₁ D₁ w t}
    (p : ℕ) (hp : 0<p) (a : Archive W₀) (old : Local a.bit) (path : Path start last) (whole : path.whole p) :
    Local (path.archive p hp a whole).bit :=
  match path,whole with
  | .here,_=>old
  | .ordinary prev ticket,ok=>advance ticket _ (trajectory p hp a old prev ok)
  | .reset prev b,ok=>reset b p hp ok.2 _ (trajectory p hp a old prev ok.1)

end
end Hierarchy.DescentLocalArchiveOrder

namespace Hierarchy.DescentSixParty
open DescentCompiler DescentInitialHost Catalyst CorrectionBatch DescentLocalArchiveOrder
noncomputable section
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p : ℕ}
local notation "wire" => S.epochPower^S.priceExponent
local notation "s" => S.firstWidth G.b p
local notation "q" => (1/((s:ℝ)*(wire:ℝ)):ℝ)
local notation "ε" => (((S.initialSites*S.copies:ℕ):ℝ)/S.epochPower)
local notation "u" => q*(wire:ℝ)
local notation "Ht" => GroupStage.depthBound (atRound S.rounds) n f g
local notation "start" => initialGroup X S.copies s

def NativeBranch.localNodes {he : 0≤ε} {hu : 0≤u} {radix : S.radix=2^k} {R : ℕ}
    {r : Epochs G hu he (h:=h) (C:=C) («Ht»:=Ht) (t:=S.rounds) S.height start}
    {c : (Epochs.finish G hu he r).Choice} (b : NativeBranch X G S radix R r c) (hp : 0<p) :
    DescentLocalArchiveOrder.Local (NativeBranch.archive X G S b hp).bit :=
  trajectory p hp _ (DescentLocalArchiveOrder.seed X S.copies s _) b.path (b.path.recorded_whole p b.recorded)

end
end Hierarchy.DescentSixParty

end OAI
