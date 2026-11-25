import OAI.Hierarchy.DescentNamedUnitExponent
import OAI.Hierarchy.DescentNamedMaskedHomeGate
import OAI.Hierarchy.DescentNamedHistoryShape
import OAI.Hierarchy.DescentPlacedPrivateSeed

namespace OAI
/-! # The seed exponent from the genuine named terminal local records -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentKernelHistory DescentBundleHistory DescentHistoryOrder DescentCompiler DescentHostDegree DescentInitialHost Catalyst
open Computability.VPVNP.BurstRAM PrivateRAM DescentTerminalObservedExponent Computability.BorderVNP.Crossing
open scoped Fin.CommRing Classical BigOperators
noncomputable section
variable {F : Type} [Field F] {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
set_option quotPrecheck false
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
local notation "epochGraph" => ((Epochs.finish G hu he r).state c).graph
variable (sh : WorldShape p R (Branch.archive X G S b hp).bit)
local notation "row" => fun v=>(sh.sites v).recipe hp


open DescentTerminalRecipeRows DescentTerminalVertexFields DescentTerminalGraphPositions DescentTerminalSiteShelves DescentTerminalChronologicalBooks
open ThreeFlat.RAM PhysicalProcedure
variable {t₀ q₀ HN NN AN wb K : ℕ}
local notation "homes" => S.hostSize S.length
local notation "terminalGroups" => S.groupCount S.length
variable (L : Order ((Epochs.finish G hu he r).state c).graph (S.hostSize S.length) p) (byHome : L.home=b.target.home)
local notation "birth" => fun v=>((Branch.localNodes X G S b hp) v).toEmbedding.trans Fin.valEmbedding
local notation "real" => fun v=>(row v).restricted
variable (label : ((Branch.archive X G S b hp).bit.Tag×List (List SliceCode))→Fin t₀)
local notation "recipes" => DescentTerminalBundleRows.recipes L real hp birth label
variable {V B : ℕ} (banks : MaskAllocation.Channels (2^k)) (base header : ℕ)
local notation "width" => span q₀ t₀ HN NN AN p
local notation "cap" => cohortSize (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (w:=p) (groups:=terminalGroups) (blocks:=2^k)
local notation "size" => channelSize (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (w:=p) (groups:=terminalGroups) (blocks:=2^k)
local notation "cells" => MaskAllocation.marks size+cap
local notation "C₀" => MaskAllocation.counter (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (p:=p) (groups:=terminalGroups) banks base
local notation "O" => PrivateCounter.registers C₀ header homes cap
local notation "values" => measured (q:=q₀) (t:=t₀) (H:=HN) (N:=NN) (A:=AN) (w:=p) (groups:=terminalGroups) (C₀).layout

open DescentTerminalCompiledPrefix
local notation "format" => (⟨q₀,t₀,HN,NN,AN,p,terminalGroups⟩ : Home.Format)
theorem seed_counted_arguments (source : Memory wb) (held : b.path.Held header source)
    (rank : ∀i,Birth (recipes i))
    (hH : ∀i v,Fintype.card (recipes i v).Hidden≤HN)
    (hN : ∀i v,Fintype.card (recipes i v).Node≤NN)
    (hA : ∀i v u,(recipes i v).arity u≤AN)
    (hw : ∀i v u,(recipes i v).width u≤p)
    (short : ∀i v,(L.site i).arity v≤q₀)
    (occupied : ∀(i : Fin homes) c,blankAt (values source i) c≠0 ↔ ∃u,b.target.chart L byHome i u=c)
    (previous : ∀i v,let book:=record (L.site i) (recipes i) (rank i) (hH i) (hN i) (hA i) (hw i) (short i) v
      ArgumentReads (venueField (cellAt (values source i) (b.target.rawResident L byHome i v))) (fun j=>(value book j).val))
    : AddressPlan.SeedCount format banks base header homes source (deadCount hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites) := by
  have total :
      (∑i:Fin homes,privateHome (values source i))=liveCount hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites := calc
    _ = ∑i,∑v,Fintype.card (recipes i v).UsedWord := by
      apply Finset.sum_congr rfl
      intro i _
      exact b.target.private_home_arguments L byHome i _ (recipes i) (rank i) (hH i) (hN i) (hA i)
        (hw i) (short i) (occupied i) (previous i)
    _ = _ := DescentTerminalBundleRows.private_rows_volume epochGraph L hp row birth label
  have partition:=DescentTerminalObservedExponent.partition hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites
  refine ⟨volume epochGraph (Branch.archive X G S b hp).bit.recipe,held_volume X G S b hp held,?_⟩
  change (∑i:Fin homes,privateHome (values source i))*p+deadCount hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites=_
  rw [total]
  exact partition

theorem seed_counted (source : Memory wb) (held : b.path.Held header source)
    (rank : ∀i,Birth (recipes i))
    (hH : ∀i v,Fintype.card (recipes i v).Hidden≤HN)
    (hN : ∀i v,Fintype.card (recipes i v).Node≤NN)
    (hA : ∀i v u,(recipes i v).arity u≤AN)
    (hw : ∀i v u,(recipes i v).width u≤p)
    (short : ∀i v,(L.site i).arity v≤q₀)
    (occupied : ∀(i : Fin homes) c,blankAt (values source i) c≠0 ↔ ∃u,b.target.chart L byHome i u=c)
    (previous : ∀i v j,let record:=record (L.site i) (recipes i) (rank i) (hH i) (hN i) (hA i) (hw i) (short i) v
      allows (fun f=>(value record f).val) j → venueField
        (cellAt (values source i) (b.target.rawResident L byHome i v)) j=(value record j).val)
    : AddressPlan.SeedCount format banks base header homes source (deadCount hp epochGraph (Branch.archive X G S b hp).bit.recipe sh.sites) := by
  exact seed_counted_arguments X G S b hp sh L byHome label banks base header source held
    rank hH hN hA hw short occupied (fun i v=>ArgumentReads.of_allowed (previous i v))

def unitAddress {blocks : ℕ} (V : DescentTerminalCompiledPrefix.Home.Format)
    (shape : DescentTerminalCompiledPrefix.Shape) (channels : MaskAllocation.Channels blocks)
    (start header : ℕ) (_ : Unit) : ℕ := (AddressPlan.registers V shape channels start header).deadBits

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
