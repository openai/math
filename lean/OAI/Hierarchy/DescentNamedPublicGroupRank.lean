import OAI.Hierarchy.DescentNamedLeafOrder
import OAI.Hierarchy.DescentTerminalPublicRelative

namespace OAI
/-! # The actual row address of a public operand in the selected host's directory -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open DescentExterior Computability.VPVNP.RAMSerialization DescentTerminalDenseGraphRead DescentTerminalDenseWindow
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
variable {F : Type} [Field F] {cp P : ℕ} (X : Approximation F cp P) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)


local notation "s" => S.firstWidth G.b p
local notation "net" => ((Epochs.finish G hu he r).state c).graph
local notation "E" => Fintype.card (Port P X.width)
variable {tail j rest : ℕ} (base : S.baseGroups=2^tail)
variable (width : S.groupWidth k tail 0+k=j+(j+rest))



open DescentTerminalGraphPositions DescentTerminalCableOrder
open ThreeFlat.Routing
local notation "retained" => S.groupWidth k tail S.length+k
local notation "O" => leafOrder X G S b hp base width
local notation "homeRow" => publicHost X G S b hp base width
local notation "pins" => NativeBranch.rawPin S (X:=X) (radix:=radix) base width
local notation "M" => publicLayout X G S b hp base width
local notation "rows" => (pins).symm.trans (chart (j:=j) (r:=rest) M)
local notation "Pin" => Σ _:Fin S.copies,Fin E

theorem public_group_rank (room : j≤retained) (whole : p∣s)
    (i : Fin (S.hostSize S.length)) (g : Order.Group O i) (external : g.val=none)
    (nm : Order.At O i g) (z : Pin) (chunk : Fin (poolBatchCount (s*1) p))
    (label : nm.val=.inr ⟨z,chunk⟩) :
    (Order.inGroup O i g nm).val =
      (Computability.BorderVNP.FragmentBucket.prior homeRow (rows z).1.val i*2^j+(rows z).2.val)*(s/p)+chunk.val := by
  refine inGroup_public_slot rows homeRow net b.target.home b.target.order _ _ hp s whole
    (fun _=>Nat.mul_one s) ?_ i g external nm z chunk label
  intro x
  simpa only [Equiv.trans_apply, Equiv.apply_symm_apply] using public_host_read X G S b hp base width room ((pins).symm x)

end
end Hierarchy.DescentSixParty.SeedNamed.Branch
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
