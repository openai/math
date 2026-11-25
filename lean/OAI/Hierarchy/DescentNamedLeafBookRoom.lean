import OAI.Hierarchy.DescentNamedLeafOrder
import OAI.Hierarchy.DescentTerminalBookTokens

namespace OAI
/-! # Rectangles and compact names of the actual paid terminal leaf -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentInitialHost DescentMixedRouter DescentResetInvoice Catalyst CatalystSubstitution
open DescentTerminalExteriorPackets DescentKernelHistory CorrectionBatch
open scoped Classical BigOperators
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

local notation "O" => leafOrder X G S b hp base width
local notation "A" => NativeBranch.localLimit G S
local notation "V" => S.groupCount S.length*2^k

open DescentTerminalLocalPortBook

theorem leaf_local_room (i : Fin (S.hostSize S.length)) :
    Room ((O).site i) 4 V (V*A) A := by
  obtain ⟨groups,nodes,arity,size⟩:=leaf_book_bounds X G S b hp base width i
  exact ⟨groups,nodes,size,arity⟩

def leaf_name (i : Fin (S.hostSize S.length)) :=
  rowName ((O).site i) (leaf_local_room X G S b hp base width i)

def leaf_arg (i : Fin (S.hostSize S.length)) :=
  refName ((O).site i) (leaf_local_room X G S b hp base width i)

theorem leaf_arg_matches (i : Fin (S.hostSize S.length)) (v : ((O).site i).Arg) :
    leaf_arg X G S b hp base width i v =
      leaf_name X G S b hp base width i (((O).site i).arg v.1 v.2) := rfl

end
end Hierarchy.DescentSixParty.SeedNamed.Branch
end OAI

open OAI.Hierarchy.DescentSixParty.SeedNamed
attribute [local irreducible] Origin.source Origin.archivePackage Branch.pinSpine Branch.originalPin
