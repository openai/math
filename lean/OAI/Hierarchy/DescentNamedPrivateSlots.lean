import OAI.Hierarchy.DescentNamedOperandBill
import OAI.Hierarchy.DescentNamedHistoryShape
import OAI.Hierarchy.DescentNamedPrivateArchive
import OAI.Hierarchy.DescentPackedPrivateAliases
import OAI.Hierarchy.DescentTerminalRestrictedRows

namespace OAI
/-! # The actual named terminal site's ragged operand slots and first private uses -/
namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentCompiler DescentHostDegree DescentInitialHost DescentKernelHistory DescentBundleHistory Catalyst
open DescentLocalPrivateNames
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false
attribute [local irreducible] Origin.source Origin.archivePackage
variable {F : Type} [Field F]
variable {cp nP : ℕ} (X : Approximation F cp nP) (G : PoweredGadget F) (S : AtomSchedule)
  {k n h C f g p R : ℕ}
variable {he : 0 ≤ (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower)}
  {hu : 0 ≤ (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower : ℝ) ^ S.priceExponent)) *
    (S.epochPower : ℝ) ^ S.priceExponent} {radix : S.radix = 2^k}
variable {r : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
  (t := S.rounds) S.height (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
variable {c : (Epochs.finish G hu he r).Choice} (b : Branch X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) radix R r c) (hp : 0 < p)
local notation "A" => Branch.archive X G S (p:=p) (n:=n) (h:=h) (C:=C) (f:=f) (g:=g) (r:=r) (c:=c) b hp
local notation "N" => ((Epochs.finish G hu he r).state c).graph


variable (stride : 1≤R) (hh : 0<S.height) (base : G.b≤2^S.capGain)
local notation "sh" => bundleShape X G S b hp stride
local notation "row₀" => fun v=>((sh).sites v).recipe hp
local notation "K₀" => NativeBranch.privateSlotCapacity G S R
local notation "a₀" => NativeBranch.privateSlotBits G S R

include hh base in
/-- The scheduled payload and the retained occurrence count bound all actual operand slots. -/
theorem operand_count_fit (v : (N).Site) :
    DescentTerminalRestrictedRows.operandCount (A).bit.recipe (sh).sites v≤K₀ := by
  have addresses:=((sh).sites v).addresses_bound R ((sh).stride v)
  have mass:=site_operand_volume X G S b hp hh base v
  apply Nat.le_of_mul_le_mul_right _ hp
  calc
    _ ≤ (R+1)*(∑u,((A).bit.recipe v).nodeBits u) := addresses
    _ ≤ (R+1)*(p*S.epochPower^(operandExponent G S+S.localTokenExponent)) := Nat.mul_le_mul_left _ mass
    _ = _ := by unfold NativeBranch.privateSlotCapacity;ring

include hh base in
theorem arguments_fit (v : (N).Site) (u : ((A).bit.recipe v).Node) :
    (∑j,∑g,(((sh).sites v).chunk u j g).count)≤K₀ :=
  (Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ u)).trans
    (operand_count_fit X G S b hp stride hh base v)

include hh base in
theorem private_slots_fit (v : (N).Site) : (∑u,(row₀ v).arity u)≤K₀ := by
  apply Nat.le_trans _ (operand_count_fit X G S b hp stride hh base v)
  apply le_of_eq
  apply Finset.sum_congr (congrArg (@Finset.univ ((A).bit.recipe v).Node) (Subsingleton.elim _ _))
  intro u _
  exact ((sh).sites v).recipe_refs hp u

include hh base in
theorem private_card_fit (v : (N).Site) : Fintype.card (Slot (row₀ v))≤K₀ := by
  simpa only [Slot,Fintype.card_sigma,Fintype.card_fin] using
    private_slots_fit X G S b hp stride hh base v

include hh base in
/-- Within each physical terminal site, the order is the real local node birth, then the argument number. -/
def privateSlot (v : (N).Site) : Slot (row₀ v)↪Fin K₀ :=
  orderedSlots (row₀ v) ((localNodes X G S b hp v).toEmbedding.trans Fin.valEmbedding)
    (private_card_fit X G S b hp stride hh base v)

theorem privateSlot_val (v : (N).Site) (arg : Slot (row₀ v)) :
    (privateSlot X G S b hp stride hh base v arg).val=
      ProtocolRAMPortRanks.«prefix» (row₀ v).arity (fun u=>(localNodes X G S b hp v u).val) arg.1+arg.2.val :=
  orderedSlots_val (row₀ v) _ _ arg

def privateCode (v : (N).Site) : (row₀ v).UsedWord ↪ DescentSIMDLookup.Cell a₀ :=
  let first:=firstAlias (row₀ v) (privateSlot X G S b hp stride hh base v)
  {toFun:=fun x=>⟨(first x).val+1,(Nat.succ_le_of_lt (first x).isLt).trans_lt
      (Nat.lt_pow_succ_log_self (b:=2) (by decide) _)⟩
   inj':=by
     intro x y eqn
     apply first.injective
     exact Fin.ext (Nat.add_right_cancel (congrArg Fin.val eqn))}

theorem privateCode_nz (v : (N).Site) (word : (row₀ v).UsedWord) :
    privateCode X G S b hp stride hh base v word≠0 :=
  fun h=>Nat.succ_ne_zero _ (congrArg Fin.val h)

theorem privateCode_first (v : (N).Site) (word : (row₀ v).UsedWord) :
    ∃arg, read (row₀ v) arg=some word ∧
      (privateCode X G S b hp stride hh base v word).val=(privateSlot X G S b hp stride hh base v arg).val+1 ∧
      ∀arg', read (row₀ v) arg'=some word →
        (privateSlot X G S b hp stride hh base v arg).val≤(privateSlot X G S b hp stride hh base v arg').val := by
  let slot:=privateSlot X G S b hp stride hh base v
  obtain ⟨arg,pos,found⟩:=firstAlias_read (row₀ v) slot word
  refine ⟨arg,found,?_,?_⟩
  · exact congrArg (fun a : Fin K₀=>a.val+1) pos.symm
  · intro other same
    exact pos.symm ▸ firstAlias_le (row₀ v) slot other word same

include hh base in
theorem native_field_counts (v : (N).Site) :
    Fintype.card ((row₀ v).restricted).Hidden≤K₀ ∧
    Fintype.card ((row₀ v).restricted).Node≤S.epochPower^S.localTokenExponent ∧
    (∀u,((row₀ v).restricted).arity u≤K₀) ∧ (∀j,((row₀ v).restricted).width j=p) := by
  have slots:=private_slots_fit X G S b hp stride hh base v
  exact ⟨(row₀ v).used_le_slots.trans slots,site_nodes X G S b hp hh v,
    fun u=>(Finset.single_le_sum (fun _ _=>Nat.zero_le _) (Finset.mem_univ u)).trans slots,fun _=>rfl⟩

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
