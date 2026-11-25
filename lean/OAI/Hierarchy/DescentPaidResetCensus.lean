import OAI.Hierarchy.DescentPaidResetRecorded
import OAI.Hierarchy.DescentPaidResetBankSites
import OAI.Hierarchy.DescentResetHeaderPlacement

namespace OAI
/-! # The reset resident funding source in the coordinates of the next chooser -/
namespace Hierarchy.DescentPaidResidentCount.Reset
open DescentSixParty DescentCompiler DescentKernelHistory DescentHostDirectory
open DescentPackedZip DescentSIMDLookup DescentStageEdgeReceipt DescentSixParty.StarKeys
open DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
variable {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D w hist n h C f g cut tail p : ℕ}
variable {cap : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
variable (b : ClosedReset cap ctl) (issued : b.Recorded p)
local notation "key" => (DescentOrderedReset.grains W b.count b.order)
local notation "vertex" => (b.frame.host.symm.toEmbedding.trans cap.vertex)
local notation "rank" => ((b.reset.rawHostRank b.terminals vertex).trans Fin.valEmbedding)
local notation "rows" => (DescentStageEdgeReceipt.groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) rank)
local notation "ps" => (DescentPhysicalOrder.rename (b.raw.siteFrom rows b.valid.coordinates))
local notation "rawId" => ((b.reset.nativeResetEdges b.terminals vertex key).order.trans Fin.valEmbedding)
local notation "pe" => (DescentPhysicalOrder.rename (DescentResetLocalOrder.allCode b.raw rawId S
  b.valid (b.raw.siteFrom rows b.valid.coordinates)))

local notation "bank" => b.reset.laneRecipe key (b.reset.unit/p) p issued.positive (Nat.div_mul_cancel issued.divides).symm
local notation "names" => b.reset.resetNames b.terminals
local notation "norm" => b.reset.orderedReblock b.terminals key


local notation "A" => b.next.placement
local notation "raw" => b.raw
local notation "nextGroup" => S.groupCount (i+1)
local notation "coords" => S.resetOutputDigits ctl.base ctl.radix b.age b.commonDepth
local notation "group" => (Equiv.refl (Fin nextGroup))
local notation "target" => b.next.vertex
local notation:max "rootAt" root:arg => (target (b.reset.placed b.terminals root))
local notation:max "activeAt" u:arg => ((coords (b.reset.blockId b.terminals u)).1)
local notation:max "lowAt" u:arg => ((coords (b.reset.blockId b.terminals u)).2)

/-- Pointwise lookup reads the authentic primary, relay, or mixed-bank payee at the
printed raw spatial address. Final site renaming does not permute packed rows. -/
theorem physical {precision : ℕ} (v) :
    DescentPacking.PackedMatch.Local.Stage.Census.count A group target precision
      (rootAt v) (activeAt v) (lowAt v) = ((payee b issued (names v):ℕ):Cell precision) := by
  have stored := congrArg (fun u => (b.raw.records u).length) ((ps).symm_apply_apply v)
  have coord := ClosedReset.Window.named_home b v
  have transfer := congrArg (fun a : (Fin nextGroup × b.next.V) × Fin (2^k) =>
    DescentPacking.PackedMatch.Local.Stage.Census.count A group target precision
      (target a.1.2) (group a.1.1) a.2) coord
  have seen := live A S b.next.valid group target precision (ps v)
  exact transfer.symm.trans (seen.trans (congrArg (fun a : ℕ => (a : Cell precision))
    (stored.trans (raw_paid b issued v))))

/-- A bank shared across all real dates can be attached directly to the next prefix scan.
Its producer dispatches on the three disjoint families of actual physical addresses. -/
theorem source {M wCPU precision : ℕ} (x : Fin (2^k)) (expr : Expr)
    (mem : Memory wCPU) (data_ : Fin (Fintype.card b.next.V)→Fin nextGroup→Cell precision)
    (loaded : Source expr data_ M mem)
    (primary : ∀t,
      let v:=(names).symm (.inl (false,t))
      lowAt v=x→data_ (rootAt v) (activeAt v)=((payee b issued (.inl (false,t)):ℕ):Cell precision))
    (relay : ∀t,
      let v:=(names).symm (.inl (true,t))
      lowAt v=x→data_ (rootAt v) (activeAt v)=((payee b issued (.inl (true,t)):ℕ):Cell precision))
    (bankPaid : ∀t,
      let v:=(names).symm (.inr t)
      lowAt v=x→data_ (rootAt v) (activeAt v)=((payee b issued (.inr t):ℕ):Cell precision))
    (vacant : ∀h g,(¬∃v,rootAt v=h ∧ activeAt v=g ∧ lowAt v=x)→data_ h g=0) :
    Source expr (fun h g=>DescentPacking.PackedMatch.Local.Stage.Census.count A group target precision h g x) M mem := by
  have equal (h) (g) : data_ h g=DescentPacking.PackedMatch.Local.Stage.Census.count A group target precision h g x := by
    by_cases populated : ∃v,rootAt v=h ∧ activeAt v=g ∧ lowAt v=x
    · obtain ⟨v,rfl,rfl,rfl⟩:=populated
      rw [physical b issued]
      obtain ⟨a,rfl⟩:=(names).symm.surjective v
      rw [Equiv.apply_symm_apply]
      rcases a with ⟨_|_,t⟩|t
      · exact primary t rfl
      · exact relay t rfl
      · exact bankPaid t rfl
    · rw [vacant h g populated,ghost A group target precision h g x]
      rintro ⟨v,hv,gv,xv⟩
      let u:=(ps).symm v
      have coordinates:=ClosedReset.Window.named_home b u
      have hp:=congrArg Prod.fst coordinates
      have hb:=congrArg Prod.snd coordinates
      change (A).pos (ps u)=_ at hp
      change (A).block (ps u)=_ at hb
      have inverse : ps u=v:=(ps).apply_symm_apply v
      rw [inverse] at hp hb
      exact populated ⟨u,by simpa only [hp] using hv,by simpa only [hp,Equiv.refl_apply] using gv,hb ▸ xv⟩
  exact (congrArg (fun rowValues => Source expr rowValues M mem) (funext fun h => funext (equal h))).mp loaded

end
end Hierarchy.DescentPaidResidentCount.Reset

end OAI
