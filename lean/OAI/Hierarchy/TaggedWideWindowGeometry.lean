import OAI.Hierarchy.TaggedWideProgramSyntax
import OAI.Hierarchy.TaggedWideNativeFamily
import OAI.Hierarchy.ProtocolRAMFrozenWindowROM
import OAI.Hierarchy.TaggedWideReadoutPurchases
import OAI.Hierarchy.ProbePhysicalTypeMenu

namespace OAI
/-! # The actual finite width-class windows and their immutable and writable addresses -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open AdaptiveProbe ProbeStage CoreBoard HistoryRoles ReportSockets Tagged TaggedShorterBudget
open ProtocolRAMFrozenWindow ProtocolRAMPackedRanked TaggedShorterReportAdvice
open ThreeFlat Routing CallPool
open scoped Classical BigOperators
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ) {κ A : ℝ} (x : WideParent κ A)
  (m ell short : ℕ) (u : ℝ→ℝ) (δ ξ : ℝ)
local notation "P" => v.widePlacement x.h x.w
local notation "dir" => WideMemory.dir x.h v.W k v.wideJobs
local notation "slots" => purchaseSlots x.h v.W k v.wideJobs ell

def wideWindowMenu :=
  (typeMenu κ A v.W m k v.wideJobs ell v.stage_positive (fun _=>short+ell)).menu u δ ξ

/-- The same lookup page can address an entire emitted offer, any width up to
the true final aperture, and any group, slot or packed candidate offset. -/
def wideWindowDemand (cap : ℕ) :=
  10*((P).catalogue.rows*cap)+((dir).groups+1)*(slots+1)+cap*x.w+1

def wideWindowStride (cap : ℕ) :=
  13*2^groupBits (v.wideWindowDemand x ell cap)+2*2^groupBits (dir).groups

def wideWindow (cap romBase : ℕ) (i : Fin (m+1)) : ProtocolRAMFrozenWindow.Format :=
  let menu:=v.wideWindowMenu m ell short u δ ξ
  let h:=menu.height i x
  { N:=(P).catalogue.rows, groups:=(dir).groups, D:=slots,
    B:=2^(h-1),M:=purchaseModules v.W u δ ξ menu x i, n:=h,
    w:=x.w,menu:=m,cap:=cap,γ:=i.val,gb:=groupBits (dir).groups,
    rom:=romBase+i.val*v.wideWindowStride x ell cap, bits:=groupBits (v.wideWindowDemand x ell cap) }

local notation "fmt" => v.wideWindow x m ell short u δ ξ

theorem wideWindow_end (cap start : ℕ) (i : Fin (m+1)) :
    (fmt cap start i).adviceEnd = start+(i.val+1)*v.wideWindowStride x ell cap := by
  simp only [Format.adviceEnd, Format.originBase,Format.biasBase,wideWindow,wideWindowStride]
  ring

theorem wideWindow_disjoint (cap start : ℕ) {i j : Fin (m+1)} (ij : i<j) :
    (fmt cap start i).adviceEnd≤(fmt cap start j).rom := by
  rw [v.wideWindow_end]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (show i.val+1≤j.val from ij)) _

theorem wideWindow_rom_bound (cap start : ℕ) (i : Fin (m+1)) :
    (fmt cap start i).adviceEnd≤ start+(m+1)*v.wideWindowStride x ell cap := by
  rw [v.wideWindow_end]
  exact Nat.add_le_add_left (Nat.mul_le_mul_right _ i.isLt) _

theorem wideWindow_addresses (cap start : ℕ) (i : Fin (m+1)) :
    let f:=fmt cap start i
    f.groups≤2^f.gb ∧ f.groups≤2^f.bits ∧ f.D≤2^f.bits ∧
      f.groups*poolBatchCount f.D f.B≤2^f.bits ∧ 10*(f.N*f.cap)≤2^f.bits ∧ cap*x.w<2^f.bits := by
  let f:=fmt cap start i
  let total:=v.wideWindowDemand x ell cap
  have fits : total≤2^f.bits:=group_capacity total
  have batchPos : 0<f.B:=by dsimp [f,wideWindow];positivity
  have batch : poolBatchCount f.D f.B≤f.D:=by
    rw [poolBatchCount]
    apply (Nat.div_le_iff_le_mul_add_pred batchPos).mpr
    have times : f.D≤f.B*f.D := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right f.D batchPos
    omega
  have live : f.groups*f.D≤(f.groups+1)*(f.D+1):=by nlinarith
  change f.groups≤2^f.gb ∧ _
  refine ⟨group_capacity _,?_,?_,?_,?_,?_⟩
  · apply le_trans _ fits
    change _≤10*(f.N*cap)+(f.groups+1)*(f.D+1)+cap*x.w+1
    nlinarith
  · apply le_trans _ fits
    change _≤10*(f.N*cap)+(f.groups+1)*(f.D+1)+cap*x.w+1
    nlinarith
  · apply (Nat.mul_le_mul_left f.groups batch).trans
    apply live.trans
    apply le_trans _ fits
    change _≤10*(f.N*cap)+(f.groups+1)*(f.D+1)+cap*x.w+1
    omega
  · apply le_trans _ fits
    change 10*(f.N*cap)≤10*(f.N*cap)+(f.groups+1)*(f.D+1)+cap*x.w+1
    omega
  · apply lt_of_lt_of_le _ fits
    change _<10*(f.N*cap)+(f.groups+1)*(f.D+1)+cap*x.w+1
    omega

theorem wideWindow_mutable_before (cap start floor : ℕ) (i : Fin (m+1)) :
    let need:=fun j=>(fmt cap start j).window.stop 0
    let pos:=WindowSeries.start floor need i
    (fmt cap start i).window.stop pos≤WindowSeries.finish floor need := by
  intro need pos
  rw [Size.stop_add]
  exact WindowSeries.within floor need i

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
