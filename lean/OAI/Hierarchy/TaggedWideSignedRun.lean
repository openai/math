import OAI.Hierarchy.TaggedWideFundedBranchReceipt
import OAI.Hierarchy.TaggedWideCalendarRejected
import OAI.Hierarchy.TaggedWideHostAdmission

namespace OAI
/-! # Native selected returns assemble the actual signed-site machine run -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard ReportSockets CatalogueRows CatalystArchive
open Tagged Tagged.WideStack TaggedShorterBudget TaggedShorterSupergroups ProtocolRAMEmit
open ProtocolRAMReportedPorts PurchaseFrozen
open scoped Classical BigOperators
set_option quotPrecheck false
set_option hygiene false
set_option maxRecDepth 8192
set_option maxHeartbeats 2200000
set_option cleanup.letToHave false

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ κ A δ ξ C : ℝ} {u : ℝ→ℝ}
    (v : FixedProtocolFormat F k p q Q σ Λ) (x : WideParent κ A) (tapeSize : ℕ)
    (π : Equiv.Perm (Fin (2^x.h))) (input : Boot.Tape x.h (2^v.W)) (m ell short unitCost : ℕ)
local notation "b" => (v.widePlacement x.h x.w).catalogue
local notation "jobs" => v.wideJobs
local notation "geom" => typeMenu κ A v.W m k jobs ell v.stage_positive (fun _=>short+ell)
local notation "menu" => (geom).menu u δ ξ
local notation "slots" => purchaseSlots x.h v.W k jobs ell
local notation "ports" => WideMemory.H x.h v.W k jobs
local notation "dir" => WideMemory.dir x.h v.W k jobs
local notation "order" => v.wideOrder x.h x.w
local notation "positive" => (b).transport order
local notation "reserve" => fuel v.mesh*x.w
open CoreBoard.PhysicalTerm Tagged.WideControlJoin WideCalendarSites HistoryRoles
open ThreeFlat Routing WireTelescope WireTelescope.CalendarTape TaggedPrune

local notation "days" => events v.mesh
local notation "dated" => v.wideDated x.h x.w ell unitCost
local notation "lay" => v.wideInstalledLayout x m ell short u δ ξ unitCost dated
local notation "size" => v.wideInstalledSize x m ell unitCost dated
local notation "seed" => v.wideInstalledHeader x m ell short u δ ξ unitCost dated
  (v.wide_dated_sites x.h x.w ell unitCost) (v.wide_dated_edges x.h x.w ell unitCost) (fun _=>0)
local notation "dst" => TerminalLayout.destination (v.wideSignedPage x.h x.w
  (v.fixedTerminalStock (v.widePlacement x.h x.w) x.h x.w))
local notation "W" => Native.wordBits x.h (2^v.W) Native.copies
variable {N : ℕ} (cpu : v.ParentFullCPUs m ell short u δ ξ unitCost N x) (room : cpu.SiteRoom)
local notation "G" => (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).2
local notation "slot" => (v.wideSelector x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le).format.slot
variable (a : SignedSites v m ell short δ ξ unitCost cpu)
local notation "Z" => a.schedule
local notation "D" => v.parentShared x m ell short unitCost ((days).length+1)
local notation "rout" => (Z).nativeRouting D
local notation "Ex" => OpenPins x.h x.w ((Z).nativeRouting D).catalyst
local notation "Se" => Fin ((Z).nativeRouting D).selectors
local notation "Priv" => (b).Private order
local notation "cap" => v.widePrivateUnit unitCost*x.w
local notation "lim" => fun _:Priv=>cap
local notation "view" => v.wideHistoryUnit unitCost*x.w
local notation "roles" => HistoryRoles.ceiling v.sampler (h:=x.h) («W»:=v.W) (k:=k) (attempts:=jobs)
  v.mesh unitCost v.keepLimit (fuel v.mesh) x.w
local notation "history" => Fin (((days).length+1)*Fintype.card
  ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r)))
local notation "outputBits" => ((Fin (dir).groups×Fin ports)×Fin view)
local notation "num" => CalendarTerms.privateWorkspace (geom).index (Equiv.refl Priv) lim roles
  (dir).groups ports (2^ell) ((days).length+1) view x.w
local notation "freeNet" => v.widePrivateGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.privateBits
local notation "planeNet" => v.widePlane («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room

local notation "n" => ((days).length+1)*Fintype.card ((r:Public v.sampler x.h v.W k jobs)×Fin (roles r))

local notation "keep" => v.wideKeepNetwork x m ell short u δ ξ unitCost cpu.room Ex Se D
local notation "pad" => cpu.positiveGate room Z
local notation "time" => v.wideHistoryGate («Ex»:=Ex) («Se»:=Se) x m ell short u δ ξ unitCost cpu.room room.history
local notation "flagAt" => (lay).pruneScratch+(lay).pruneRows
local notation "index" => TaggedPrune.Index (rout).count
local notation "header" => cpu.header (rout).catalyst
local notation "adm" => cpu.admitted (rout).catalyst
local notation "hardware" => a.installed room
local notation "source" => fun _ : Fin (m+1)=>slots
local notation "count" => purchaseModules v.W u δ ξ menu x
local notation "target" => fun i=>purchaseCandidates x.h v.W k jobs (source i) ((menu).height i x) (count i)

variable (items : PurchaseList (F:=F) (C:=C) menu x source target count)
local notation "cuts" => fun i=>(items i).cut ((hardware).read i)

/-- Facts from one genuine paid output on a matching input rank. Rejected
ranks need only their native final pruning word and the paid machine trace. -/
structure SignedSites.SelectedOutput (e : Ex→Bool) (s : Se→Bool) (j : index) (out : Memory W) : Prop where
  ran : (G).Ran (header e s) out
  flag : out flagAt=if ((rout).links j).Keep (2^x.h) then 1 else 0
  receipt : ((rout).links j).Keep (2^x.h)→Nonempty ((Z).Receipt (geom).index G cuts keep pad freeNet planeNet time a.enter a.finish a.step
    j.1 j.2 e s ((G).terminal out) (dir).groups ports (2^ell) view m n)

local notation "selected" => SignedSites.SelectedOutput (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unitCost)
    (cpu:=cpu) (a:=a) (room:=room) (items:=items)

/-- Choosing an observed output for every matching public tag and selector
produces one actual Run. The uniqueness of the numbered path gives the same
return to every subsequent receipt readout. -/
def SignedSites.run_from_selected
    (returned : ∀(e : Ex→Bool) (s : Se→Bool) (j : index),reads (rout).encoding e s j→
      ∃out,selected e s j out) : (a.physical room items).Run := by
  classical
  let hasMatch (e : Ex→Bool) (s : Se→Bool) := ∃j:index,reads (rout).encoding e s j
  have chooseOutput (e : Ex→Bool) (s : Se→Bool) (has : hasMatch e s) :
      ∃out,∀j:index,reads (rout).encoding e s j→selected e s j out := by
    obtain ⟨j,hj⟩:=has
    obtain ⟨out,obs⟩:=returned e s j hj
    refine ⟨out,fun k hk=>?_⟩
    exact (reads_unique (rout).encoding hj hk) ▸ obs
  let out (e : Ex→Bool) (s : Se→Bool) : Memory W := if ok : hasMatch e s then (chooseOutput e s ok).choose else 0
  have facts (e : Ex→Bool) (s : Se→Bool) (j : index) (hj : reads (rout).encoding e s j) :
      selected e s j (out e s) := by
    have present : hasMatch e s:=⟨j,hj⟩
    dsimp only [out]
    rw [dite_eq_left present]
    exact (chooseOutput e s present).choose_spec j hj
  have policy (e : Ex→Bool) (s : Se→Bool) (p : Equiv.Perm (Tagged.Row x.h))
      (matchesTag : (p : Tagged.Row x.h→Tagged.Row x.h)=Tagged.tag (fun i=>e (.inl i))) :
      adm e s ↔ ∃!i : Fin ((rout).count p),(rout).encoding p i=s :=
    v.widePrefixLanguage x.h x.w cpu.age cpu.ready.credit cpu.ready.size_le size seed Z D e s p matchesTag
  have paidRun (e : Ex→Bool) (s : Se→Bool) (auth : authentic (parentTag rout) e s) (admitted : adm e s) :
      (G).Ran (header e s) (out e s) := by
    obtain ⟨j,hj⟩:=((Z).tape_iff (geom).index lim roles (dir).groups ports (2^ell) ((days).length+1) view
      e s auth (adm e s) (policy e s)).mp admitted
    exact (facts e s j hj).ran
  apply (Z).assembled_run_kept (geom).index lim roles (dir).groups ports (2^ell) ((days).length+1) view
    (v.wideFullGates x m ell short u δ ξ unitCost cpu.room).1 G (cpu.firstPins (rout).catalyst)
    (cpu.paidPins (rout).catalyst) (0 : Fin 1) keep pad freeNet planeNet time a.enter a.finish a.step
    cuts (fun i=>⌊((menu).height i x:ℝ)^A⌋₊) m n x.formats.2.1 header header
    (fun e s=>(cpu.reads (rout).catalyst e s).1) (fun e s=>(cpu.reads (rout).catalyst e s).2)
    adm (fun e s auth=>cpu.prefix (rout).catalyst e s auth) (fun e s _=>policy e s) out paidRun
    (v.wideFullGates_word_room (u:=u) (δ:=δ) (ξ:=ξ) x m ell short unitCost cpu.room cpu.large).2
  · intro e s p i hj kept
    exact ((facts e s ⟨p,i⟩ hj).receipt kept).some
  · intro e s p i hj rejected d
    have observed:=v.wide_keep_flag x m ell short u δ ξ unitCost cpu.room Ex Se D (out e s) (out e s)
      (fun _ _=>rfl) (((rout).links ⟨p,i⟩).Keep (2^x.h)) (facts e s ⟨p,i⟩ hj).flag e s (Equiv.refl D) d
    have compose : d ∘ ⇑(Equiv.refl D).symm = d := by funext pin; rfl
    simpa only [compose, ite_eq_right rejected] using observed

theorem SignedSites.evaluates_from_selected
    (returns : ∀items : PurchaseList (F:=F) (C:=C) menu x source target count,
      ∀(e : Ex→Bool) (s : Se→Bool) (j : index),reads (rout).encoding e s j→
      ∃out,SignedSites.SelectedOutput (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unitCost)
    (cpu:=cpu) (a:=a) (room:=room) (items:=items) e s j out) :
    a.Evaluates room C :=
  fun items=>⟨SignedSites.run_from_selected (v:=v) (x:=x) (m:=m) (ell:=ell) (short:=short) (unitCost:=unitCost)
    (cpu:=cpu) (a:=a) (room:=room) (items:=items) (returns items)⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
