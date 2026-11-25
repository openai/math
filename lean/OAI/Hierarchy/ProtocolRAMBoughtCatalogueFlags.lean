import OAI.Hierarchy.ProtocolRAMBoughtCatalogueROM
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueSupport
import OAI.Hierarchy.ProtocolRAMBoughtTerminalPorts

namespace OAI
/-! # Exact active purchase ordinals on the priced terminal calendar -/

namespace Hierarchy.ProtocolRAM.BoughtSockets
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native PurchaseFrozen ReportSockets ProbeStage.CoreBoard
open TaggedShorterSupergroups Calendar Calendar.CatalogueRows
open scoped Fin.CommRing Classical
noncomputable section
variable {z W k attempts K H q goods r edges N jobs : ℕ}

/-- Bidirectional identification of the original acquired-flag operands, sufficient
also for a dated scan which leaves every dormant physical role at width zero. -/
theorem priced_flags (c : Mesh) (finish : ℝ) (prices : PhasePrice) (arena : Arena)
    (F : Attempt→Format z (2^W) k q goods) (initial width cap : ℕ) (sink : Sink r edges)
    (idBase : ℕ) (role : Attempt→Expr) (ids : Attempt→Fin goods→Expr)
    (order : ∀a,arena.base c (.attempt a)≤(F a).market.failures.base ∧
      arena.base c (.attempt a)≤(F a).market.shelf.firstBase ∧ arena.base c (.attempt a)≤(F a).testsStart)
    (dates : Fin attempts→Fin (c.inject+c.cool)×Fin c.outerFuel)
    (S : PurchaseSampler) (depth outer keys remap super sites : ℕ)
    (π : Equiv.Perm (Fin (2^z))) (entry : Shelf.Mem z (2^W)) :
    let C:=pricedInstalled c finish prices F (feedColumns (N:=N) c arena F initial width cap) sink idBase role ids
    let output:=run C (events c) entry
    let atDate:=fun i=>Attempt.outer (dates i).1.val (dates i).2.val
    let market:=fun i=>(F (atDate i)).atTime c finish prices (atDate i)
    let v:=Directory.ofChart outer keys remap super sites atDate C (fun i=>(market i).shelf)
    let mode:=fun i=>observedMode C entry (dates i).1.val (dates i).2.val
    let frozen:=fun i=>(market i).failures.pass.apply ((guard C (atDate i)).apply (trialState C entry (dates i).1.val (dates i).2.val))
    let marks : Marks z W k attempts:=fun i=>Shelf.catalogueMarks (mode i) (market i).shelf (market i).phase (market i).temperature (market i).kind (frozen i)
    let flag:=v.archived z (2^W) k S.degree depth v.flagBase
    let head:=v.header z (2^W) k S.degree depth
    let w:=wordBits z (2^W) Native.copies
    ∀(fixture : Fin attempts→Shelf.Mem z (2^W)),
    (∀i,(market i).sampler=S ∧ (market i).depth=depth) →
    (∀i,(market i).shelf.Incoming (k:=k) (market i).sampler π (market i).depth (market i).phase (market i).temperature (market i).kind (frozen i)) →
    (∀i (j : Key z (2^W) k),(market i).shelf.Prepared (market i).sampler (market i).depth (fixture i) j (frozen i)) →
    mounted C (events c) entry → ArchiveRoom C entry (c.inject+c.cool) →
    (∀i,(market i).rows≤2^(F (atDate i)).batch.decisionBits) →
    (∀i,(repair C (atDate i)).purchaseOut+(market i).rows≤arena.base c (.attempt (atDate i))+arena.stride) →
    head.Loaded output → attempts≤2^w →
    ∀j : Fin head.count,flag.eval output (j.val:Word w)≠0 ↔
      ∃path : Bought S π depth marks,head.enum ⟨path.1,BoughtLocation.relative path.2⟩=j := by
  intro C output atDate market v mode frozen marks flag head w fixture shape input static mountedAll archive padded area ROM hEvents j
  have slots i := (dates i).1.isLt
  have fuel i := (dates i).2.isLt
  have room i : (v.shelf i).flagsBase S z (2^W) k depth+count z (2^W) k*paths z S.degree depth<2^w := by
    have head:=outer_head_ready mountedAll (slots i) (fuel i)
    have readyMarket : (market i).ready ((guard C (atDate i)).apply (trialState C entry (dates i).1.val (dates i).2.val)) := head.2.1
    have below := readyMarket.2.2.2.1
    change (market i).shelf.flagsBase S z (2^W) k depth+count z (2^W) k*paths z S.degree depth<2^(wordBits z (2^W) Native.copies)
    simpa only [Market.flags,Market.rows,(shape i).1,(shape i).2] using below
  have flags i := priced_flag_terminal (N:=N) c finish prices arena F initial width cap sink idBase role ids order entry
    (dates i).1.val (dates i).2.val (slots i) (fuel i) mountedAll archive (padded i) (area i)
  have inputs i : (v.shelf i).Incoming (k:=k) S π depth (market i).phase (market i).temperature (market i).kind (frozen i) := by
    change (market i).shelf.Incoming (k:=k) S π depth (market i).phase (market i).temperature (market i).kind (frozen i)
    simpa only [(shape i).1,(shape i).2] using input i
  have tables i : ∀j : Key z (2^W) k,(v.shelf i).Prepared S depth (fixture i) j (frozen i) := by
    change ∀j : Key z (2^W) k,(market i).shelf.Prepared S depth (fixture i) j (frozen i)
    simpa only [(shape i).1,(shape i).2] using static i
  have archived i : ∀r : Fin (count z (2^W) k*paths z S.degree depth),output (v.flagBase i+r.val)=if mode i=3 then
      (v.shelf i).result S k depth (frozen i) ((v.shelf i).flagsBase S z (2^W) k depth+r.val) else 0 := by
    have read : ∀r : Fin (market i).rows,output ((repair C (atDate i)).purchaseOut+r.val)=if mode i=3 then
      (market i).shelf.result (market i).sampler k (market i).depth (frozen i) ((market i).flags+r.val) else 0 := flags i
    intro r
    have rowsAt : (market i).rows=count z (2^W) k*paths z S.degree depth := by
      simp only [Market.rows,(shape i).1,(shape i).2]
    have actual := read ⟨r.val,r.isLt.trans_le rowsAt.ge⟩
    change output ((repair C (atDate i)).purchaseOut+r.val)=if mode i=3 then
      (market i).shelf.result S k depth (frozen i) ((market i).shelf.flagsBase S z (2^W) k depth+r.val) else 0
    simpa only [Market.flags,(shape i).1,(shape i).2] using actual
  constructor
  · exact v.active_original S π depth marks output (fun i=>(market i).phase) (fun i=>(market i).temperature)
      (fun i=>(market i).kind) mode frozen fixture (fun i ok=>Shelf.catalogueMarks_buy _ _ _ _ _ _ ok)
      inputs tables room archived ROM hEvents j
  · rintro ⟨path,rfl⟩
    exact (v.original_active S π depth 0 0 0 output (fun i=>(market i).phase) (fun i=>(market i).temperature)
      (fun i=>(market i).kind) mode frozen fixture inputs tables room archived ROM hEvents path).2

end
end Hierarchy.ProtocolRAM.BoughtSockets

end OAI
