import OAI.Computability.BorderVNP.TeamSiteTimedEvent
import OAI.Computability.BorderVNP.TeamSiteTimedStop
import OAI.Computability.BorderVNP.TeamSiteInverse

/-! # Exact full-loop replay of the timed site on every physical choice supply -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP RAMTape BurstRAM TeamPrivateFragment TeamSiteEvents TeamSiteChoices SupplyRun
open RAMSerialization (WordRecord)
variable {Q Γ : Type} {w p r k a m g H : ℕ} {hw : 2 ≤ w+1}
local notation "FullBank" => Stacks (TeamClocked.Port (Layout.Port r k ((m+1)*g)))

/-- Every typed charged chunk executes on the installed time-limited physical processor.
The restored template suffices for the next burst, even after a zero-weight timeout. -/
theorem chunk_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ)
    (N : ℕ) (pub : Fin k → Word w) (last : Bool) {s z : TeamOpcode.State w p r} {c fin : Window w}
    {es : List (TeamRAM.Event w)} (chunk : Chunk (P.fetch pub (fun j => (lib j).timedEval (mark j) N)) s c es z fin)
    (sg : Option Bool) (rs : List (WordRecord (w+1))) (base : FullBank) (rest : List Bool)
    (safe : c.Safe) (clock : base ∘ loopPort ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs (base ∘ loopPort))
    (meter : MeterReady base N) (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ t out, t ≤ Work.chunkBudget w m g (N+1) es + TimedBudget.calls (TimedBudget.meterCoefficient m g) N es ∧
      StackRuns (replay (code P lib mark)) t (loopLabel last (.clock sg (.enter s.pc)),chunkBits es++rest) base
        (loopLabel last (.clock (chunkSign sg es) (.enter z.pc)),rest) out ∧
      Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) (out ∘ loopPort) ∧
      out ∘ loopPort ∘ Port.clock = fin.bank pub z ∧
      (rs++chunkSlots (c.elapsed.val+1) es).length+2*fin.block.val ≤ 4*H ∧ Framed base out := by
  induction chunk generalizing sg rs base with
  | nil =>
    refine ⟨0,base,by simp [TimedBudget.calls],.nil ..,?_,clock,?_,Framed.refl base⟩ <;>
      simpa only [chunkSlots,TeamEventRecords.historySlots,List.append_nil]
  | @cons s c e next es z fin act go fits cap later ih =>
    obtain ⟨t,mid,ht,first,wr,cb,room,fr⟩ := event_run P lib mark N pub last s next c sg e rs base
      (chunkBits es++rest) safe fits cap act go clock ready meter space
    obtain ⟨_,_,time,hs⟩ := c.charged_values e.action.extra safe fits
    obtain ⟨u,out,hu,path,wr',cb',room',fr'⟩ := ih (Loop.times sg (signBit e.sign)) _ mid hs cb wr (fr.meter meter) room
    have stamp : (c.charge e.action.extra).elapsed.val+1 = c.elapsed.val+1+(1+e.action.extra) := by omega
    refine ⟨t+u,out,?_,?_,?_,cb',?_,fr.trans fr'⟩
    · simp only [Work.chunkBudget_cons,TimedBudget.calls,List.map_cons,List.sum_cons] at hu ⊢
      omega
    · simpa only [chunkBits,List.flatMap_cons,List.append_assoc,chunkSign,List.foldl_cons] using first.trans path
    · simpa only [chunkSlots,TeamEventRecords.historySlots,stamp,List.append_assoc] using wr'
    · simpa only [chunkSlots,TeamEventRecords.historySlots,stamp,List.append_assoc] using room'

/-- A complete accepting or deferred native chunk reaches precisely the designated
physical local close with its canonical final bank, at the timed-site budget. -/
theorem close_complete (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ) (N : ℕ) (last : Bool)
    {s z : TeamOpcode.State w p r} {c fin : Window w} {es : List (TeamRAM.Event w)}
    (chunk : Chunk (P.fetch pub (fun j => (lib j).timedEval (mark j) N)) s c es z fin)
    (live : Option (Fin p)) (closed : Closed P pub z fin live)
    (sg : Option Bool) (rs : List (WordRecord (w+1))) (base : FullBank) (rest : List Bool)
    (safe : c.Safe) (clock : base ∘ loopPort ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs (base ∘ loopPort))
    (meter : MeterReady base N) (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ t out, t ≤ TimedBudget.body m g (TimedBudget.meterCoefficient m g) N es ∧
      StackRuns (replay (code P lib mark)) t (loopLabel last (.clock sg (.enter s.pc)),chunkBits es++rest) base
        (loopLabel last (.close (chunkSign sg es) live),rest) out ∧
      Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) (out ∘ loopPort) ∧
      out ∘ loopPort ∘ Port.clock = fin.bank pub z ∧ Framed base out := by
  obtain ⟨t,mid,ht,run,wr,cb,_,fr⟩ := chunk_run P lib mark N pub last chunk sg rs base rest safe clock ready meter space
  let sup : Supply := fun _ => false
  have hfin := (chunk.clock safe).2.2.1
  rcases closed with ⟨rfl,h⟩ | ⟨rfl,h⟩
  · obtain ⟨u,q,b,hu,endRun,qeq,beq⟩ := stop_run P lib mark pub N z fin sup .accepted (.accept h) last
      (chunkSign sg es) _ mid rest hfin cb wr
    have same := beq (by decide)
    subst b
    change q = _ at qeq
    subst q
    refine ⟨t+u,mid,?_,run.trans endRun,wr,cb,fr⟩
    unfold TimedBudget.body Processor.Row.nativeCost; omega
  · obtain ⟨u,q,b,hu,endRun,qeq,beq⟩ := stop_run P lib mark pub N z fin sup .handoff (.handoff h) last
      (chunkSign sg es) _ mid rest hfin cb wr
    have same := beq (by decide)
    subst b
    change q = _ at qeq
    subst q
    refine ⟨t+u,mid,?_,run.trans endRun,wr,cb,fr⟩
    unfold TimedBudget.body Processor.Row.nativeCost; omega

/-- On every branch supply, the true processor has a complete finite block path.
No termination assumption is made on the unmetered private program. Accepted and
deferred paths expose the actual canonical records and registers; rejection reaches
the genuine pre-sort zero terminal. -/
theorem supplied_run (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (lib : Fin a → Macro Q Γ m g) (mark : Fin a → Γ) (hm : ∀ j, (lib j).alphabet.blank ≠ mark j)
    (N : ℕ) (last : Bool) (s : TeamOpcode.State w p r) (c : Window w) (u : Supply)
    (sg : Option Bool) (rs : List (WordRecord (w+1))) (base : FullBank) (suffix : List Bool)
    (safe : c.Safe) (clock : base ∘ loopPort ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs (base ∘ loopPort))
    (meter : MeterReady base N) (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ es z fin v, Chunk (P.fetch pub (fun j => (lib j).timedEval (mark j) N)) s c es z fin ∧
      Prefix u (chunkBits es) ∧ SupplyRun.Run P pub (fun j => TimedSupply.shadow N (lib j)) (N+1)
        z fin (drop u (chunkBits es).length) [] z fin v ∧
      ∃ t q out, t ≤ TimedBudget.body m g (TimedBudget.meterCoefficient m g) N es ∧
        StackRuns (replay (code P lib mark)) t (loopLabel last (.clock sg (.enter s.pc)),chunkBits es++suffix) base
          (q,suffix) out ∧ outcome P lib mark last (chunkSign sg es) z.pc q v ∧ (v ≠ .reject →
        Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) (out ∘ loopPort) ∧
        out ∘ loopPort ∘ Port.clock = fin.bank pub z ∧ Framed base out) := by
  obtain ⟨es,z,fin,v,ch,pre,h⟩ := TimedSupply.exists_history P pub lib mark hm N s c u safe
  obtain ⟨t,mid,ht,run,wr,cb,_,fr⟩ := chunk_run P lib mark N pub last ch sg rs base suffix safe clock ready meter space
  obtain ⟨u',q,out,hu,endRun,ok,eq⟩ := stop_run P lib mark pub N z fin _ v h last (chunkSign sg es) _ mid suffix
    (ch.clock safe).2.2.1 cb wr
  refine ⟨es,z,fin,v,ch,pre,h,t+u',q,out,?_,run.trans endRun,ok,fun hgood => eq hgood ▸ ⟨wr,cb,fr⟩⟩
  unfold TimedBudget.body Processor.Row.nativeCost; omega

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
