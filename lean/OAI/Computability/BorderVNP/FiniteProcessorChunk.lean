import OAI.Computability.BorderVNP.FiniteProcessorCallback
import OAI.Computability.BorderVNP.TeamSiteChunkRun

/-! # Chronological finite-field instruction blocks

The physical guarded fetch, exact callback and timestamp reset realize every
source event in its original time. The whole chunk reads its recorded private
choices and carries the product of field adjustments to its exit.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamPrivateFragment TeamTapeHandoff
open BurstRAM (Word wordBits)
open RAMSerialization (WordRecord)
open TeamRAM (Event)
open TeamEventRecords (physicalSlots)
open private charged_result old_length_le from OAI.Computability.BorderVNP.TeamSiteRun

variable {Q Γ : Type} {p r k a m g w H : ℕ} {F : Type*} [Field F] [Fintype F] {hw : 2 ≤ w+1}

/-- One full charged native instruction, with no hidden choices in dispatch or reset.
The output is ready for any subsequent instruction on the same bank. -/
theorem event_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (fuel : ℕ) (weights : Returns Q Γ F m a) (acc : F)
    (pub : Fin k → Word w) (s next : TeamOpcode.State w p r) (c : Window w) (sg : Option Bool)
    (e : Event w) (rs : List (WordRecord (w+1))) (base : Stacks (Port r k (m*g))) (rest : List Bool)
    (safe : c.Safe) (fits : c.Fits e.action.extra) (cap : e.action.extra ≤ c.cap.val)
    (act : (P.fetch pub (fun j => (lib j).eval fuel) s).action = some e.action)
    (go : (P.fetch pub (fun j => (lib j).eval fuel) s).advance e.choices e.old = some (next,e.sign))
    (clock : base ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs base)
    (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ n out, n ≤ instructionBudget w m g fuel e.action.extra ∧
      StackRuns (replay (loopCode P lib weights)) n ((.clock sg (.enter s.pc),Fintype.equivFin F acc),eventBits e++rest) base
        ((.clock (Loop.times sg (signBit e.sign)) (.enter next.pc),Fintype.equivFin F (acc*eventAdjustment lib weights fuel (TeamOpcode.prepare P pub s).1 e)),rest) out ∧
      Work.Ready hw H (rs++physicalSlots (c.elapsed.val+1) e) out ∧
      out ∘ Port.clock = (c.charge e.action.extra).bank pub next ∧
      (rs++physicalSlots (c.elapsed.val+1) e).length + 2*(c.charge e.action.extra).block.val ≤ 4*H := by
  let M : TeamOpcode.Macros w a := fun j => (lib j).eval fuel
  let prep := TeamOpcode.prepare P pub s
  let win := c.charge e.action.extra
  let ticks := c.first
  let cb := win.callbackBank pub prep.2.reg ticks
  let mid := installStacks Port.clock base cb
  have cr := charged_result P pub M s c e act cap fits
  obtain ⟨n,hn,guard⟩ := clock_run P lib weights sg acc pub s c.block c.global c.elapsed c.cap safe base clock (eventBits e++rest)
  rw [cr] at guard
  have cm : mid ∘ Port.clock = cb := funext fun u => installStacks_at (fun _ _ he => Port.clock.inj he) ..
  rw [← TeamOpcode.prepare_action] at act go
  have first := c.first_val safe fits
  obtain ⟨hblock,_,htime,hs⟩ := c.charged_values e.action.extra safe fits
  have tickBound : ticks.val+e.action.extra ≤ 2^w := by
    have he := (c.charge e.action.extra).elapsed.isLt
    change c.first.val + _ ≤ _; rw [first]; omega
  have count := old_length_le _ _ _ act go
  have room := fits.1
  obtain ⟨t,b,ht,callback,hr,cbank⟩ := callback_run P lib fuel weights acc sg prep.1 prep.2 e next win ticks pub
    (ready.installClock cb) cm act go cap tickBound (by omega) rest
  have reset := reset_run P lib weights (Loop.times sg (signBit e.sign)) (acc*eventAdjustment lib weights fuel prep.1 e) next.pc b rest
  have tickLen : (b (.clock .stamp)).length = w := (congrArg List.length (congrFun cbank .stamp)).trans (BurstRAM.length_wordBits _)
  rw [tickLen] at reset
  rw [show ticks.val = c.elapsed.val+1 from first] at hr
  refine ⟨_,_,Nat.add_le_add_right (Nat.add_le_add hn ht) _, (guard.trans callback).trans reset,hr.reset,
    reset_clock win pub next ticks b cbank,?_⟩
  rw [List.length_append,hblock]
  have hlen := slots_length_le (c.elapsed.val+1) e
  omega

/-- The complete chronological native block replays from the actual register, countdown
and record bank. Every subsequent continuation receives the untouched suffix of choice
bits and the unmodified order of the accumulated typed sorter slots. -/
theorem chunk_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (fuel : ℕ) (weights : Returns Q Γ F m a) (pub : Fin k → Word w) {s last : TeamOpcode.State w p r} {c fin : Window w}
    {es : List (Event w)} (chunk : Chunk (P.fetch pub (fun j => (lib j).eval fuel)) s c es last fin)
    (sg : Option Bool) (acc : F) (rs : List (WordRecord (w+1))) (base : Stacks (Port r k (m*g))) (rest : List Bool)
    (safe : c.Safe) (clock : base ∘ Port.clock = c.bank pub s) (ready : Work.Ready hw H rs base)
    (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ n out, n ≤ Work.chunkBudget w m g fuel es ∧
      StackRuns (replay (loopCode P lib weights)) n ((.clock sg (.enter s.pc),Fintype.equivFin F acc),chunkBits es++rest) base
        ((.clock (chunkSign sg es) (.enter last.pc),Fintype.equivFin F (acc*foldEvents P pub lib fuel (eventAdjustment lib weights fuel) s es)),rest) out ∧
      Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) out ∧
      out ∘ Port.clock = fin.bank pub last ∧
      (rs++chunkSlots (c.elapsed.val+1) es).length + 2*fin.block.val ≤ 4*H := by
  induction chunk generalizing sg acc rs base with
  | nil =>
    simp only [foldEvents,mul_one]
    refine ⟨0,base,le_rfl,.nil ..,?_,clock,?_⟩ <;> simpa only [chunkSlots,TeamEventRecords.historySlots,List.append_nil]
  | @cons s c e next es last fin act go fits cap later ih =>
    obtain ⟨n,b,hn,first,hb,cb,room⟩ := event_run P lib fuel weights acc pub s next c sg e rs base
      (chunkBits es++rest) safe fits cap act go clock ready space
    obtain ⟨_,_,time,hs⟩ := c.charged_values e.action.extra safe fits
    obtain ⟨t,out,ht,tail,ready',bank',space'⟩ := ih (Loop.times sg (signBit e.sign)) (acc*eventAdjustment lib weights fuel (TeamOpcode.prepare P pub s).1 e) _ b hs cb hb room
    have hgo : (P.fetch pub (TeamSiteEvents.macros lib fuel) s).advance e.choices e.old = some (next,e.sign) := go
    have stamp : (c.charge e.action.extra).elapsed.val + 1 = c.elapsed.val+1+(1+e.action.extra) := by omega
    refine ⟨n+t,out,Nat.add_le_add hn ht,?_,?_,bank',?_⟩
    · simpa only [chunkBits, List.flatMap_cons, List.append_assoc, chunkSign,List.foldl_cons,foldEvents,hgo,mul_assoc] using first.trans tail
    · simpa only [chunkSlots,TeamEventRecords.historySlots, stamp, List.append_assoc] using ready'
    · simpa only [chunkSlots,TeamEventRecords.historySlots, stamp, List.append_assoc] using space'

end FieldProcessor

end BorderVNP
end Computability
end OAI
