import OAI.Computability.BorderVNP.TeamSiteTimedRegular

/-! # Ordinary RAM callbacks in the clocked team interpreter -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor

open VPVNP BurstRAM RAMTape TeamPrivateFragment TeamSite.Work
open RAMSerialization (WordRecord)
open TeamEventRecords (physicalSlots)
open private ordinary_budget slots_empty encode_negative from OAI.Computability.BorderVNP.TeamSiteCallback

variable {w H p r k a m g : ℕ} {hw : 2 ≤ w+1} {Q Γ : Type}

/-- Every signed continuation, binary guess and ordinary memory action executes
entirely on the regular loop portion and produces its prescribed record suffix.
This uses no bound on any private tape program. -/
theorem ordinary_callback (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (mark : Fin a → Γ) (M : TeamOpcode.Macros w a) (fuel : ℕ)
    (sg : Option Bool) (out : TeamOpcode.Exit p r a) (bank : PrivateRAM.LogConfig w p r)
    (e : TeamRAM.Event w) (next : TeamOpcode.State w p r) (win : Window w) (tick : Word w)
    (pub : Fin k → Word w) {rs : List (WordRecord (w+1))} {s : Stacks (Port r k ((m+1)*g))}
    (work : Ready hw H rs s) (clock : s ∘ Port.clock = win.callbackBank pub bank.reg tick)
    (ordinary : ∀ j addr len pc, out ≠ .call j addr len pc)
    (action : (out.action M bank).action = some e.action)
    (advance : (out.action M bank).advance e.choices e.old = some (next,e.sign))
    (free : rs.length+2*e.old.length ≤ 4*H) (suffix : List Bool) :
    ∃ t b, t ≤ eventBudget w m g fuel e.action.extra ∧
      StackRuns (replay (regular P lib mark)) t
        (.clock sg (.exit (.callback out)),eventBits e ++ suffix) s
        (Loop.resume (Loop.times sg (signBit e.sign)) next.pc,suffix) b ∧
      Ready hw H (rs++physicalSlots tick.val e) b ∧ b ∘ Port.clock = win.callbackBank pub next.reg tick := by
  simp only [eventBits,List.append_assoc]
  rcases e with ⟨ac,vs,bits,weight⟩
  have simpleTime : 1 ≤ eventBudget w m g fuel 0 := le_trans (by omega) (ordinary_budget w m g fuel)
  cases out with
  | sign negative pc =>
    change some (.ordinary none) = some ac at action
    cases action
    cases bits <;> cases vs <;> try contradiction
    change some (⟨pc,bank.reg⟩, if negative then .minus else .plus) = some (next,weight) at advance
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
    simp only [slots_empty,List.append_nil,encode_negative]
    exact ⟨1,s,simpleTime,.cons (.goto rfl) (.nil ..),work,clock⟩
  | native cb =>
    cases cb with
    | accept | reject | returnState => contradiction
    | next pc =>
      change some (.ordinary none) = some ac at action
      cases action
      cases bits <;> cases vs <;> try contradiction
      change some (⟨pc,bank.reg⟩,.plus) = some (next,weight) at advance
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
      simp only [slots_empty,List.append_nil,times_plus]
      exact ⟨1,s,simpleTime,.cons (.goto rfl) (.nil ..),work,clock⟩
    | choose yes no =>
      change some (.ordinary none) = some ac at action
      cases action
      rcases bits with _ | ⟨b,_ | ⟨_,tail⟩⟩ <;> cases vs <;> try contradiction
      change some (⟨if b then yes else no,bank.reg⟩,.plus) = some (next,weight) at advance
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
      simp only [slots_empty,List.append_nil,times_plus]
      exact ⟨1,s,simpleTime,by cases b <;> exact .cons (.goto rfl) (.nil ..),work,clock⟩
    | read dst addr pc =>
      change some (.ordinary (some ((bank.reg addr).val,none))) = some ac at action
      cases action
      cases bits <;> rcases vs with _ | ⟨v,_ | ⟨_,tail⟩⟩ <;> try contradiction
      change some (⟨pc, Function.update bank.reg dst v⟩,.plus) = some (next,weight) at advance
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
      obtain ⟨t,b,ht,run,ready,bank'⟩ := regular_memory P lib mark sg pc (.load dst addr) v suffix work pub
        ⟨pc,bank.reg⟩ (TeamTapeHandoff.chargeRegisters win.block win.global win.elapsed 0) tick win.cap clock
        (by simpa using free)
      rw [show TeamMemoryCallback.pair (.load dst addr) bank.reg tick v = _ from
        TeamEventRecords.ordinary_slots (.load dst addr) bank.reg tick v [] .plus] at ready
      simp only [times_plus]
      exact ⟨t,b,ht.trans (ordinary_budget ..),by simpa [TeamBurstProbe.choices,memoryExit] using run,ready,bank'⟩
    | write addr src pc =>
      change some (.ordinary (some ((bank.reg addr).val,some (bank.reg src)))) = some ac at action
      cases action
      cases bits <;> rcases vs with _ | ⟨v,_ | ⟨_,tail⟩⟩ <;> try contradiction
      change some (⟨pc,bank.reg⟩,.plus) = some (next,weight) at advance
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
      obtain ⟨t,b,ht,run,ready,bank'⟩ := regular_memory P lib mark sg pc (.store addr src) v suffix work pub
        ⟨pc,bank.reg⟩ (TeamTapeHandoff.chargeRegisters win.block win.global win.elapsed 0) tick win.cap clock
        (by simpa using free)
      rw [show TeamMemoryCallback.pair (.store addr src) bank.reg tick v = _ from
        TeamEventRecords.ordinary_slots (.store addr src) bank.reg tick v [] .plus] at ready
      simp only [times_plus]
      exact ⟨t,b,ht.trans (ordinary_budget ..),by simpa [TeamBurstProbe.choices,memoryExit] using run,ready,bank'⟩
  | call j addr len pc => exact (ordinary j addr len pc rfl).elim

end TeamSite.TimedProcessor

end BorderVNP
end Computability
end OAI
