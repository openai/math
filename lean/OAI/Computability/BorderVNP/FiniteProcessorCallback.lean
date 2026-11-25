import OAI.Computability.BorderVNP.FiniteProcessorLoopPrivate

/-! # All finite-field callbacks of the actual validator

An enabled callback updates the processor by the native field correction for the
resolved opcode. The words, choices, records and signed continuation coincide
with the original physical instruction.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP BurstRAM RAMTape TeamSite TeamSite.Work TeamPrivateFragment
open RAMSerialization (WordRecord)
open TeamEventRecords (physicalSlots)
open private callback from OAI.Computability.BorderVNP.TeamSiteLoop
open private ordinary_budget burst_budget slots_empty encode_negative from OAI.Computability.BorderVNP.TeamSiteCallback

variable {Q Γ : Type} {p r k a m g w H : ℕ} {F : Type*} [Field F] [Fintype F] {hw : 2 ≤ w+1}

private theorem choose_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (weights : Returns Q Γ F m a)
    (sg : Option Bool) (acc : F) (yes no : Fin p) (b : Bool) (rest : List Bool) (s : Stacks (Port r k (m*g))) :
    StackRuns (replay (loopCode P lib weights)) 1
      ((.clock sg (.exit (.callback (.native (.choose yes no)))),Fintype.equivFin F acc),b::rest) s
      ((Loop.resume sg (if b then yes else no),Fintype.equivFin F acc),rest) s := by
  cases b <;> apply StackRuns.cons _ (StackRuns.nil ..) <;> exact .goto (by
    simp [replay,loopCode,FieldStack.productCode,Loop.code,loopFactor,callback,StackOp.rename])

/-- Every successful RAM event replays on the real charged site with exactly its
old-word and native choices. Its canonical records are appended, the native
successor registers are committed, and its path contribution multiplies the
site sign before the next instruction is entered. -/
theorem callback_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (fuel : ℕ)
    (weights : Returns Q Γ F m a) (acc : F) (sg : Option Bool) (out : TeamOpcode.Exit p r a) (bank : PrivateRAM.LogConfig w p r)
    (e : TeamRAM.Event w) (next : TeamOpcode.State w p r) (win : Window w) (tick : Word w)
    (pub : Fin k → Word w) {rs : List (WordRecord (w+1))} {s : Stacks (Port r k (m*g))}
    (work : Ready hw H rs s) (clock : s ∘ Port.clock = win.callbackBank pub bank.reg tick)
    (action : (out.action (fun j => (lib j).eval fuel) bank).action = some e.action)
    (advance : (out.action (fun j => (lib j).eval fuel) bank).advance e.choices e.old = some (next,e.sign))
    (cap : e.action.extra ≤ win.cap.val) (time : tick.val+e.action.extra ≤ 2^w)
    (free : rs.length+2*e.old.length ≤ 4*H) (suffix : List Bool) :
    ∃ t b, t ≤ eventBudget w m g fuel e.action.extra ∧
      StackRuns (replay (loopCode P lib weights)) t
        ((.clock sg (.exit (.callback out)),Fintype.equivFin F acc),eventBits e ++ suffix) s
        ((Loop.resume (Loop.times sg (signBit e.sign)) next.pc,Fintype.equivFin F (acc*eventAdjustment lib weights fuel out e)),suffix) b ∧
      Ready hw H (rs++physicalSlots tick.val e) b ∧ b ∘ Port.clock = win.callbackBank pub next.reg tick := by
  simp only [eventBits,List.append_assoc]
  rcases e with ⟨ac,vs,bits,weight⟩
  have simpleTime : 1 ≤ eventBudget w m g fuel 0 := le_trans (by omega) (ordinary_budget w m g fuel)
  have regs (i) : s (isa (.reg i)) = wordBits (bank.reg i) := congrFun clock (.isa (.reg i))
  have st : s (.clock .stamp) = wordBits tick := congrFun clock .stamp
  have max : s (.clock .maxBurst) = wordBits win.cap := congrFun clock .maxBurst
  cases out with
  | sign negative pc =>
    change some (.ordinary none) = some ac at action
    cases action
    cases bits <;> cases vs <;> try contradiction
    change some (⟨pc,bank.reg⟩, if negative then .minus else .plus) = some (next,weight) at advance
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
    simp only [eventAdjustment,mul_one,slots_empty,List.append_nil,encode_negative]
    exact ⟨1,s,simpleTime,.cons (.goto (by simp [replay,loopCode,FieldStack.productCode,Loop.code,loopFactor,callback,StackOp.rename,TeamBurstProbe.choices])) (.nil ..),work,clock⟩
  | native cb =>
    cases cb with
    | accept | reject | returnState => contradiction
    | next pc =>
      change some (.ordinary none) = some ac at action
      cases action
      cases bits <;> cases vs <;> try contradiction
      change some (⟨pc,bank.reg⟩,.plus) = some (next,weight) at advance
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
      simp only [eventAdjustment,mul_one,slots_empty,List.append_nil,times_plus]
      exact ⟨1,s,simpleTime,.cons (.goto (by simp [replay,loopCode,FieldStack.productCode,Loop.code,loopFactor,callback,StackOp.rename,TeamBurstProbe.choices])) (.nil ..),work,clock⟩
    | choose yes no =>
      change some (.ordinary none) = some ac at action
      cases action
      rcases bits with _ | ⟨b,_ | ⟨_,tail⟩⟩ <;> cases vs <;> try contradiction
      change some (⟨if b then yes else no,bank.reg⟩,.plus) = some (next,weight) at advance
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
      simp only [eventAdjustment,mul_one,slots_empty,List.append_nil,times_plus]
      exact ⟨1,s,simpleTime,choose_run P lib weights sg acc yes no b suffix s,work,clock⟩
    | read dst addr pc =>
      change some (.ordinary (some ((bank.reg addr).val,none))) = some ac at action
      cases action
      cases bits <;> rcases vs with _ | ⟨v,_ | ⟨_,tail⟩⟩ <;> try contradiction
      change some (⟨pc, Function.update bank.reg dst v⟩,.plus) = some (next,weight) at advance
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
      obtain ⟨t,b,ht,run,ready,bank'⟩ := memory_run P lib weights sg acc pc (.load dst addr) v suffix work pub
        ⟨pc,bank.reg⟩ (TeamTapeHandoff.chargeRegisters win.block win.global win.elapsed 0) tick win.cap clock
        (by simpa using free)
      rw [show TeamMemoryCallback.pair (.load dst addr) bank.reg tick v = _ from
        TeamEventRecords.ordinary_slots (.load dst addr) bank.reg tick v [] .plus] at ready
      simp only [eventAdjustment,mul_one,times_plus]
      exact ⟨t,b,ht.trans (ordinary_budget ..),by simpa [TeamBurstProbe.choices,memoryExit] using run,ready,bank'⟩
    | write addr src pc =>
      change some (.ordinary (some ((bank.reg addr).val,some (bank.reg src)))) = some ac at action
      cases action
      cases bits <;> rcases vs with _ | ⟨v,_ | ⟨_,tail⟩⟩ <;> try contradiction
      change some (⟨pc,bank.reg⟩,.plus) = some (next,weight) at advance
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj advance)
      obtain ⟨t,b,ht,run,ready,bank'⟩ := memory_run P lib weights sg acc pc (.store addr src) v suffix work pub
        ⟨pc,bank.reg⟩ (TeamTapeHandoff.chargeRegisters win.block win.global win.elapsed 0) tick win.cap clock
        (by simpa using free)
      rw [show TeamMemoryCallback.pair (.store addr src) bank.reg tick v = _ from
        TeamEventRecords.ordinary_slots (.store addr src) bank.reg tick v [] .plus] at ready
      simp only [eventAdjustment,mul_one,times_plus]
      exact ⟨t,b,ht.trans (ordinary_budget ..),by simpa [TeamBurstProbe.choices,memoryExit] using run,ready,bank'⟩
  | call j addr len pc =>
    change (if (bank.reg addr).val+(bank.reg len).val ≤ 2^w
      then some (.burst (bank.reg addr).val (bank.reg len).val) else none) = some ac at action
    split at action <;> try contradiction
    rename_i legal
    obtain rfl := Option.some.inj action
    change (if vs.length = (bank.reg len).val then ((lib j).eval fuel vs bits).map
      (fun z => (⟨pc,bank.reg⟩,z)) else none) = some (next,weight) at advance
    split at advance <;> try contradiction
    rename_i length
    obtain ⟨z,he,eq⟩ := Option.map_eq_some_iff.mp advance
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj eq
    obtain ⟨n,hn,sign,u,native,rfl⟩ := ((lib j).eval_iff ..).mp he
    have range : (bank.reg addr).val+vs.length ≤ 2^w := length.symm ▸ legal
    have ticks : tick.val+vs.length ≤ 2^w := length.symm ▸ time
    obtain ⟨t,b,ht,run,ready,bank'⟩ := loop_private_run P lib weights acc sg j addr len pc work (bank.reg addr)
      (bank.reg len) tick win.cap (regs addr) (regs len) st max ⟨cap,legal⟩ (length ▸ free)
      vs length native fuel hn suffix
    have eqSlots := TeamEventRecords.burst_slots (bank.reg addr) tick vs bits (TeamPrivateCall.sign sign) range ticks
    rw [length] at eqSlots
    rw [eqSlots] at ready
    rw [length] at ht
    simp only [eventAdjustment,returned,signBit_sign]
    exact ⟨_,_,ht.trans (burst_budget _ _ _ _ _ _ hn.le),run,ready,bank'.trans clock⟩

end FieldProcessor

end BorderVNP
end Computability
end OAI
