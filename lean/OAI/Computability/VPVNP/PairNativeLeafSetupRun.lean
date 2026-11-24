import OAI.Computability.VPVNP.PairNativeLeafSetupTable
import OAI.Computability.VPVNP.PairNativeCachePaper
import OAI.Computability.VPVNP.PairNativeFrameLeaf
import OAI.Computability.VPVNP.PairSimulationLeafImagePreparation

/-! # Native geometry and auxiliary-counter cache in the same vertex burst

The true eleven pair operands and the six terminal header reads determine
both regions. The geometry pointer and all twelve fields survive the cache
writes. Every path then continues from the same private configuration and
with the entire supplied choice tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeLeafSetup

open BurstRAM PrivateRAM LiveProgram PrimedInputRAM PrimedStackRAM PrimedCounter.GuessWord NativeOperands
open CursorNetwork CursorRouting LeafSourceLoad LeafRegisterBank
open scoped Fin.CommRing

attribute [local irreducible] NativeOperands.capacity NativeOperands.saved

variable {c : Constants} {r pcs : ℕ} (K : Block c r)
  {p : UniversalMachine.Program} {B n H : ℕ} {i : Fin (2^(n^c.chainPower-1))}
  (Q : Layout (CounterPublic.spec p c |>.lengths n i) n (addressWidth B n) H (CursorBounds.wordBits B n))
  (D : PrimedCounter.Data Q (n^(c.circuitExponent+5)))

local notation "w" => CursorBounds.wordBits B n
local notation "d" => CursorBounds.virtualBits B n
local notation "e" => roundedUp 1 4 n
local notation "geom" => AssemblerPublic.geometry B n H

theorem paper_run (hb : 0 < K.denominator) (hB : 1 ≤ B) (hn : 3 ≤ n)
    (hH : H = 2^roundedUp K.numerator K.denominator n)
    (fit : PairNativeGeometry.Fits K.numerator K.denominator n w)
    (hp : Q.program = p) (hbase : Q.scratchBase = 2^d) (hf : D.Fits) (hroot : D.root.val = 0)
    (hw : 2 ≤ w) (hc : 2^d*2^e < 2^w)
    (M : Machine w pcs r 11)
    (hpub : M.publicData = Pieces.word geom (CounterPublic.actualPrefix p) ∘ StageOperands.pair c)
    (pc : Fin (size K) → Fin pcs) (ret : Instr 2 pcs r 11)
    (rows : ∀ j, M.code (pc j) = (row K pc ret j).resize w)
    (m : Memory w) (st : Config w pcs r) (start : st.pc = pc (entry K))
    (before : (M.publicData 6).val < NativeFrame.frameBase
      (NativeFrame.fromHeader K.degree M.publicData (st.reg K.frame.header) m))
    (room : (NativeFrame.fromHeader K.degree M.publicData (st.reg K.frame.header) m).cacheBase+38 ≤ 2^w) :
    let A := NativeFrame.fromHeader K.degree M.publicData (st.reg K.frame.header) m
    let G := NativeFrame.frameBase A
    let header := st.reg K.frame.header
    let role := st.reg K.frame.role
    ∃ ticks ≤ work (NativeCache.args c) K.numerator K.denominator geom+76, ∃ out : Config w pcs r,
      out.pc = pc (done K) ∧ out.persistent = st.persistent ∧ out.reg K.frame.hist = (A.histBase : Word w) ∧
      LeafGeometryLoad.Stored (M.publicData 6).val G out.privateMem (NativeFrame.leafWords K.degree M.publicData header role m) ∧
      (∀ j : Fin 12, out.privateMem ((G+j.val : ℕ) : Word w) = NativeFrame.fields K.degree M.publicData header role m j) ∧
      Cached A.cacheBase out.privateMem (LeafVisit.cacheWords D d e) ∧
      (∀ a : Word w, a ≠ M.publicData 6 → (a.val < G ∨ G+12 ≤ a.val) →
        (a.val < A.cacheBase ∨ A.cacheBase+38 ≤ a.val) → out.privateMem a = st.privateMem a) ∧
      (∀ j, j ∉ Set.range K.frame.work → j ≠ K.frame.hist → j ∉ Set.range K.cache → out.reg j = st.reg j) ∧
      ∀ fuel bits, execute M.program (fuel+ticks+K.degree+142) st m bits =
        (execute M.program fuel out m bits).map
          (Flow.prependEvents (NativeFrame.events K.degree header m ++ List.replicate (ticks+1) .tick)) := by
  intro A G header role
  have pubN : (M.publicData 6).val = n := by
    rw [hpub]
    exact Nat.mod_eq_of_lt (PrimedInputRAM.Opcodes.pubNat_lt Q hf.assembler 1)
  have cacheEq : A.cacheBase = G + n^5 := by
    change G + (M.publicData 6).val^5 = _
    rw [pubN]
  have sep : G+12 ≤ A.cacheBase := by
    have pos : 3^5 ≤ n^5 := Nat.pow_le_pow_left hn _
    omega
  have frows j : M.code ((pc ∘ framePC K) j) =
      (K.frame.row K.degree (pc ∘ framePC K) (handoff K pc) j).resize w := by
    rw [Function.comp_apply,rows,frame_row]
  obtain ⟨mid, stop, installed, run⟩ := NativeFrame.run K.frame K.degree M (pc ∘ framePC K)
    (handoff K pc) frows m st start before (by change G+12 ≤ _; change A.cacheBase+38 ≤ _ at room; omega)
  let next : Config w pcs r := {mid with pc := pc (cacheEntry K)}
  have jump : M.program.step mid = .localStep next := by
    change (M.code mid.pc).run M.publicData mid = _
    rw [stop, frows]
    change ((NativeFrame.Table.row (frameFlow K) _ _ _ _ _ _).resize w).run M.publicData mid = _
    rw [NativeFrame.Table.at_done]
    simp only [handoff,Instr.resize,Instr.run,ite_self,next]
  have crows j : M.code ((pc ∘ cachePC K) j) =
      (NativeCacheTable.row (cacheFlow K) (NativeCache.storeSrc c K.cache) (NativeCache.ptr c K.cache)
        (NativeCache.one c K.cache) (pc ∘ cachePC K) ret j).resize w := by
    rw [Function.comp_apply,rows,cache_row]
  have vd : 0 < d := (Nat.mul_pos (show 0 < B by omega)
    (Nat.clog_pos (by decide : 1 < 2) (show 1 < n by omega))).trans_le (CursorBounds.addressBits_le_virtualBits B n hn)
  let v : Position d := (⟨0,vd⟩,0)
  let buf : Buffers d (2^e) w := fun _ _ => false
  have cachePort : next.reg (K.cache (saved (NativeCache.args c))) = (A.cacheBase : Word w) := by
    change mid.reg _ = _
    rw [← K.basePort]
    exact installed.cache
  obtain ⟨t,ht,out,cacheSteps,pcOut,cached,rest,persist,regs⟩ := NativeCache.paper_run c Q D K.numerator K.denominator
    hb hB (by omega) hH fit hp hbase hf hroot hw hc K.cache M hpub (pc ∘ cachePC K) ret crows
    A.cacheBase room next rfl cachePort v buf
  have saved := installed.stored_after out.privateMem (before.trans_le (by change G ≤ A.cacheBase; omega))
    sep (by change A.cacheBase ≤ _; change A.cacheBase+38 ≤ _ at room; omega)
    (fun j h => rest j (.inl h))
  have cacheVals j : sourceWord (LeafStartup.auxiliary D hw hc v buf) D.pub (Static.dest j) =
      LeafVisit.cacheWords D d e j := by cases j <;> rfl
  refine ⟨t,ht,out,pcOut,persist.trans installed.persistent,(regs _ K.histogramPort).trans installed.hist,
    saved.1,saved.2,fun j => (cached j).trans (cacheVals j),?_,?_,?_⟩
  · intro a ha hg hc'
    exact (rest a hc').trans (installed.outside a ha hg)
  · intro j hf' hh hcache
    apply (regs _ hcache).trans
    exact installed.registers j hf' hh (fun eq => hcache ⟨_,K.basePort.symm.trans eq.symm⟩)
  · intro fuel bits
    have steps := (Prefix.tick jump cacheSteps).execute fuel m bits
    change execute M.program (fuel+(.tick :: List.replicate t .tick : List (Event w)).length) mid m
      (choiceBits (.tick :: List.replicate t .tick) ++ bits) = _ at steps
    have ch : choiceBits (.tick :: List.replicate t (.tick : Event w)) = [] :=
      (@NativeFrame.tick_cost (CursorBounds.wordBits B n) t).2
    rw [List.length_cons,List.length_replicate,ch,List.nil_append] at steps
    rw [show fuel+t+K.degree+142 = (fuel+(t+1))+K.degree+141 by omega,run,steps,Option.map_map]
    congr 1
    funext rep
    simp only [Function.comp_apply,Flow.prependEvents,List.replicate_succ,List.append_assoc,header]

end PairSimulation.NativeLeafSetup

end VPVNP
end Computability
end OAI
