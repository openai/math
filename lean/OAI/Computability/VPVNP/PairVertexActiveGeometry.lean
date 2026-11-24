import OAI.Computability.VPVNP.PairVertexGeometryRun
import OAI.Computability.VPVNP.PairNativeFrameFootprint
import OAI.Computability.VPVNP.PairVertexSiteSegments

/-! # Starting an actual nonterminal-ordinal call of the assembled vertex RAM -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.VertexImage

open BurstRAM PrivateRAM LiveProgram PrimedInputRAM TerminalSiteStart NativeOperands
open scoped Fin.CommRing

variable {W : ℕ}

/-- Events of the active vertex entry, from testing the site ordinal through the two control
ticks and the terminal site bootstrap. -/
def startTrace (m : Memory W) (h : Word W) :=
  guardTrace m h ++ [.tick,.tick] ++ bootTrace m h

theorem start_cost (m : Memory W) (h : Word W) :
    (startTrace m h).length = 44 ∧ countProbes (startTrace m h) = 9 ∧
      choiceBits (startTrace m h) = [] ∧ after m (startTrace m h) = m := by
  exact ⟨rfl,rfl,rfl,rfl⟩

private theorem tick_after (m : Memory W) (n : ℕ) : after m (List.replicate n .tick) = m := by
  induction n with
  | zero => rfl
  | succ n ih => simpa only [List.replicate_succ,after,List.foldl_cons,update] using ih

/-- The three observable quantities of the bootstrap and private operand
initialization. All genuine external accesses in these two stages are reads. -/
theorem active_geometry_cost (degree t : ℕ) (m : Memory W) (h : Word W) :
    let es := startTrace m h ++ (NativeFrame.events degree h m ++ List.replicate (t+2) .tick)
    es.length = t+degree+187 ∧ countProbes es = 15 ∧ choiceBits es = [] ∧ after m es = m := by
  intro es
  have s := start_cost m h
  have g := VertexGeometry.charges degree h m t
  refine ⟨?_,?_,?_,?_⟩
  · rw [show es = _ from rfl,List.length_append,s.1,g.1]; omega
  · rw [show es = _ from rfl,countProbes_append,s.2.1,g.2.1]
  · rw [show es = _ from rfl,Flow.choiceBits_append,s.2.2.1,g.2.2]; rfl
  · have app (mem : Memory W) (xs ys : List (Event W)) : after mem (xs++ys) = after (after mem xs) ys := List.foldl_append
    rw [show es = _ from rfl,app,s.2.2.2,app,NativeFrame.events_after,tick_after]

variable (c : Constants) (degree a b : ℕ) {p r : ℕ} {rootFields leaf shrink refresh : Segment}
  (A : Placement (segments (VertexGeometry.segment c degree a b) rootFields leaf shrink refresh) p r)
  {prog : UniversalMachine.Program} {B n H : ℕ} {i : Fin (2^(n^c.chainPower-1))}

local notation "W₀" => CursorBounds.wordBits B n
local notation "D₀" => CursorBounds.virtualBits B n
local notation "E₀" => roundedUp 1 4 n
local notation "g₀" => AssemblerPublic.geometry B n H

variable (Q : PrimedInputRAM.Layout (CounterPublic.spec prog c |>.lengths n i)
  n (addressWidth B n) H (CursorBounds.wordBits B n))
  (D : PrimedCounter.Data Q (n^(c.circuitExponent+5)))

/-- The ordinal guard, root-address load and complete geometry/cache
initialization run from the real bootstrap entry. The unused tape, the
pending root, and all saved coordinates are passed to the field gather. -/
theorem active_geometry (hb : 0 < b) (hB : 1 ≤ B) (hn : 3 ≤ n) (hH : H = 2^roundedUp a b n)
    (fit : PairNativeGeometry.Fits a b n W₀) (hp : Q.program = prog) (hbase : Q.scratchBase = 2^D₀)
    (hf : D.Fits) (hroot : D.root.val = 0) (hw : 2 ≤ W₀) (hc : 2^D₀*2^E₀ < 2^W₀)
    (M : Machine W₀ p r 11) (pub : M.publicData = Pieces.word g₀ (CounterPublic.actualPrefix prog) ∘ StageOperands.pair c)
    (link : Contains A M) (m : Memory W₀) (start : Config W₀ p r)
    (here : start.pc = A.entry .bootstrap)
    (active : start.persistent < m (headerWord M.publicData+7).val)
    (before : (M.publicData 6).val < NativeFrame.frameBase (NativeFrame.fromHeader degree M.publicData
      (headerWord M.publicData) m))
    (room : (NativeFrame.fromHeader degree M.publicData (headerWord M.publicData) m).cacheBase+38 ≤ 2^W₀) :
    let h := headerWord M.publicData
    ∃ t ≤ work (NativeCache.args c) a b g₀+76, ∃ boot out,
      boot.persistent = start.persistent ∧
      BootReady (M.publicData 6) h start.persistent m (boot.reg ∘ bootBank A) ∧
      boot.privateMem = Function.update start.privateMem (M.publicData 6-1) (m (h+6).val + m (h+15).val*start.persistent) ∧
      VertexGeometry.Ready c degree a b A m M.publicData boot out (LeafVisit.cacheWords D D₀ E₀) ∧
      TerminalSiteStart.Continues M m start out
        (startTrace m h ++ (NativeFrame.events degree h m ++ List.replicate (t+2) .tick)) := by
  intro h
  obtain ⟨boot,entry,persist,ready,mem,run⟩ := TerminalSiteStart.active_run (boot_startLinked A M link)
    m start here active
  have word : boot.reg (A.saved header) = h := ready.header
  obtain ⟨t,ht,out,result,next⟩ := VertexGeometry.segment_run c degree a b A Q D hb hB hn hH fit hp hbase hf
    hroot hw hc M pub link m boot entry (word ▸ before) (word ▸ room)
  refine ⟨t,ht,boot,out,persist,ready,mem,result,?_⟩
  have bootRun : TerminalSiteStart.Continues M m start boot (startTrace m h) := run
  have len := (VertexGeometry.charges degree h m t).1
  intro fuel bits
  rw [List.length_append,Nat.add_comm (startTrace m h).length,← Nat.add_assoc,bootRun,len]
  rw [show fuel + (t+degree+143) = fuel+t+degree+143 by omega,next,word]
  simp only [Option.map_map,Function.comp_def,Flow.prependEvents,List.append_assoc]

end PairSimulation.VertexImage

end VPVNP
end Computability
end OAI
