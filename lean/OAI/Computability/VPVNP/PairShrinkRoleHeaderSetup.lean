import OAI.Computability.VPVNP.PairShrinkHiddenHeaderTrace
import OAI.Computability.VPVNP.PairShrinkHiddenSegmentRun

/-! # Exact DFS stage for the hosted hidden-field header compiler -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkRole

open BurstRAM BurstRAM.PrivateRAM ShrinkHiddenGuess
open private no_choices from OAI.Computability.VPVNP.CompressorRecordRegisterSetup
open scoped Fin.CommRing

variable {w p r endAddr : ℕ}

/-- The hosted header loads the five published fields and changes only registers. -/
def hiddenHeader (s t oldHead : ℕ) (m : Memory w) : Setup w endAddr where
  trace _ _ := Header.canonicalTrace s t (oldHead : Word w) m
  updated _ saved := saved
  quiet _ _ := no_choices ..

/-- Link the actual installed header at its segment entry to the hidden guess
loop. The scratch and trace hold uniformly for every eligible configuration. -/
theorem hiddenHeader_realizes {M : Machine w p r 11} {m : Memory w}
    (s t : ℕ) (pc : Fin (Table.segmentCount s t) → Fin p)
    (dfs : Fin 9 ↪ Fin r) (saved : VertexImage.Saved ↪ Fin r)
    (prv : Fin (Table.R s t) ↪ Fin r) (ret : Fin p)
    (rows : ∀ i, M.code (pc i) = ((Table.segment s t).row pc dfs saved prv ret i).resize w)
    (g : Args w) (oldHead : ℕ) (selectors : g.selectorBits = (s : Word w))
    (stride : g.rowStride = t) (fit : oldHead + 38 < 2 ^ w)
    (headers : Header.Published g oldHead m)
    (separate : ∀ i : Fin 9, i = 3 ∨ i = 5 ∨ i = 6 ∨ i = 7 →
      dfs i ∉ Set.range ((Table.vm s t).trans prv))
    {pre post : Word w → Config w p r → Prop}
    (start : ∀ node c, pre node c → c.pc = pc (Table.segment s t).entry ∧
      Table.SegmentOperands s t prv g oldHead c)
    (resume : ∀ node c d, pre node c → d.pc = Table.segmentLoop s t pc (.inl .one) →
      Inputs g ((Table.regs s t).trans prv) d → d.privateMem = c.privateMem →
      d.persistent = c.persistent →
      (∀ i, i ∉ Set.range ((Table.vm s t).trans prv) → d.reg i = c.reg i) → post node d) :
    Realizes (hiddenHeader (endAddr := endAddr) s t oldHead m).reader M m dfs pre
      (fun _ => post) := by
  apply Setup.realizes
  intro node c hc
  obtain ⟨ep,operands⟩ := start node c hc
  obtain ⟨d,path,entry,inputs,mem,pers,keep,_⟩ :=
    Table.segment_prepare_raw M pc dfs saved prv ret rows g m oldHead c ep operands
      selectors stride fit headers
  rw [Header.trace_canonical s t _ _ c m _ operands.level] at path
  exact ⟨d, resume node c d hc entry inputs mem pers keep,
    ⟨fun i hi => keep _ (separate i hi), fun addr _ => congrFun mem addr, pers⟩,
    congrArg (DFS.scratch endAddr) mem, path⟩

end PairSimulation.ShrinkRole

end VPVNP
end Computability
end OAI
