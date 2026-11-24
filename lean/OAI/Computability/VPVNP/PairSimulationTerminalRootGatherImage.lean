import OAI.Computability.VPVNP.PairSimulationTerminalRootGather
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherLinked

/-! # Executing the installed root gather in the final-vertex call -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalRootGather

open BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {S : VertexImage.Part → VertexImage.Segment} {w p r : ℕ}

/-- The installed gather reads only its three directory columns and the shared
bits of the selected site's outgoing and incoming fields. -/
theorem image_run_reads (A : VertexImage.Placement S p r) (hfield : S .rootFields = segment)
    (M : Machine w p r 11) (contains : VertexImage.Contains A M) (L : Layout) (mem : Memory w)
    (fit : L.Fits mem) (c : Config w p r) (hc : c.pc = A.entry .rootFields)
    (saved : Saved L (imageRegs A hfield) c) (hn : M.publicData 6 = (L.n : Word w))
    (stride : c.privateMem (c.privateMem (L.n : Word w)+7) = (L.stride : Word w))
    (P : ℕ → Prop) (readable : L.Readable mem P) :
    ∃ out es, out.pc=A.dfsPC 0 ∧ out.persistent=c.persistent ∧
      (∀ i, out.reg (A.dfs i) = c.reg (A.dfs i)) ∧
      (∀ i, out.reg (A.saved i) = c.reg (A.saved i)) ∧
      Frame (imageRegs A hfield) c out ∧
      out.privateMem = Layout.placed L.dest (L.packet mem) c.privateMem ∧
      Cost es (15+21*L.degree+5*(L.packet mem).length) (5*L.degree+(L.packet mem).length) ∧
      CompressorRecords.SourceTransport.Reads P es ∧ Prefix M mem c es out := by
  obtain ⟨out,es,hdone,frame,priv,cost,reads,exec⟩ := run_reads (image_linked A hfield contains) L mem fit c
    (hc.trans (image_entry A hfield).symm) saved hn stride P readable
  refine ⟨out,es,hdone,frame.1,fun i => frame.2 _ (fun j => ?_),fun i => frame.2 _ (fun j => ?_),
    frame,priv,cost,reads,exec⟩
  · apply A.reg.injective.ne; exact Sum.inr_ne_inl
  · apply A.reg.injective.ne
    intro h
    exact Sum.inr_ne_inl (Sum.inr.inj h)

theorem image_run (A : VertexImage.Placement S p r) (hfield : S .rootFields = segment)
    (M : Machine w p r 11) (contains : VertexImage.Contains A M) (L : Layout) (mem : Memory w)
    (fit : L.Fits mem) (c : Config w p r) (hc : c.pc = A.entry .rootFields)
    (saved : Saved L (imageRegs A hfield) c) (hn : M.publicData 6 = (L.n : Word w))
    (stride : c.privateMem (c.privateMem (L.n : Word w)+7) = (L.stride : Word w)) :
    ∃ out es, out.pc=A.dfsPC 0 ∧ out.persistent=c.persistent ∧
      (∀ i, out.reg (A.dfs i) = c.reg (A.dfs i)) ∧
      (∀ i, out.reg (A.saved i) = c.reg (A.saved i)) ∧
      Frame (imageRegs A hfield) c out ∧
      out.privateMem = Layout.placed L.dest (L.packet mem) c.privateMem ∧
      Cost es (15+21*L.degree+5*(L.packet mem).length) (5*L.degree+(L.packet mem).length) ∧
      Prefix M mem c es out := by
  obtain ⟨out,es,pc,persistent,dfs,savedRegs,frame,priv,cost,_,exec⟩ :=
    image_run_reads A hfield M contains L mem fit c hc saved hn stride _ (L.readable_true mem)
  exact ⟨out,es,pc,persistent,dfs,savedRegs,frame,priv,cost,exec⟩

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI
