import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherCode

/-!
# Native boot of the terminal root gather

Twelve local instructions fetch the private descriptor stride, locate the
root's argument buffer and initialize the endpoints of the vertex's slot
interval. Both arithmetic products are ordinary machine-word products.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalRootGather

open BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {w p r : ℕ} {M : Machine w p r 11} {pc : PC → Fin p} {reg : Reg ↪ Fin r} {done : Fin p}

theorem boot_run (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (c : Config w p r) (hc : c.pc = pc (.boot 0)) (h : Saved L reg c)
    (hn : M.publicData 6 = (L.n : Word w))
    (stride : c.privateMem (c.privateMem (L.n : Word w)+7) = (L.stride : Word w)) :
    ∃ out, out.pc = pc (.scan false) ∧ Frame reg c out ∧ out.privateMem = c.privateMem ∧
      out.reg (reg (tmp 2)) = (L.dest : Word w) ∧ out.reg (reg (tmp 3)) = 1 ∧
      out.reg (reg (tmp 5)) = (L.index 0 : Word w) ∧ out.reg (reg (tmp 6)) = (L.index L.degree : Word w) ∧
      out.reg (reg (tmp 7)) = (L.index 0 : Word w) ∧ Prefix M m c (List.replicate 12 .tick) out := by
  let labels := blockPC (pc ∘ PC.boot) (pc (.scan false))
  let v := TerminalSiteStart.eval (M.publicData ∘ id) c.persistent m bootLines (c.reg ∘ reg) c.privateMem
  obtain ⟨out,hpc,hstate,hregs,hpriv,hframe,run⟩ :=
    TerminalSiteStart.linear_run_framed M reg id m bootLines labels (linked_boot hl) c (by exact hc)
  have get (j : Reg) : out.reg (reg j) = v.2.1 j := congrFun hregs j
  have hdiv : BinaryOp.div.eval (c.reg (reg (save VertexImage.slots))) (c.reg (reg (save VertexImage.finalSites))) =
      (L.degree : Word w) := by
    rw [h.slots,h.sites]
    change Fin.ofNat (2^w) ((L.slots % (2^w))/(L.sites % (2^w))) = _
    rw [Nat.mod_eq_of_lt fit.slots,Nat.mod_eq_of_lt fit.sites]
    rfl
  have start : v.2.1 (tmp 7) = (L.index 0 : Word w) := by
    change c.reg (reg (save VertexImage.ordinal)) * BinaryOp.div.eval (c.reg (reg (save VertexImage.slots))) (c.reg (reg (save VertexImage.finalSites))) = _
    rw [h.ordinal,hdiv]; simp [Layout.index]
  have hp : labels (Fin.last bootLines.length) = pc (.scan false) := by simp [labels,blockPC]
  refine ⟨out,hpc.trans hp,⟨hstate,?_⟩,hpriv,?_,?_,?_,?_,?_,run⟩
  · intro j hj
    by_cases inRange : ∃ i, reg i = j
    · obtain ⟨i,rfl⟩ := inRange
      cases i with
      | inl i => exact (hj i rfl).elim
      | inr i => exact get (.inr i)
    · exact hframe j (fun i hi => inRange ⟨i,hi⟩)
  · rw [get]
    change M.publicData 6 + c.privateMem (c.privateMem (M.publicData 6)+7)*c.reg (reg (save VertexImage.root)) = _
    rw [hn,stride,h.root]
    simp [Layout.dest,mul_comm]
  · exact get _
  · exact (get _).trans start
  · rw [get]
    change v.2.1 (tmp 7) + BinaryOp.div.eval (c.reg (reg (save VertexImage.slots))) (c.reg (reg (save VertexImage.finalSites))) = _
    rw [start,hdiv]; simp [Layout.index]
  · exact (get _).trans start

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI
