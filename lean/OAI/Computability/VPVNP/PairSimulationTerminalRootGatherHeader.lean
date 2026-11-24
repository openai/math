import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherCode
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherReads

/-! # Native endpoint headers for outgoing and incoming terminal slots -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalRootGather

open BurstRAM PrivateRAM CompressorRecords.SourceTransport
open scoped Fin.CommRing

variable {w p r : ℕ}

private theorem address_val {x y : ℕ} (h : x+y < 2^w) :
    ((x : Word w)+(y : Word w)).val = x+y := by
  rw [← Nat.cast_add, Fin.val_natCast, Nat.mod_eq_of_lt h]

/-- The header selects the edge, fetches its width and exclusive prefix, and
leaves the source interval ready for the bit loop. Only the incoming pass
needs an inverse incidence read. -/
theorem header_run_reads {M : Machine w p r 11} {pc : PC → Fin p} {reg : Reg ↪ Fin r} {done : Fin p}
    (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (b : Bool) (j : ℕ) (hj : j < L.degree) (c : Config w p r)
    (hc : c.pc = pc (.header b (firstHeader b))) (h : Saved L reg c)
    (hslot : c.reg (reg (tmp 5)) = (L.index j : Word w)) (P : ℕ → Prop) (readable : L.Readable m P) :
    ∃ out es, out.pc = pc (.bits b 0) ∧ Frame reg c out ∧ out.privateMem = c.privateMem ∧
      out.reg (reg (tmp 0)) = (L.start m b j : Word w) ∧
      out.reg (reg (tmp 1)) = ((L.start m b j + L.width m b j : ℕ) : Word w) ∧
      (∀ i : Fin 9, i ≠ 0 → i ≠ 1 → i ≠ 4 → out.reg (reg (tmp i)) = c.reg (reg (tmp i))) ∧
      es.length = (if b then 8 else 7) ∧ countProbes es = (if b then 3 else 2) ∧
      (∀ m', after m' es = m') ∧ choiceBits es = [] ∧ Reads P es ∧ Prefix M m c es out := by
  let bank := c.reg ∘ reg
  let v := TerminalSiteStart.eval (M.publicData ∘ id) c.persistent m (headerLines b) bank c.privateMem
  let labels := blockPC (pc ∘ PC.header b) (pc (.bits b 0))
  have entry : c.pc = labels 0 := by cases b <;> exact hc
  obtain ⟨out, hp, hper, hregs, hpriv, hframe, hrun⟩ :=
    TerminalSiteStart.linear_run_framed M reg id m (headerLines b) labels (linked_header hl b) c entry
  have bank_eq (i : Reg) : out.reg (reg i) = v.2.1 i := congrFun hregs i
  have kept (i : Reg) (h0 : i ≠ tmp 0) (h1 : i ≠ tmp 1) (h4 : i ≠ tmp 4) :
      out.reg (reg i) = c.reg (reg i) := by
    rw [bank_eq]
    cases b <;> simp [v, bank, headerLines, TerminalSiteStart.eval, h0, h1, h4]
  let edge : Word w := if b then m (bank (save VertexImage.incoming) + bank (tmp 5)).val else bank (tmp 5)
  let start := bank (save VertexImage.wires) + m (bank (save VertexImage.prefixBase) + edge).val
  let width := m (bank (save VertexImage.widths) + edge).val
  have edge_eq : edge = (L.edge m b j : Word w) := by
    cases b with
    | false => exact hslot
    | true =>
      change m (c.reg (reg (save VertexImage.incoming)) + c.reg (reg (tmp 5))).val = _
      rw [h.incoming, hslot, address_val (fit.inverseAddr j hj)]
      exact (Fin.ofNat_val_eq_self _).symm
  have start_eq : start = (L.start m b j : Word w) := by
    change c.reg (reg (save VertexImage.wires)) + m (c.reg (reg (save VertexImage.prefixBase)) + edge).val = _
    rw [h.wires, h.prefixBase, edge_eq, address_val (fit.prefixAddr b j hj), Layout.start, Nat.cast_add]
    exact congrArg _ (Fin.ofNat_val_eq_self _).symm
  have width_eq : width = (L.width m b j : Word w) := by
    change m (c.reg (reg (save VertexImage.widths)) + edge).val = _
    rw [h.widths, edge_eq, address_val (fit.widthAddr b j hj)]
    exact (Fin.ofNat_val_eq_self _).symm
  have hstart : v.2.1 (tmp 0) = start := by cases b <;> rfl
  have hend : v.2.1 (tmp 1) = width+start := by cases b <;> rfl
  refine ⟨out, v.1, ?_, ⟨hper,?_⟩, ?_, (bank_eq _).trans (hstart.trans start_eq), ?_, ?_, ?_, ?_, ?_, ?_, ?_, hrun⟩
  · simpa only [labels, blockPC, Fin.lastCases_last] using hp
  · intro a ha
    by_cases hin : a ∈ Set.range reg
    · obtain ⟨i,rfl⟩ := hin
      apply kept i <;> intro he <;> subst i <;> exact ha _ rfl
    · exact hframe a (fun i eqn => hin ⟨i,eqn⟩)
  · cases b <;> exact hpriv
  · rw [bank_eq, hend, width_eq, start_eq, Nat.cast_add, add_comm]
  · intro i h0 h1 h4
    apply kept <;> simpa only [tmp, TerminalSiteStart.dfs, ne_eq, Sum.inl.injEq]
  · cases b <;> rfl
  · cases b <;> rfl
  · intro m'; cases b <;> rfl
  · cases b <;> rfl
  · let wa := bank (save VertexImage.widths) + edge
    let pa := bank (save VertexImage.prefixBase) + edge
    let ia := bank (save VertexImage.incoming) + bank (tmp 5)
    have hw : P wa.val := by
      change P (c.reg (reg (save VertexImage.widths)) + edge).val
      rw [h.widths, edge_eq, address_val (fit.widthAddr b j hj)]
      exact readable.widths b j hj
    have hp' : P pa.val := by
      change P (c.reg (reg (save VertexImage.prefixBase)) + edge).val
      rw [h.prefixBase, edge_eq, address_val (fit.prefixAddr b j hj)]
      exact readable.prefixes b j hj
    have hi : P ia.val := by
      change P (c.reg (reg (save VertexImage.incoming)) + c.reg (reg (tmp 5))).val
      rw [h.incoming, hslot, address_val (fit.inverseAddr j hj)]
      exact readable.incoming j hj
    intro a value member
    cases b with
    | false =>
      change Event.read a value ∈ [.tick, .tick, .read wa (m wa.val), .tick, .read pa (m pa.val),
        .tick, .tick] at member
      simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, Event.read.injEq, false_or, or_false] at member
      rcases member with ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact hw
      · exact hp'
    | true =>
      change Event.read a value ∈ [.tick, .read ia (m ia.val), .tick, .read wa (m wa.val),
        .tick, .read pa (m pa.val), .tick, .tick] at member
      simp only [List.mem_cons, List.not_mem_nil, reduceCtorEq, Event.read.injEq, false_or, or_false] at member
      rcases member with ⟨rfl,_⟩ | ⟨rfl,_⟩ | ⟨rfl,_⟩
      · exact hi
      · exact hw
      · exact hp'

theorem header_run {M : Machine w p r 11} {pc : PC → Fin p} {reg : Reg ↪ Fin r} {done : Fin p}
    (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (b : Bool) (j : ℕ) (hj : j < L.degree) (c : Config w p r)
    (hc : c.pc = pc (.header b (firstHeader b))) (h : Saved L reg c)
    (hslot : c.reg (reg (tmp 5)) = (L.index j : Word w)) :
    ∃ out es, out.pc = pc (.bits b 0) ∧ Frame reg c out ∧ out.privateMem = c.privateMem ∧
      out.reg (reg (tmp 0)) = (L.start m b j : Word w) ∧
      out.reg (reg (tmp 1)) = ((L.start m b j + L.width m b j : ℕ) : Word w) ∧
      (∀ i : Fin 9, i ≠ 0 → i ≠ 1 → i ≠ 4 → out.reg (reg (tmp i)) = c.reg (reg (tmp i))) ∧
      es.length = (if b then 8 else 7) ∧ countProbes es = (if b then 3 else 2) ∧
      (∀ m', after m' es = m') ∧ choiceBits es = [] ∧ Prefix M m c es out := by
  obtain ⟨out, es, hp, hf, hm, hs, he, hr, ht, hq, ha, hb, _, run⟩ :=
    header_run_reads hl L m fit b j hj c hc h hslot (fun _ ↦ True) (L.readable_true m)
  exact ⟨out, es, hp, hf, hm, hs, he, hr, ht, hq, ha, hb, run⟩

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI
