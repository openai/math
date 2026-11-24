import OAI.Computability.VPVNP.CompressorGreedyPrepareHeaderAccess
import OAI.Computability.VPVNP.CompressorGreedyPrepareRowsAccess

/-! # Memory accesses of one relocated greedy record writer

The public control-word loader and the final cursor increment have no
external probes. The header and operand writers stay inside the current
walk layout, and the only external reads are the two mate tables.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.Greedy.PrepareAccess

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM SourceTransport Compression
open scoped Fin.CommRing
open private header_written base_bounds nextVertex putHeader from OAI.Computability.VPVNP.CompressorRecordGreedyPrepare
open private split_trace from OAI.Computability.VPVNP.CompressorGreedyPrepareRowsAccess
open private loaded loadControls trace_slots from OAI.Computability.VPVNP.CompressorGreedyRelocated

variable {w N width d : ℕ} {V : Type*}

private theorem body (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows' : OperandRows d) (m : Memory w) (i : Fin N)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (space : L.limit < 2^w) (free : GraphOutside (d := d) L T order)
    (size : (rowWords T G order (order.symm i) rows').length = width)
    (rd : ℕ → Prop) (cells : ∀ e : V × Fin d, ∀ b ∈ [T.outgoing,T.incoming], rd (b+portNumber order e).val)
    (rs : Regs w 13) (input : RowInput T (Fin.ofNat _ i.val) 0 rs) (unit : rs 11 = 1)
    (first : rs 8 = L.base 0) (stride : rs 9 = Fin.ofNat _ (2+width))
    {es out last} (run : trace (slotNumbers w d) (Fin.ofNat _ i.val) (prepareBody rows') rs m =
      some (es,out,last)) : Reads rd es ∧ Writes (Interval L.origin L.limit) es := by
  let s := Fin.ofNat (2^w) i.val
  let b := L.base i.val
  let dest := b+1+1
  let mid := writeRow (writeMemory m (L.label i) 0) b [L.label i,L.base (i.val+1)]
  obtain ⟨bs,bend⟩ := base_bounds L i
  change b.val = _ at bs
  change b.val+(2+width) ≤ L.limit at bend
  have hd : dest.val = b.val+2 := advance_val b 2 (by omega)
  obtain ⟨hs,hregs,hRun,_,_,hstate⟩ := header_written L T m i d rs labels input unit first stride
  change trace (slotNumbers w d) s (putHeader d) rs m = some (hs,hregs,mid) at hRun
  have hacc := head L T m i rs labels input unit first stride hRun
  have table (e : V × Fin d) (x : Word w) (hx : x ∈ [T.outgoing,T.incoming]) :
      mid (x+portNumber order e).val = m (x+portNumber order e).val := by
    rw [← trace_after hRun]
    apply SourceTransport.after_outside m hacc.2
    have := free e x hx
    rintro ⟨ha,hb⟩; omega
  have rep' : T.Represents G order mid :=
    ⟨rep.degree,rep.fits,rep.vertices,fun e ↦ (table e _ (by simp)).trans (rep.outgoing e),
      fun e ↦ (table e _ (by simp)).trans (rep.incoming e)⟩
  have hin : RowInput T (vertexNumber order (order.symm i)) dest hregs := by
    simpa only [vertexNumber,Equiv.apply_symm_apply] using hstate
  have wordsFit : dest.val+(rowWords T G order (order.symm i) rows').length < 2^w := by rw [size]; omega
  have wordsFree := free.free dest.val (rowWords T G order (order.symm i) rows').length (by omega) (by rw [size]; omega)
  obtain ⟨ms,mregs,mRun,_,_,_⟩ := initRows_trace T G order s (order.symm i) rows' mid dest hregs hin rep' wordsFit wordsFree
  have macc := rows T G order s (order.symm i) rows' mid dest hregs hin rep' wordsFit wordsFree rd cells mRun
  change trace _ s ((putHeader d ++ initRows rows') ++ nextVertex d) rs m = _ at run
  rw [List.append_assoc] at run
  obtain ⟨ts,tRun,rfl⟩ := split_trace hRun run
  obtain ⟨ns,nRun,rfl⟩ := split_trace mRun tRun
  have no : countProbes ns = 0 := by
    have h := congrArg (fun z ↦ z.map (countProbes ∘ Prod.fst)) nRun
    simpa (config := {decide := true}) [nextVertex,trace,Op.effect,BinaryOp.eval,Function.update,countProbes] using h.symm
  apply append ⟨fun a v h ↦ (hacc.1 a v h).elim,hacc.2⟩
  apply append _ (FlowFootprint.bounds_of_noProbes rd (Interval L.origin L.limit) no)
  refine ⟨macc.1,fun a v h ↦ ?_⟩
  obtain ⟨h₁,h₂⟩ := macc.2 a v h
  rw [size] at h₂
  exact ⟨by omega,by omega⟩

/-- Native single vertex visit and the complete bounds on its external addresses. -/
theorem one (L : WalkLayout w N width) (T : PortTables w) (G : SlotGraph V d)
    (order : V ≃ Fin N) (rows' : OperandRows d) (m : Memory w) (i : Fin N)
    (labels : T.labels = Fin.ofNat _ L.origin) (rep : T.Represents G order m)
    (space : L.limit < 2^w) (free : GraphOutside (d := d) L T order)
    (size : (rowWords T G order (order.symm i) rows').length = width)
    (rd : ℕ → Prop) (cells : ∀ e : V × Fin d, ∀ b ∈ [T.outgoing,T.incoming], rd (b+portNumber order e).val) :
    let P := ((Relocated.preparePass rows').table.instantiate w (Relocated.publicWords d L T)).program
    ∃ es, execute P (1+(Relocated.prepareCode rows').length) (P.start (Fin.ofNat _ i.val)) m [] =
      some ⟨es,some (Fin.ofNat _ (i.val+1))⟩ ∧ Reads rd es ∧ Writes (Interval L.origin L.limit) es := by
  let s := Fin.ofNat (2^w) i.val
  obtain ⟨a,r,ha,_,hpa,hr,hu,hfirst,hstride⟩ := loaded L T m s d
  obtain ⟨b,last,hb,hresult,_,_⟩ := prepareBody_trace L T G order rows' m i labels rep space free size r hr hu hfirst hstride
  have acc := append (FlowFootprint.bounds_of_noProbes rd (Interval L.origin L.limit) hpa)
    (body L T G order rows' m i labels rep space free size rd cells r hr hu hfirst hstride hb)
  refine ⟨a++b,?_,acc⟩
  let M := (template (Relocated.prepareCode rows') 0).instantiate w (Relocated.publicWords d L T)
  change execute M.program (1+(Relocated.prepareCode rows').length) ⟨M.entry,s,fun _ ↦ 0,fun _ ↦ 0⟩ m [] = _
  dsimp only [M]
  rw [execute_template,run_eq_trace,Relocated.prepareCode,trace_append,ha]
  simp only [Option.bind_some,trace_slots,s,hb,Option.map_some,hresult,List.append_nil]

end CompressorRecords.Greedy.PrepareAccess

end VPVNP
end Computability
end OAI
