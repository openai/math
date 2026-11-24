import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherBoot
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherHeader
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherScan

/-! # Loading the root packet before the native DFS

One fixed segment reads the actual outgoing and incoming incidence directories,
then gathers the shared payloads into the site's private descriptor. The
destination memory formula gives the value at every private word, including
the DFS stack and the histogram outside the packet.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalRootGather

open BurstRAM PrivateRAM CompressorRecords.SourceTransport
open scoped Fin.CommRing

variable {w p r : ℕ} {M : Machine w p r 11} {pc : PC → Fin p} {reg : Reg ↪ Fin r} {done : Fin p}

/-- Execute the complete finite gather. Both passes use the same external
memory and branch suffix, and each writes exactly its packed private words. -/
theorem run_reads (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (c : Config w p r) (hc : c.pc=pc (.boot 0)) (saved : Saved L reg c)
    (hn : M.publicData 6=(L.n : Word w))
    (stride : c.privateMem (c.privateMem (L.n : Word w)+7)=(L.stride : Word w))
    (P : ℕ → Prop) (readable : L.Readable m P) :
    ∃ out es, out.pc=done ∧ Frame reg c out ∧
      out.privateMem=Layout.placed L.dest (L.packet m) c.privateMem ∧
      Cost es (15+21*L.degree+5*(L.packet m).length) (5*L.degree+(L.packet m).length) ∧
      Reads P es ∧ Prefix M m c es out := by
  have headers : HeadersReads P L M m pc reg := by
    intro b j hj cur hpc h hs
    obtain ⟨out,es,ho,hf,hm,hsrc,hend,hr,hlen,hprobes,hafter,hchoices,hreads,hex⟩ :=
      header_run_reads hl L m fit b j hj cur hpc h hs P readable
    exact ⟨out,es,ho,hf,hm,hsrc,hend,hr,⟨hlen,hprobes,hafter,hchoices⟩,hreads,hex⟩
  let xs := (L.fields m false).flatten
  let ys := (L.fields m true).flatten
  have len : (L.packet m).length=xs.length+ys.length := List.length_append
  have room := fit.destEnd
  rw [len] at room
  obtain ⟨boot,hboot,fboot,pboot,hd,ho,hi,hstop,hfirst,rboot⟩ := boot_run hl L m fit c hc saved hn stride
  obtain ⟨left,levents,hreset,fleft,pleft,leftCur,cleft,leftReads,rleft⟩ :=
    scan_run_reads hl L m fit P readable headers false L.degree 0 L.dest
      (Nat.zero_add _) (by rw [suffix_full]; change L.dest+xs.length < _; omega) boot hboot
      (saved.transport fboot) ⟨hd,ho,hi,hstop,hfirst⟩
  rw [suffix_full] at pleft leftCur cleft
  obtain ⟨mid,hmid,fmid,pmid,midCur,rmid⟩ := reset_run hl L m left hreset L.degree (L.dest+xs.length) leftCur
  obtain ⟨out,revents,hdone,fright,pright,_,cright,rightReads,rright⟩ :=
    scan_run_reads hl L m fit P readable headers true L.degree 0 (L.dest+xs.length) (Nat.zero_add _)
      (by rw [suffix_full]; change L.dest+xs.length+ys.length < _; omega)
      mid hmid (saved.transport ((fboot.trans fleft).trans fmid)) midCur
  rw [suffix_full] at pright cright
  refine ⟨out,_,hdone,((fboot.trans fleft).trans fmid).trans fright,?_,?_,
    (((Reads.replicate_tick P 12).append leftReads).append (Reads.replicate_tick P 1)).append rightReads,
    ((rboot.trans rleft).trans rmid).trans rright⟩
  · rw [pright,pmid,pleft,pboot,Layout.placed_append]; rfl
  · have cost := (((Cost.replicate_tick (w:=w) 12).append cleft).append Cost.tick).append cright
    rw [len]
    convert cost using 1 <;> first | rfl | (simp only [xs,ys,Bool.false_eq_true,↓reduceIte,Nat.mul_add]; omega)

theorem run (hl : Linked M pc reg done) (L : Layout) (m : Memory w) (fit : L.Fits m)
    (c : Config w p r) (hc : c.pc=pc (.boot 0)) (saved : Saved L reg c)
    (hn : M.publicData 6=(L.n : Word w))
    (stride : c.privateMem (c.privateMem (L.n : Word w)+7)=(L.stride : Word w)) :
    ∃ out es, out.pc=done ∧ Frame reg c out ∧
      out.privateMem=Layout.placed L.dest (L.packet m) c.privateMem ∧
      Cost es (15+21*L.degree+5*(L.packet m).length) (5*L.degree+(L.packet m).length) ∧ Prefix M m c es out := by
  obtain ⟨out, es, hp, hf, hm, cost, _, exec⟩ :=
    run_reads hl L m fit c hc saved hn stride (fun _ ↦ True) (L.readable_true m)
  exact ⟨out, es, hp, hf, hm, cost, exec⟩

end PairSimulation.TerminalRootGather

end VPVNP
end Computability
end OAI
