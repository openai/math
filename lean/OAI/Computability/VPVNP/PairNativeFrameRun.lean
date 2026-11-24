import OAI.Computability.VPVNP.PairNativeFramePrelude
import OAI.Computability.VPVNP.PairNativeFrameStore

/-! # Executing the terminal vertex's private geometry installation

The caller supplies two live registers holding the terminal header and its
role offset. The program consumes six external reads, computes all addresses,
and publishes the histogram and scalar-cache pointers in the designated
registers of the enclosing vertex burst.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeFrame
open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r : ℕ}

/-- Register allocation for the terminal frame installer, with input and output separation
conditions that protect the role and cache values during handoff. -/
structure Ports (r : ℕ) where
  /-- Embedding of the installer's 24 local work registers into the enclosing machine's
  register bank. -/
  work : R ↪ Fin r
  /-- Caller register supplying the terminal header's external address to the first entry copy. -/
  header : Fin r
  /-- Caller register supplying the role offset to the second entry copy, distinct from the
  destination of the first copy. -/
  role : Fin r
  /-- Caller register receiving the private histogram base before the cache pointer is copied
  out. -/
  hist : Fin r
  /-- Caller register receiving the scalar-cache base for the next phase of leaf preparation. -/
  cache : Fin r
  role_free : role ≠ work 0
  hist_free : hist ≠ work 11
  outputs : hist ≠ cache

/-- Frame prelude specialized to the work-register embedding and the caller's two input
registers. -/
abbrev Ports.code (P : Ports r) (degree : ℕ) := prelude degree P.work P.header P.role
/-- Instruction-row emitter that uses these ports for the prelude, private frame stores and
pointer handoff to the caller. -/
abbrev Ports.row (P : Ports r) (degree : ℕ) := Table.row (P.code degree) P.work P.hist P.cache (p := p)

/-- Trace of the entire frame installation, extending the prelude by 27 local ticks for private
stores, cursor advances and the two output copies. -/
def events (degree : ℕ) (header : Word w) (m : Memory w) :=
  preludeEvents degree header m ++ List.replicate 27 .tick

theorem events_cost (degree : ℕ) (header : Word w) (m : Memory w) :
    (events degree header m).length = degree+141 ∧
    countProbes (events degree header m) = 6 ∧ choiceBits (events degree header m) = [] := by
  obtain ⟨l,p,b⟩ := prelude_cost degree header m
  obtain ⟨tp,tb⟩ := tick_cost (w := w) 27
  refine ⟨?_,?_,?_⟩
  · rw [events,List.length_append,l,List.length_replicate]
  · rw [events,countProbes_append,p,tp]
  · rw [events,Flow.choiceBits_append,b,tb]; rfl

/-- The private memory and register ABI seen by all subsequent visits in
this burst, including visits that fail the route or cursor-zero verifier. -/
structure Result (P : Ports r) (degree : ℕ) (pub : Fin 11 → Word w) (m : Memory w)
    (c out : Config w p r) : Prop where
  pointer : out.privateMem (pub 6) = (frameBase (fromHeader degree pub (c.reg P.header) m) : Word w)
  values : ∀ i : Fin 12, out.privateMem ((frameBase (fromHeader degree pub (c.reg P.header) m)+i.val : ℕ) : Word w) =
    fields degree pub (c.reg P.header) (c.reg P.role) m i
  outside : ∀ a : Word w, a ≠ pub 6 → a.val < frameBase (fromHeader degree pub (c.reg P.header) m) ∨
      frameBase (fromHeader degree pub (c.reg P.header) m)+12 ≤ a.val → out.privateMem a = c.privateMem a
  hist : out.reg P.hist = ((fromHeader degree pub (c.reg P.header) m).histBase : Word w)
  cache : out.reg P.cache = ((fromHeader degree pub (c.reg P.header) m).cacheBase : Word w)
  persistent : out.persistent = c.persistent
  registers : ∀ j, j ∉ Set.range P.work → j ≠ P.hist → j ≠ P.cache → out.reg j = c.reg j

theorem run (P : Ports r) (degree : ℕ) (M : Machine w p r 11)
    (emb : Fin (Table.size (P.code degree)) → Fin p) (finish : Instr 2 p r 11)
    (rows : ∀ j, M.code (emb j) = (P.row degree emb finish j).resize w) (m : Memory w)
    (c : Config w p r) (entry : c.pc = emb (Table.label (P.code degree) (P.code degree).entry))
    (before : (M.publicData 6).val < frameBase (fromHeader degree M.publicData (c.reg P.header) m))
    (fit : frameBase (fromHeader degree M.publicData (c.reg P.header) m)+12 ≤ 2^w) :
    ∃ out, out.pc = emb (Table.tail (P.code degree) 27) ∧ Result P degree M.publicData m c out ∧
      ∀ fuel bits, execute M.program (fuel + degree+141) c m bits =
        (execute M.program fuel out m bits).map (Flow.prependEvents (events degree (c.reg P.header) m)) := by
  let flow := P.code degree
  change ∀ j, M.code (emb j) = (Table.row flow P.work P.hist P.cache emb finish j).resize w at rows
  let header := c.reg P.header
  let n := (M.publicData 6).val
  let G := frameBase (fromHeader degree M.publicData header m)
  let hd := preludeEvents degree header m
  have hw : (n : Word w) = M.publicData 6 := Fin.ext (Nat.mod_eq_of_lt (M.publicData 6).isLt)
  obtain ⟨bank,deriv,ready,frame⟩ := prelude_run degree P.work P.header P.role P.role_free M.publicData
    c.persistent m c.reg
  let mid : Config w p r := ⟨emb (Table.tail flow 0),c.persistent,bank,c.privateMem⟩
  have hn : mid.reg (P.work 9) = (n : Word w) := (ready.field 6).trans hw.symm
  obtain ⟨s,runStores,pcS,installed⟩ := store_run flow P.work P.hist P.cache emb finish M rows
    n G before fit mid rfl hn ready.graph ready.cursor ready.unit
  let h := s.put (emb (Table.tail flow 26)) P.hist (s.reg (P.work 14))
  let out := h.put (emb (Table.tail flow 27)) P.cache (h.reg (P.work 11))
  have histStep : M.program.step s = .localStep h := by
    change (M.code s.pc).run M.publicData s = _
    rw [pcS,rows,Table.at_hist]; rfl
  have cacheStep : M.program.step h = .localStep out := by
    change (M.code (emb (Table.tail flow 26))).run M.publicData h = _
    rw [rows,Table.at_cache]; rfl
  have handoff : Prefix M s [.tick,.tick] out := .tick histStep (.tick cacheStep (.nil _))
  have tail : Prefix M mid (List.replicate 27 .tick) out := runStores.append handoff
  refine ⟨out,rfl,?_,?_⟩
  · refine ⟨?_,?_,?_,?_,?_,installed.persistent,?_⟩
    · exact hw ▸ installed.pointer
    · intro i; exact (installed.fields i).trans (ready.field i)
    · intro a hne outside
      exact installed.outside a (fun eq => hne (Fin.ext eq)) outside
    · change Function.update h.reg P.cache _ P.hist = _
      rw [Function.update_of_ne P.outputs]
      change Function.update s.reg P.hist _ P.hist = _
      rw [Function.update_self,installed.registers _ (P.work.injective.ne (by decide))]
      exact ready.field 11
    · change Function.update h.reg P.cache _ P.cache = _
      rw [Function.update_self]
      change Function.update s.reg P.hist _ (P.work 11) = _
      rw [Function.update_of_ne P.hist_free.symm,installed.registers _ (P.work.injective.ne (by decide))]
      exact ready.field 8
    · intro j outside histFree cacheFree
      have hcur : j ≠ P.work 18 := fun eq => outside ⟨18,eq.symm⟩
      change Function.update h.reg P.cache _ j = _
      rw [Function.update_of_ne cacheFree]
      change Function.update s.reg P.hist _ j = _
      rw [Function.update_of_ne histFree,installed.registers j hcur]; exact frame j outside
  · intro fuel bits
    have linked := Table.linked flow P.work P.hist P.cache emb finish M rows
    have reject : M.code (emb (Table.tail flow 28)) = .reject := by rw [rows,Table.at_bad]; rfl
    have front := deriv.execute linked reject c.privateMem (fuel+27) bits
    have initial : (⟨emb (Table.label flow flow.entry),c.persistent,c.reg,c.privateMem⟩ : Config w p r) = c := by
      rw [←entry]
    change execute M.program (hd.length+(fuel+27)) ⟨emb (Table.label flow flow.entry),c.persistent,c.reg,c.privateMem⟩ m (choiceBits hd ++ bits) =
      (execute M.program (fuel+27) mid m bits).map (Flow.prependEvents hd) at front
    obtain ⟨len,_,ch⟩ := prelude_cost degree header m
    change hd.length = degree+114 at len
    change choiceBits hd = [] at ch
    rw [len,ch,List.nil_append,initial] at front
    have last := tail.execute fuel m bits
    rw [List.length_replicate,(tick_cost (w := w) 27).2,List.nil_append] at last
    rw [show fuel+degree+141 = (degree+114)+(fuel+27) by omega,front,last,Option.map_map]
    congr 1
    funext rep; simp only [Function.comp_apply,Flow.prependEvents,events,hd,List.append_assoc,header]

end PairSimulation.NativeFrame

end VPVNP
end Computability
end OAI
