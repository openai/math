import OAI.Computability.VPVNP.PairNativeCacheProgram
import OAI.Computability.VPVNP.PairNativeFlowPrefix

/-! # Executing the native 38-word private cache initializer

The prefix ends at the continuation supplied by the surrounding vertex
burst. The private cache holds every fixed virtual parameter and every
auxiliary public word. External memory and binary choices are untouched.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.NativeCache

open BurstRAM BurstRAM.PrivateRAM PrimedInputRAM PrimedStackRAM PrimedCounter.GuessWord
open LiveProgram LeafSourceLoad NativeOperands
open scoped Fin.CommRing

variable {R pcs : ℕ} (c : Constants) (g : Geometry) (lit : LiteralPrefix) (a b : ℕ)
  (reg : Fin (bankSize c) ↪ Fin R) (M : Machine g.w pcs R 11)

/-- Arithmetic flow whose labels form the first part of the cache table in the enclosing
machine. -/
abbrev code := relocated c a b reg
/-- Map each fixed leaf source to the enclosing machine register read by its private store
instruction. -/
abbrev storeSrc := reg ∘ resultReg c
/-- Enclosing machine register that points to the private cell for the next cache store. -/
abbrev ptr := reg (cursor (args c))
/-- Enclosing machine register containing the unit increment used to advance the cache cursor. -/
abbrev one := reg (unit (args c))

/-- Native evidence for the one private computation that prepares the leaf
cache, including the caller's register and private-memory frame. -/
theorem run (hb : 0 < b) (hn : 0 < g.n) (hwidth : g.w = (g.d+10)^4)
    (hbucket : g.H = 2^roundedUp a b g.n) (fit : PairNativeGeometry.Fits a b g.n g.w)
    (hf : ∀ j, FieldFits g (expr c j)) (h6 : (M.publicData 6).val = g.n) (h7 : (M.publicData 7).val = g.d)
    (h1 : M.publicData 1 = Fin.ofNat _ lit.length) (h0 : M.publicData 0 = Fin.ofNat _ lit.value)
    (embed : Fin (NativeCacheTable.size (code c a b reg)) → Fin pcs) (finish : Instr 2 pcs R 11)
    (rows : ∀ i, M.code (embed i) =
      (NativeCacheTable.row (code c a b reg) (storeSrc c reg) (ptr c reg) (one c reg) embed finish i).resize g.w)
    (base : ℕ) (room : base+38 ≤ 2^g.w) (st : Config g.w pcs R)
    (entry : st.pc = embed (NativeCacheTable.label (code c a b reg) (code c a b reg).entry))
    (baseWord : st.reg (reg (saved (args c))) = (base : Word g.w)) :
    ∃ t ≤ work (args c) a b g+76, ∃ out,
      Prefix M st (List.replicate t .tick) out ∧
      out.pc = embed (NativeCacheTable.done (code c a b reg)) ∧
      Cached base out.privateMem (fun j => Pieces.word g lit (expr c j)) ∧
      (∀ x : Word g.w, x.val < base ∨ base+38 ≤ x.val → out.privateMem x = st.privateMem x) ∧
      out.persistent = st.persistent ∧
      ∀ j, j ∉ Set.range reg → out.reg j = st.reg j := by
  let A := code c a b reg
  let sreg := storeSrc c reg
  let cur := ptr c reg
  let un := one c reg
  let pc := embed ∘ NativeCacheTable.pc A
  let inc := embed ∘ NativeCacheTable.inc A
  let vals := fun j => Pieces.word g lit (expr c j)
  let ext : Memory g.w := fun _ => 0
  obtain ⟨t,ht,out,arith,ready,hcur,hu,frame⟩ := prelude c g lit a b reg hb hn hwidth hbucket fit hf
    M.publicData h6 h7 h1 h0 st.persistent ext st.reg
  have linked := NativeCacheTable.linked_of_rows A sreg cur un M embed finish rows
  let mid : Config g.w pcs R := ⟨pc 0,st.persistent,out,st.privateMem⟩
  have head : Prefix M st (List.replicate t .tick) mid := by
    have h := arith.toPrefix linked st.privateMem
    have hst : (⟨embed (NativeCacheTable.label A A.entry),st.persistent,st.reg,st.privateMem⟩ : Config g.w pcs R) = st := by
      change st.pc = embed (NativeCacheTable.label A A.entry) at entry
      rw [← entry]
    exact hst ▸ h
  have stores (j : Fin (slots 34).length) : M.code (pc j.castSucc) = storeInstr sreg cur (inc j) (slots 34)[j] := by
    rw [show pc j.castSucc = embed (NativeCacheTable.pc A j.castSucc) from rfl,rows,NativeCacheTable.row_store]
    rfl
  have advances (j : Fin (slots 34).length) : M.code (inc j) = incInstr cur un (pc j.succ) := by
    rw [show inc j = embed (NativeCacheTable.inc A j) from rfl,rows,NativeCacheTable.row_advance]
    rfl
  have hsrc (j : Static 34) : sreg j ≠ cur := reg.injective.ne (temp_ne_fixed ((number j).val+1) 10)
  have huc : un ≠ cur := reg.injective.ne (by
    intro h; have := congrArg Fin.val h; change 11 = 10 at this; contradiction)
  obtain ⟨final,tail,atEnd,mem⟩ := write_rows M sreg cur un hsrc huc (slots 34) vals pc inc
    stores advances base mid rfl (hcur.trans baseWord) hu ready (by simpa using room)
  have run := head.append tail
  rw [← List.replicate_add,length_slots] at run
  refine ⟨_,by omega,final,run,atEnd,mem.cached,?_,mem.persistent,?_⟩
  · intro x hx; apply mem.outside; simpa using hx
  · intro j hj; exact (mem.frame j (fun eq => hj ⟨cursor (args c),eq.symm⟩)).trans (frame _ hj)

end PairSimulation.NativeCache

end VPVNP
end Computability
end OAI
