import OAI.Computability.VPVNP.PairSimulationLeafSourcePrelude
import OAI.Computability.VPVNP.PairSimulationLeafCacheWrite

/-! # The complete scalar source bank for a virtual leaf of a pair call -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafSourceLoad

open BurstRAM PrivateRAM RAMTape LeafRegisterBank PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {d e w k r p pubs : ℕ}

theorem slot_offset (i : Fin (slots k).length) : ((slots k)[i]).offset = i.val := by
  have hi : i.val < 4+k := by simpa only [length_slots] using i.isLt
  have h : ((slots k).map Static.offset)[i.val]'(by simpa using hi) = i.val := by
    simp only [slots_offsets,List.getElem_range]
  simp only [List.getElem_map] at h
  exact h

/-- Private array at the offset reserved by the pair's leaf arena. -/
def Cached (base : ℕ) (m : Word w → Word w) (vals : Static k → Word w) : Prop :=
  ∀ j, m ((base+j.offset : ℕ) : Word w) = vals j

theorem Stored.cached {c out : Config w p r} {cursor : Fin r} {base : ℕ} {vals : Static k → Word w}
    (h : Stored c out cursor base ((slots k).map vals)) : Cached base out.privateMem vals := by
  intro j
  obtain ⟨i,hi,he⟩ := List.mem_iff_getElem.mp (mem_slots j)
  let ix : Fin (slots k).length := ⟨i,hi⟩
  have hix : (slots k)[ix] = j := he
  have off : j.offset = i := hix ▸ slot_offset ix
  rw [off]
  have hv := h.values ⟨i, by simpa only [List.length_map] using hi⟩
  have hm : i < ((slots k).map vals).length := by simpa only [List.length_map] using hi
  change out.privateMem ((base+i : ℕ) : Word w) = ((slots k).map vals)[i]'hm at hv
  simpa only [List.getElem_map, he] using hv

/-- From the actual dynamic address and header, and the resident 38-word
cache, furnish every input of the pointer and scalar-port initializer. -/
theorem cachedSources (x : VirtualSite.Input d e w) (vals : Fin k → Word w)
    (M : Machine w p r pubs) (ports : Source k ↪ Fin r) (site hdr base cursor unit : Fin r)
    (pre : Fin 5 → Fin p) (pc : Fin ((slots k).length+1) → Fin p) (inc : Fin (slots k).length → Fin p)
    (preRows : ∀ i, M.code (pre i) = prelude ports site hdr base cursor unit pre (pc 0) i)
    (read : ∀ i : Fin (slots k).length, M.code (pc i.castSucc) = readInstr ports cursor (inc i) (slots k)[i])
    (advance : ∀ i : Fin (slots k).length, M.code (inc i) = incInstr cursor unit (pc i.succ))
    (wires : Wiring ports hdr base cursor unit) (cacheBase : ℕ) (c : Config w p r) (entry : c.pc = pre 0)
    (ha : c.reg site = x.addrWord) (hh : c.reg hdr = x.headerWord) (hzero : x.initialWord = 0)
    (hb : c.reg base = (cacheBase : Word w))
    (ready : Cached cacheBase c.privateMem (fun i : Static k => sourceWord x vals i.dest)) :
    ∃ out, Prefix M c (List.replicate (5+2*(4+k)) .tick) out ∧ out.pc = pc (Fin.last (slots k).length) ∧
      (∀ j, out.reg (ports j) = sourceWord x vals j) ∧
      out.reg cursor = ((cacheBase+(4+k) : ℕ) : Word w) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧
      ∀ i, (∀ j, i ≠ ports j) → i ≠ cursor → i ≠ unit → out.reg i = c.reg i := by
  let args := fun i : Static k => sourceWord x vals i.dest
  let mid : Config w p r := {c with pc := pc 0, reg := prepBank ports site hdr base cursor unit c.reg}
  have start := prep_run M ports site hdr base cursor unit pre (pc 0) preRows wires c entry
  have hc : mid.reg cursor = (cacheBase : Word w) := by simp [mid,prepBank,wires.different,hb]
  have hone : mid.reg unit = 1 := Function.update_self ..
  have hcache (i : Fin (slots k).length) : mid.privateMem ((cacheBase+i.val : ℕ) : Word w) = args (slots k)[i] := by
    simpa only [slot_offset] using ready (slots k)[i]
  have body := cached_rows M ports cursor unit (fun i => wires.cursor_disjoint i.dest)
    (fun i => wires.unit_disjoint i.dest) wires.different.symm args (slots k) pc inc read advance cacheBase mid
    rfl hc hone hcache
  let dst := (slots k).foldl (setStatic ports args) mid.reg
  let out := {mid with
    pc := pc (Fin.last (slots k).length)
    reg := Function.update dst cursor ((cacheBase+(slots k).length : ℕ) : Word w)}
  have run := start.append body
  change Prefix M c (List.replicate 5 .tick ++ List.replicate (2*(slots k).length) .tick) out at run
  rw [← List.replicate_add,length_slots] at run
  refine ⟨out,run,rfl,?_,?_,rfl,rfl,?_⟩
  · intro j
    change Function.update dst cursor _ (ports j) = _
    rw [Function.update_of_ne (wires.cursor_disjoint j).symm]
    have readAt (i : Static k) : dst (ports i.dest) = sourceWord x vals i.dest := by
      rw [show dst (ports i.dest) = _ from fold_at ports args (slots k) mid.reg i, ite_eq_left (mem_slots i)]
    have other (j : Source k) (h : ∀ i : Static k, j ≠ i.dest) : dst (ports j) = mid.reg (ports j) :=
      fold_outside ports args _ _ _ (fun i => ports.injective.ne (h i))
    cases j with
    | d | width | bucket | fuel | operand _ => first | exact readAt .d | exact readAt .width | exact readAt .bucket | exact readAt .fuel | exact readAt (.operand _)
    | initial | address | header =>
      rw [other _ (by intro i; cases i <;> simp [Static.dest])]
      simp [mid,prepBank,(wires.unit_disjoint _).symm,(wires.cursor_disjoint _).symm,sourceWord,hzero,ha,hh]
  · change Function.update dst cursor _ cursor = _
    rw [Function.update_self, length_slots]
  · intro i hi hcur hu
    change Function.update dst cursor _ i = _
    rw [Function.update_of_ne hcur]
    unfold dst
    rw [fold_outside ports args _ _ i (fun j => hi j.dest)]
    exact prep_preserve ports site hdr base cursor unit c.reg i hi hcur hu

end PairSimulation.LeafSourceLoad

end VPVNP
end Computability
end OAI
