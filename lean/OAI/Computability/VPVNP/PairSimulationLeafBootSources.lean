import OAI.Computability.VPVNP.PairSimulationLeafBootRows

/-! # The cached-source and capacity prefix of the linked leaf startup -/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.LeafBoot

open BurstRAM PrivateRAM RAMTape LeafStartup StackMachine LeafRegisterBank PrimedCounter.GuessWord
open scoped Fin.CommRing

variable {w p r k d e : ℕ} (pc : Label → Fin p) (reg : Reg ↪ Fin r) (nPub : Fin k) (done : Fin p)
  (M : Machine w p r k)

theorem source_prefix (x : VirtualSite.Input d e w) (args : Fin 34 → Word w) (n base : ℕ)
    (link : Linked pc reg nPub done M) (c : Config w p r) (entry : c.pc = pc (.pre 0))
    (addr : c.reg (sources reg .address) = x.addrWord) (hdr : c.reg (sources reg .header) = x.headerWord)
    (initial : x.initialWord = 0) (hb : c.reg (cacheBase reg) = (base : Word w))
    (cached : LeafSourceLoad.Cached base c.privateMem (fun j => sourceWord x args j.dest))
    (hn : M.publicData nPub = (n : Word w)) :
    ∃ out, Prefix M c (List.replicate 89 .tick) out ∧ out.pc = scalarEntry pc ∧
      (∀ j, out.reg (sources reg j) = sourceWord x args j) ∧
      out.reg (pointer reg .cursor) = ((base+38 : ℕ) : Word w) ∧
      out.reg (pointer reg .stride) = ((n^40 : ℕ) : Word w) ∧
      out.privateMem = c.privateMem ∧ out.persistent = c.persistent ∧ out.reg (nodeBase reg) = c.reg (nodeBase reg) ∧
      ∀ i, i ∉ Set.range reg → out.reg i = c.reg i := by
  let inc (i : Fin (LeafSourceLoad.slots 34).length) := pc (.increment (i.cast (by rw [LeafSourceLoad.length_slots])))
  have hread (i : Fin (LeafSourceLoad.slots 34).length) :
      M.code (readPC pc i.castSucc) = LeafSourceLoad.readInstr (sources reg) (pointer reg .cursor)
        (inc i) (LeafSourceLoad.slots 34)[i] := by
    let j : Fin 38 := i.cast (by rw [LeafSourceLoad.length_slots])
    have he : readPC pc i.castSucc = pc (.read j) := by simp [readPC,j, show i.val < 38 by simpa using i.isLt]; congr 2
    rw [he]; exact link (.read j)
  have hadv (i : Fin (LeafSourceLoad.slots 34).length) : M.code (inc i) =
      LeafSourceLoad.incInstr (pointer reg .cursor) (stack reg .one) (readPC pc i.succ) :=
    link (.increment (i.cast (by rw [LeafSourceLoad.length_slots])))
  obtain ⟨mid,run,hm,values,cur,mem,persist,fr⟩ := LeafSourceLoad.cachedSources x args M (sources reg)
    (sources reg .address) (sources reg .header) (cacheBase reg) (pointer reg .cursor) (stack reg .one)
    (pc ∘ Label.pre) (readPC pc) inc (fun i => link (.pre i)) hread hadv (wiring reg) base c entry addr hdr initial hb cached
  have atCap : mid.pc = pc (.capacity 0) := by simpa [readPC] using hm
  have sep : pointer reg .stride ≠ tmp reg := by simp [pointer,tmp]
  obtain ⟨out,capRun,hpc,stride,hmem,hstate,frame⟩ := LeafCapacity.run M (pc ∘ Label.capacity)
    (pointer reg .stride) (tmp reg) sep nPub (scalarEntry pc) (fun i => link (.capacity i)) mid atCap n hn
  have all := run.append capRun
  rw [← List.replicate_add] at all
  refine ⟨out,all,hpc,?_,?_,stride,hmem.trans mem,hstate.trans persist,?_,?_⟩
  · exact fun j => (frame _ (by simp [pointer]) (by simp [tmp])).trans (values j)
  · exact (frame _ (by simp [pointer]) (by simp [pointer,tmp])).trans cur
  · exact (frame _ (by simp [nodeBase,pointer]) (by simp [nodeBase,tmp])).trans
      (fr _ (by simp [nodeBase]) (by simp [nodeBase,pointer]) (by simp [nodeBase,stack]))
  · intro i hi
    have ne (j : Reg) : i ≠ reg j := fun he => hi ⟨j,he.symm⟩
    exact (frame i (ne _) (ne _)).trans (fr i (fun _ => ne _) (ne _) (ne _))

end PairSimulation.LeafBoot

end VPVNP
end Computability
end OAI
