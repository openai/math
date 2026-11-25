import OAI.Computability.BorderVNP.RoutingISACallInversion
import OAI.Computability.BorderVNP.RoutingISACallSetup

/-!
# Exact private paths at one assigned cell

The owner comparison is made on the actual directory word. Only the selected team
loads the two argument fields. The returned event has exactly the words, choice bits
and sign accepted by private routine zero, and all paths preserve shared memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.CellDispatch

open VPVNP.BurstRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem owner_guard {f : Frame} {i : ℕ} {s : Bank w} {m : Memory w}
    (ready : f.Ready i s) (owner : s 8 = m (f.address i)) :
    s 3 = s 8 ↔ (m (f.address i)).val = f.team := by
  rw [owner]
  exact ⟨fun e => (congrArg Fin.val e.symm).trans ready.2.2.2.1,
    fun e => Fin.ext (ready.2.2.2.1.trans e.symm)⟩

/-- Each admitted private path at this directory row realizes exactly the indicated
signed burst. A skipped row has a unique ordinary bookkeeping history. -/
theorem row_run {f : Frame} {i : ℕ} {s : Bank w} {m : Memory w}
    (ready : f.Ready i s) (fit : f.address i + 2 < 2^w) (more : i < f.count)
    {result : Option Outcome} (valid : f.Valid m macros i result) :
    ∃ es t, Runs pub macros body s m es t m ∧ f.Ready (i+1) t ∧
      tick w :: es = f.rowTrace m i result := by
  obtain ⟨u,ru,hu,ptr,owner⟩ := owner_run (pub := pub) (macros := macros) (m := m) ready fit
  by_cases own : (m (f.address i)).val = f.team
  · rw [Frame.Valid, ite_eq_left own] at valid
    obtain ⟨o,rfl,span,path⟩ := valid
    obtain ⟨v,rv,hv,base,len⟩ := args_run (pub := pub) (macros := macros) (m := m) hu ptr fit
    have call : Runs pub macros (.call 0 9 10) v m [f.callEvent m i o] v m := by
      apply private_iff.mpr
      rw [base, len]
      exact ⟨span,rfl,rfl,o,path,rfl⟩
    have br := Runs.ifEq (s := u) (m := m) (pub := pub) (macros := macros) (x := 3) (y := 8) (a := .seq readArgs (.call 0 9 10)) (b := .nop)
      (by simpa only [(owner_guard hu owner).2 own, ite_true] using rv.seq call)
    obtain ⟨z,rz,hz⟩ := increment_run (pub := pub) (macros := macros) (m := m) hv more
    exact ⟨_,z,ru.seq (br.seq rz),hz,rfl⟩
  · have hn : u 3 ≠ u 8 := mt (owner_guard hu owner).1 own
    have : result = none := by simpa only [Frame.Valid, own, ite_false] using valid
    subst result
    have nop : Runs pub macros .nop u m [tick w] u m := Runs.localStep m rfl rfl
    have br := Runs.ifEq (s := u) (m := m) (pub := pub) (macros := macros) (x := 3) (y := 8) (a := .seq readArgs (.call 0 9 10)) (b := .nop)
      (by simpa only [hn, ite_false] using nop)
    obtain ⟨z,rz,hz⟩ := increment_run (pub := pub) (macros := macros) (m := m) hu more
    exact ⟨_,z,ru.seq (br.seq rz),hz,rfl⟩

/-- Conversely, every normal return at this row is the history of an admitted private
outcome on the owner's actual interval, or the skip history of a different team. -/
theorem row_decode {f : Frame} {i : ℕ} {s : Bank w} {m : Memory w}
    (ready : f.Ready i s) (fit : f.address i + 2 < 2^w) (more : i < f.count)
    {es t mt} (run : Runs pub macros body s m es t mt) :
    ∃ result, f.Valid m macros i result ∧ f.Ready (i+1) t ∧ mt = m ∧
      tick w :: es = f.rowTrace m i result := by
  obtain ⟨_,_,_,_,rfl,ownerActual,rest⟩ := seq_split run
  obtain ⟨u,ownerRun,hu,ptr,owner⟩ := owner_run (pub := pub) (macros := macros) (m := m) ready fit
  obtain ⟨rfl,rfl,rfl⟩ := ownerRun.unique_of_deterministic (by decide) ownerActual
  obtain ⟨_,after,afterMem,_,rfl,test,inc⟩ := seq_split rest
  obtain ⟨_,rfl,branch⟩ := eq_split test
  by_cases own : (m (f.address i)).val = f.team
  · simp only [(owner_guard hu owner).2 own, ite_true] at branch
    obtain ⟨_,_,_,_,rfl,argsActual,called⟩ := seq_split branch
    obtain ⟨v,argsRun,hv,base,len⟩ := args_run (pub := pub) (macros := macros) (m := m) hu ptr fit
    obtain ⟨rfl,rfl,rfl⟩ := argsRun.unique_of_deterministic (by decide) argsActual
    obtain ⟨span, hAfter, hMem, o,path,rfl⟩ := private_iff.mp called
    subst after afterMem
    obtain ⟨z,incRun,hz⟩ := increment_run (pub := pub) (macros := macros) (m := m) hv more
    obtain ⟨rfl,rfl,rfl⟩ := incRun.unique_of_deterministic (by decide) inc
    refine ⟨some o,?_,hz,rfl,?_⟩
    · rw [Frame.Valid, ite_eq_left own]
      exact ⟨o,rfl,by simpa only [base,len] using span,by simpa only [Frame.burst,base,len] using path⟩
    · simp only [base,len]; rfl
  · have hn : u 3 ≠ u 8 := fun h => own ((owner_guard hu owner).1 h)
    simp only [hn, ite_false] at branch
    have nop : Runs pub macros .nop u m [tick w] u m := Runs.localStep m rfl rfl
    obtain ⟨rfl,rfl,rfl⟩ := nop.unique_of_deterministic (by decide) branch
    obtain ⟨z,incRun,hz⟩ := increment_run (pub := pub) (macros := macros) (m := m) hu more
    obtain ⟨rfl,rfl,rfl⟩ := incRun.unique_of_deterministic (by decide) inc
    exact ⟨none,by simp [Frame.Valid,own],hz,rfl,rfl⟩

end RoutingISA.CellDispatch

end BorderVNP
end Computability
end OAI
