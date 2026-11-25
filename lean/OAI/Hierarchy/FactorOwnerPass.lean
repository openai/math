import OAI.Hierarchy.FactorPrefixOwner
import OAI.Hierarchy.FactorBucketPass

namespace OAI
/-! # The actual native owner table in physical factor order -/

namespace Hierarchy.FactorBucketRAM

open FactorAllocation Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
variable {w width N d T : ℕ}

structure OwnerLayout (N classes : ℕ) where
  keys : ℕ
  counts : ℕ
  output : ℕ
  beforeCounts : keys+N≤counts
  beforeOutput : counts+classes≤output

def classIndex (g : Key w d) : ℕ := (finFunctionFinEquiv g).val

theorem owner_natural (v : Parameters width) (m : Memory width)
    (bank : OwnerLayout N ((20*(w+1)+2)^d)) (i : Fin N) (g : Key w d)
    (pkeys : v 8=(bank.keys:Word width)) (pcounts : v 9=(bank.counts:Word width))
    (pout : v 10=(bank.output:Word width)) (pt : v 4=(T:Word width))
    (smallT : T<2^width) (fits : bank.output+N≤2^width)
    (keyRead : m (bank.keys+i.val)=(classIndex g:Word width))
    (a : ℕ) (countRead : (m (bank.counts+classIndex g)).val=a) :
    ownerStep v (i.val:Word width) m =
      Function.update (Function.update m (bank.counts+classIndex g) ((a+1:ℕ):Word width))
        (bank.output+i.val) ((a%T:ℕ):Word width) := by
  have kb := bank.beforeCounts
  have cb := bank.beforeOutput
  have gi : classIndex g < (20*(w+1)+2)^d := (finFunctionFinEquiv g).isLt
  have ii := i.isLt
  have kFits : bank.keys+i.val<2^width := by omega
  have cFits : bank.counts+classIndex g<2^width := by omega
  have oFits : bank.output+i.val<2^width := by omega
  have aFit : a<2^width := countRead ▸ (m (bank.counts+classIndex g)).isLt
  have valEq : m (bank.counts+classIndex g)=(a:Word width) := by rw [←countRead]; simp
  simp only [ownerStep,pkeys,pcounts,pout,pt,←Nat.cast_add,Fin.val_cast_of_lt kFits,
    keyRead,Fin.val_cast_of_lt cFits,BinaryOp.eval,Fin.val_cast_of_lt smallT,valEq]
  rw [GridPassageRAMRow.writeMemory_nat _ _ oFits,GridPassageRAMRow.writeMemory_nat _ _ cFits]
  simp [Nat.mod_eq_of_lt aFit]

/-- The full one-pass state relates every native count and every completed owner
to its mathematical value. Key words were produced by the preceding digit pass. -/
theorem owner_state (ht : 0<T) (cost : Fin N → Fin d → ℕ) (v : Parameters width)
    (bank : OwnerLayout N ((20*(w+1)+2)^d)) (m : Memory width)
    (pkeys : v 8=(bank.keys:Word width)) (pcounts : v 9=(bank.counts:Word width))
    (pout : v 10=(bank.output:Word width)) (pt : v 4=(T:Word width))
    (smallT : T<2^width) (fits : bank.output+N≤2^width)
    (keys : ∀ i : Fin N, m (bank.keys+i.val)=(classIndex (key w cost i):Word width))
    (clear : ∀ g : Key w d, m (bank.counts+classIndex g)=0) :
    (∀ a<bank.counts, iterRows ownerStep v m N a=m a) ∧
    (∀ i : Fin N, iterRows ownerStep v m N (bank.output+i.val) =
      ((owner ht w cost i).val:Word width)) := by
  let mem := iterRows ownerStep v m
  let tag := key w cost
  have kb := bank.beforeCounts
  have cb := bank.beforeOutput
  have gi (g : Key w d) : classIndex g < (20*(w+1)+2)^d := (finFunctionFinEquiv g).isLt
  have countsBound (n : ℕ) (g : Key w d) : prefixCount w cost n g ≤ n := by
    apply (List.length_filter_le ..).trans
    simp [List.length_take]
  have inv (n : ℕ) (hn : n≤N) :
      (∀ a<bank.counts, mem n a=m a) ∧
      (∀ g : Key w d, mem n (bank.counts+classIndex g) =
        ((prefixCount w cost n g):Word width)) ∧
      (∀ j : Fin N, j.val<n → mem n (bank.output+j.val) = ((owner ht w cost j).val:Word width)) := by
    induction n with
    | zero => simpa [mem,iterRows,prefix_zero] using And.intro (by simp : ∀ a<bank.counts, m a=m a) (And.intro clear (by simp :
          ∀ j : Fin N, j.val<0 → m (bank.output+j.val) = ((owner ht w cost j).val:Word width)))
    | succ n ih =>
      let j : Fin N := ⟨n,by omega⟩
      have jval : j.val=n := rfl
      obtain ⟨oldKeys,oldCounts,oldOut⟩ := ih (by omega)
      have readKey : mem n (bank.keys+j.val)=(classIndex (tag j):Word width) := by
        rw [oldKeys _ (by have := j.isLt; omega),keys j]
      have oldBound : prefixCount w cost n (tag j)<2^width := by
        have := countsBound n (tag j); omega
      have oldRead : (mem n (bank.counts+classIndex (tag j))).val = prefixCount w cost n (tag j) := by
        rw [oldCounts,Fin.val_cast_of_lt oldBound]
      have row := owner_natural v (mem n) bank j (tag j) pkeys pcounts pout pt smallT fits
        readKey (prefixCount w cost n (tag j)) oldRead
      have state : mem (n+1) = _ := row
      rw [state]
      constructor
      · intro a ha
        rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega),oldKeys a ha]
      constructor
      · intro g
        have gl := gi g
        have jl := gi (tag j)
        rw [Function.update_of_ne (by omega),←jval,prefix_succ]
        by_cases eq : g=tag j
        · subst g; simp [tag,jval]
        · have ne : bank.counts+classIndex g ≠ bank.counts+classIndex (tag j) := by
            intro same
            exact eq (finFunctionFinEquiv.injective (Fin.ext (Nat.add_left_cancel same)))
          rw [Function.update_of_ne ne,Function.update_of_ne eq,oldCounts]
      · intro f hf
        by_cases eq : f=j
        · subst f
          simp [jval,owner_eq_prefix ht,tag]
        · have fv : f.val≠n := fun e => eq (Fin.ext (e.trans jval.symm))
          have jl := gi (tag j)
          rw [Function.update_of_ne (by omega),Function.update_of_ne (by omega)]
          exact oldOut f (by omega)
  exact ⟨(inv N le_rfl).1,fun i=>(inv N le_rfl).2.2 i i.isLt⟩

theorem owner_table (ht : 0<T) (cost : Fin N → Fin d → ℕ) (v : Parameters width)
    (bank : OwnerLayout N ((20*(w+1)+2)^d)) (m : Memory width)
    (pkeys : v 8=(bank.keys:Word width)) (pcounts : v 9=(bank.counts:Word width))
    (pout : v 10=(bank.output:Word width)) (pt : v 4=(T:Word width))
    (smallT : T<2^width) (fits : bank.output+N≤2^width)
    (keys : ∀ i : Fin N, m (bank.keys+i.val)=(classIndex (key w cost i):Word width))
    (clear : ∀ g : Key w d, m (bank.counts+classIndex g)=0) (i : Fin N) :
    iterRows ownerStep v m N (bank.keys+i.val) = (classIndex (key w cost i):Word width) ∧
    iterRows ownerStep v m N (bank.output+i.val) = ((owner ht w cost i).val:Word width) := by
  have all := owner_state ht cost v bank m pkeys pcounts pout pt smallT fits keys clear
  exact ⟨(all.1 _ (by have := bank.beforeCounts; have := i.isLt; omega)).trans (keys i),all.2 i⟩

end Hierarchy.FactorBucketRAM

end OAI
