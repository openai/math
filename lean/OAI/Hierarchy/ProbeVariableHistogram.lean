import OAI.Hierarchy.ProbeHistogramNative

namespace OAI
/-! # One fixed compactor exposing all histogram target wires -/

noncomputable section
namespace Hierarchy.Probe.VariableHistogram
open scoped Classical BigOperators
open ThreeFlat Diagonal TraceCircuit MotifOuterTerms MotifSelectorChecks
open Routing Routing.StableCompaction
variable {F : Type*} [CommRing F] {r H b : ℕ}

def wordWires (i : Fin r) : Fin (b+H) → BitSource (r*H) (r*b+H*r) :=
  Fin.append (fun j=>.pin ((finProdFinEquiv (i,j)).castAdd _)) (fun a=>.hidden (finProdFinEquiv (i,a)))

def countWires (a : Fin H) : Fin (r+(r+r)) → BitSource (r*H) (r*b+H*r) :=
  Fin.append (fun i=>.hidden (finProdFinEquiv (i,a)))
    (Fin.append (fun _=>.constant true) (fun i=>.pin (Fin.natAdd _ (finProdFinEquiv (a,i)))))

def branch (F : Type*) [CommRing F] (positive : 0<H) (r b : ℕ) :
    (Fin r ⊕ Fin H) → Component F (r*H) (r*b+H*r)
  | .inl i=>⟨_,ConstantKernelLUT.network (checkLut (NativeHistogram.valid H) (NativeHistogram.letter positive)),wordWires i⟩
  | .inr a=>⟨_,NativeHistogram.compactor F r,countWires a⟩

def network (F : Type*) [CommRing F] (positive : 0<H) (r b : ℕ) : BitNetwork F (r*b+H*r) :=
  BitNetwork.glue (fun i=>(branch F positive r b i).net) (fun i=>(branch F positive r b i).wire)

def pins (z : Fin r→Fin b → Bool) (out : Fin H→Fin r → Bool) := Fin.append (blocks r b z) (blocks H r out)

private theorem word_at (z : Fin r→Fin b → Bool) (out : Fin H→Fin r → Bool)
    (mask : Fin r→Fin H → Bool) (i : Fin r) :
    (fun j=>(wordWires i j).read (blocks r H mask) (pins z out))=Fin.append (z i) (mask i) := by
  funext j
  refine Fin.addCases (fun _=>?_) (fun _=>?_) j <;> simp [wordWires,pins,BitSource.read,-Fin.natAdd_eq_addNat]

private theorem count_at (z : Fin r→Fin b → Bool) (out : Fin H→Fin r → Bool)
    (mask : Fin r→Fin H → Bool) (a : Fin H) :
    (fun j=>(countWires a j).read (blocks r H mask) (pins z out))=
      Fin.append (fun i=>mask i a) (Fin.append (fun _=>true) (out a)) := by
  funext j
  refine Fin.addCases (fun _=>?_) (fun t=>?_) j
  · simp [countWires,BitSource.read]
  · refine Fin.addCases (fun _=>?_) (fun _=>?_) t <;> simp [countWires,pins,BitSource.read,-Fin.natAdd_eq_addNat]

def stream (hist : Histogram (Fin H) r) : Fin H→Fin r → Bool := fun a=>unary (hist.val a).val

theorem eval (positive : 0<H) (z : Fin r→Fin b → Bool) (out : Fin H→Fin r → Bool) :
    (network F positive r b).eval (pins z out)=
      if (∀ i,NativeHistogram.valid H (z i)) ∧ out=stream (histogram (fun i=>NativeHistogram.letter positive (z i)))
      then 1 else 0 := by
  let word:=fun i=>NativeHistogram.letter positive (z i)
  let desired:=fun i a=>symbolMask word a i
  rw [network,BitNetwork.glue_eval,←(blocks r H).sum_comp]
  let payload (m : Fin r→Fin H → Bool) :=
    (∏ i,if checks (NativeHistogram.valid H) (NativeHistogram.letter positive) (z i) (m i) then (1:F) else 0) *
      (∏ a,if out a=unary (active (fun i=>m i a)).card then (1:F) else 0)
  have each (m : Fin r→Fin H → Bool) :
      (∏ i,((branch F positive r b i).net).eval (fun j=>
        ((branch F positive r b i).wire j).read (blocks r H m) (pins z out)))=payload m := by
    rw [Fintype.prod_sum_type]
    apply congrArg₂ (·*·)
    · apply Finset.prod_congr rfl
      intro i _
      change (ConstantKernelLUT.network (F:=F) (checkLut (NativeHistogram.valid H) (NativeHistogram.letter positive))).eval
        (fun j => (wordWires i j).read (blocks r H m) (pins z out)) = _
      rw [word_at,ConstantKernelLUT.network_eval]
      simp [checkLut,-Fin.natAdd_eq_addNat]
    · apply Finset.prod_congr rfl
      intro a _
      change (NativeHistogram.compactor F r).eval
        (fun j => (countWires a j).read (blocks r H m) (pins z out)) = _
      rw [count_at,NativeHistogram.compactor_run,compact_ones]
  simp only [each]
  rw [Fintype.sum_eq_single desired]
  · have counts (a : Fin H) : (active (fun i=>desired i a)).card=((histogram word).val a).val := by
      simp [desired,histogram,occurrence,active,symbolMask]
    simp only [payload,counts,Fintype.prod_boole,ite_mul,one_mul,zero_mul]
    have flags : (∀i,checks (NativeHistogram.valid H) (NativeHistogram.letter positive) (z i) (desired i)) ↔
        ∀i,NativeHistogram.valid H (z i) := by simp [checks,desired,symbolMask,word]
    have unaryEq : (∀ a,out a=unary ((histogram word).val a).val) ↔ out=stream (histogram word) :=
      ⟨funext,fun eq a=>congrFun eq a⟩
    simp only [flags,unaryEq]
    by_cases ok : ∀ i, NativeHistogram.valid H (z i)
    · simp [ok,word]
    · simp [ok]
  · intro m diff
    have bad : ¬∀ i,checks (NativeHistogram.valid H) (NativeHistogram.letter positive) (z i) (m i) := by
      intro good
      exact diff (funext (fun i=>funext (fun a=>(good i).2 a)))
    simp only [payload,Fintype.prod_boole,ite_eq_right bad,zero_mul]

theorem cost (positive : 0<H) :
    (network F positive r b).cells+(network F positive r b).internal ≤
      r*(2^(b+H)*(b+H+1))+r*H+r*2^(b+H)+128000*H*(r+1)*(Nat.log 2 (r+1)+2)^3 := by
  let target:=histogram (fun _ : Fin r=>(⟨0,positive⟩ : Fin H))
  apply Eq.trans_le _ (NativeHistogram.cost (F:=F) positive b target)
  simp [network,branch,BitNetwork.glue_cells,BitNetwork.glue_internal,Fintype.sum_sum_type,
    NativeHistogram.network,MotifSelectorChecks.network_cells,MotifSelectorChecks.network_hidden,
    ConstantKernelLUT.network_cells,ConstantKernelLUT.network_internal]

end Hierarchy.Probe.VariableHistogram
end

end OAI
