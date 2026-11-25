import OAI.ThreeFlat.Diagonal.TraceStaticRowEval
import OAI.ThreeFlat.Diagonal.TraceStaticTable
import OAI.ThreeFlat.Diagonal.TraceUniformValue
import OAI.ThreeFlat.Diagonal.TraceCircuitPad

namespace OAI
/-! # Replicating the same public gate table at every row of the RAM trace -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory TraceRows TraceBanks TraceCompose
open TraceRowPackets TraceProgram
variable {F : Type*} [CommRing F] [Fintype F] {w p r k f S d : ℕ}

theorem network_agrees (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (r k d : ℕ) (pin : Fin (S*w) → Bool) :
    (network hF hw hp base st hs hf r k d).eval pin =
      (TraceUniformRow.network hF hw hp hp0 base st hs hf r k d).eval pin := by
  classical
  rw [network,TraceCircuit.assemble_eval,TraceUniformRow.network,TracePacketArray.eval]
  apply Finset.sum_congr rfl; intro hidden _
  apply Finset.prod_congr rfl; intro v _
  let x := fun j : TraceUniformRow.Port w p r k d => (TraceUniformRow.addresses (by omega) S f v j).read hidden pin
  let y := Sum.elim x (ctrlAt (p:=p) (k:=k) hw hs hf base v)
  let table := gateTable hF hw hp base f st r k d
  let raw := fun i => (portSource hw hs hf base v ((Fintype.equivFin (Port w p r k d)).symm i)).read hidden pin
  change table.eval raw = _
  have hy : raw ∘ Fintype.equivFin (Port w p r k d) = y := by
    funext j
    simp only [raw,Function.comp_apply,Equiv.symm_apply_apply]
    cases j <;> rfl
  rw [show table.eval raw = ∏ a, TraceUniformRow.coefficient a
      ((template hF hw hp base f st a).2.eval (raw ∘ Fintype.equivFin (Port w p r k d))) from
    TracePacketArray.one_eval ..,hy]
  exact Finset.prod_congr rfl (fun a _ => congrArg (TraceUniformRow.coefficient a)
    (template_eval hF hw hp hp0 base st hs hf v a x))

/-- The public table, with all executable and advice bits open, computes
the weighted self-advised RAM value on a zero-initialized memory tail. -/
theorem network_advice (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (hp0 : 0 < p) (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1))
    (fit : S+f ≤ 2^(1+d)) {q : ℕ} (textFit : (1+6*p+k)*w ≤ q) (adviceFit : base+q ≤ S)
    (D : Fin q → Bool) (input : Memory w) :
    let m := initialMemory S input
    let h := RAM.memoryWithAdvice base D m
    (network hF hw hp base st hs hf r k d).eval (TracePhysical.headerPins (fun i : Fin S => h i.val)) =
      RAM.adviceValue (RAM.FieldCode.ofCardLe hF) p r k textFit D f st base m := by
  intro m h
  rw [network_agrees hF hw hp hp0 base st hs hf r k d]
  exact TraceUniformRow.network_eval_advice hF hw hp hp0 base st hs hf fit textFit adviceFit D input

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
