import OAI.ThreeFlat.Diagonal.TraceLocalNetwork
import OAI.ThreeFlat.Diagonal.TraceBoolNet

namespace OAI
/-! # One trivalent transcript for all bits of a word instruction -/

noncomputable section
namespace Hierarchy.TaggedShorterBoolBatch
open ThreeFlat Diagonal TraceCircuit
open scoped Classical BigOperators

variable {F σ : Type*} {c p : ℕ}

private def outRow [Zero F] [One F] (B : TraceCompose.Batch σ (Fin c))
    (input : σ → Fin p) (expected : Fin c → Fin p) (i : Fin c) : Cell F B.size p :=
  ⟨![address (fun s => .pin (input s)) id (B.port i),.pin (expected i),.constant false],
    fun z => if z 0=z 1 then 1 else 0⟩

def network [Zero F] [One F] (B : TraceCompose.Batch σ (Fin c))
    (input : σ → Fin p) (expected : Fin c → Fin p) : BitNetwork F p :=
  let rows : Fin (B.size+c) → Cell F B.size p := Fin.addCases
    (gateRows (F:=F) (fun s => .pin (input s)) B.program id)
    (outRow B input expected)
  ⟨B.size,B.size+c,fun i => (rows i).source,fun i => (rows i).table⟩

theorem eval [CommRing F] (B : TraceCompose.Batch σ (Fin c))
    (input : σ → Fin p) (expected : Fin c → Fin p) (pin : Fin p → Bool) :
    (network (F:=F) B input expected).eval pin =
      if ∀ i, B.eval (pin ∘ input) i=pin (expected i) then 1 else 0 := by
  classical
  let checks := gateRows (F:=F) (fun s => .pin (input s)) B.program id
  have factor (ws : Fin B.size → Bool) (i : Fin c) :
      (outRow (F:=F) B input expected i).eval pin ws =
      if (B.port i).read id (pin ∘ input) ws = pin (expected i) then 1 else 0 := by
    have read : (address (fun s => .pin (input s)) id (B.port i)).read ws pin =
        (B.port i).read id (pin ∘ input) ws := address_read _ _ _ _ _
    change (if (address (fun s => .pin (input s)) id (B.port i)).read ws pin =
        pin (expected i) then 1 else 0) = _
    by_cases h : (B.port i).read id (pin ∘ input) ws = pin (expected i)
    · rw [ite_eq_left (read.trans h),ite_eq_left h]
    · rw [ite_eq_right (fun q => h (read.symm.trans q)),ite_eq_right h]
  have weight (ws : Fin B.size → Bool) : (network (F:=F) B input expected).weight pin ws =
      if ws=B.program.run (pin ∘ input) then
        (if ∀ i, B.eval (pin ∘ input) i=pin (expected i) then 1 else 0) else 0 := by
    change (∏ i : Fin (B.size+c),
      ((Fin.addCases (motive:=fun _=>Cell F B.size p) checks (outRow B input expected)) i).eval pin ws) = _
    rw [Fin.prod_univ_add]
    simp only [Fin.addCases_left,Fin.addCases_right,checks,gateRows_weight,Function.comp_id,factor,Fintype.prod_boole]
    have gateInput : (fun s => (BitSource.pin (input s) : BitSource B.size p).read ws pin)=pin ∘ input := rfl
    rw [gateInput]
    by_cases eqn : ws = B.program.run (pin ∘ input)
    · subst ws
      rw [ite_eq_left rfl,ite_eq_left rfl,one_mul]
      by_cases hits : ∀ i, B.eval (pin ∘ input) i=pin (expected i)
      · exact (ite_eq_left hits).trans (ite_eq_left hits).symm
      · exact (ite_eq_right hits).trans (ite_eq_right hits).symm
    · rw [ite_eq_right eqn,ite_eq_right eqn,zero_mul]
  change (∑ ws : Fin B.size → Bool, (network (F:=F) B input expected).weight pin ws)=_
  simp only [weight]
  simp

theorem size [Zero F] [One F] (B : TraceCompose.Batch σ (Fin c))
    (input : σ → Fin p) (expected : Fin c → Fin p) :
    (network (F:=F) B input expected).cells+(network (F:=F) B input expected).internal=2*B.size+c := by
  change B.size+c+B.size=_
  omega

/-- All output references of a bounded-fan-in Boolean network share a single
transcript and hence its gate count is paid only once. -/
def wordBatch {n m : ℕ} (pins : Fin n → σ ⊕ Bool) (N : ExactQuantumFactoring.BooleanNetwork n m) :
    TraceCompose.Batch σ (Fin m) :=
  ⟨N.net.count,TraceBoolNet.program pins N.net,fun j => TraceBoolNet.wire pins N.net (N.output j)⟩

theorem wordBatch_eval {n m : ℕ} (pins : Fin n → σ ⊕ Bool)
    (N : ExactQuantumFactoring.BooleanNetwork n m) (x : σ → Bool) (j : Fin m) :
    (wordBatch pins N).eval x j=N.eval (fun i => (pins i).elim x id) j :=
  TraceBoolNet.wire_eval pins N.net x (N.output j)

end Hierarchy.TaggedShorterBoolBatch

end
end OAI
