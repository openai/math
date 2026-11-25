import OAI.ThreeFlat.Diagonal.TraceCircuit
import OAI.ThreeFlat.Diagonal.TraceCompose

namespace OAI
/-! # A scalar-weighted family of local Boolean checks as trivalent cells -/

namespace ThreeFlat.Diagonal.TraceCircuit

open Computability.VPVNP (Ref)
open Computability.VPVNP.BooleanTranscript

variable {F σ : Type*} {p k c : ℕ}

/-- Take the designated Boolean output of each circuit as a unary scalar
factor over the chosen coefficient ring. Identity wires, invalid-bit
indicators and terminal field factors all use the same construction. -/
def outputBatch [Zero F] [One F] (B : TraceCompose.Batch σ (Fin c)) (input : σ → Fin p)
    (scalar : Fin c → Bool → F) : BitNetwork F p :=
  let rows : Fin (B.size+c) → Cell F B.size p := Fin.addCases
    (gateRows (F:=F) (fun i => .pin (input i)) B.program id)
    (fun i => ⟨![address (fun i => .pin (input i)) id (B.port i),.constant false,.constant false],
      fun z => scalar i (z 0)⟩)
  ⟨B.size,B.size+c,fun i => (rows i).source,fun i => (rows i).table⟩

private theorem outputBatch_weight [CommRing F] (B : TraceCompose.Batch σ (Fin c))
    (input : σ → Fin p) (scalar : Fin c → Bool → F) (pin : Fin p → Bool) (ws : Fin B.size → Bool) :
    (outputBatch B input scalar).weight pin ws =
      if ws = B.program.run (pin ∘ input) then ∏ i, scalar i ((B.port i).read id (pin ∘ input) ws) else 0 := by
  classical
  let tail := fun i => (⟨![address (fun i => .pin (input i)) id (B.port i),
      .constant false,.constant false],fun z => scalar i (z 0)⟩ : Cell F B.size p)
  let checks := gateRows (F:=F) (fun i => .pin (input i)) B.program id
  change (∏ i : Fin (B.size+c), ((Fin.addCases (motive := fun _ => Cell F B.size p) checks tail) i).eval pin ws) = _
  rw [Fin.prod_univ_add]
  simp only [Fin.addCases_left, Fin.addCases_right, checks]
  rw [gateRows_weight]
  simp only [Function.comp_id, BitSource.read, tail, Cell.eval]
  change (if ws = B.program.run (pin ∘ input) then 1 else 0) *
    (∏ i, scalar i ((address (fun i => .pin (input i)) id (B.port i)).read ws pin)) = _
  have hout (i : Fin c) :
      (address (fun j => .pin (input j)) id (B.port i)).read ws pin =
        (B.port i).read id (pin ∘ input) ws := by
    exact address_read (fun j => .pin (input j)) id (B.port i) pin ws
  simp only [hout]
  by_cases h : ws = B.program.run (pin ∘ input) <;> simp [h]

/-- The local output factor network has one cell and one hidden wire per
deterministic gate, together with exactly one unary cell per scalar factor. -/
theorem outputBatch_eval [CommRing F] (B : TraceCompose.Batch σ (Fin c))
    (input : σ → Fin p) (scalar : Fin c → Bool → F) (pin : Fin p → Bool) :
    (outputBatch B input scalar).eval pin = ∏ i, scalar i (B.eval (pin ∘ input) i) := by
  classical
  change (∑ ws : Fin B.size → Bool, (outputBatch B input scalar).weight pin ws) = _
  simp [outputBatch_weight, TraceCompose.Batch.eval]

def localNetwork [Zero F] [One F] (packets : Fin c → TraceCompose.Packet σ) (input : σ → Fin p)
    (scalar : Fin c → Bool → F) : BitNetwork F p :=
  outputBatch (TraceCompose.gather packets) input scalar

theorem localNetwork_eval [CommRing F] (packets : Fin c → TraceCompose.Packet σ) (input : σ → Fin p)
    (scalar : Fin c → Bool → F) (pin : Fin p → Bool) :
    (localNetwork packets input scalar).eval pin =
      ∏ i, scalar i ((packets i).2.eval (pin ∘ input)) := by
  simp [localNetwork, outputBatch_eval, TraceCompose.gather_eval]

@[simp] theorem localNetwork_cells [Zero F] [One F] (packets : Fin c → TraceCompose.Packet σ)
    (input : σ → Fin p) (scalar : Fin c → Bool → F) :
    (localNetwork packets input scalar).cells = (∑ i, (packets i).1)+c := by
  exact congrArg (·+c) (TraceCompose.gather_size packets)

end ThreeFlat.Diagonal.TraceCircuit

end OAI
