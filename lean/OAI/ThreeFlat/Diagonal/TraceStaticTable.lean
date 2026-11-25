import OAI.ThreeFlat.Diagonal.TraceStaticRow
import OAI.ThreeFlat.Diagonal.TraceCircuitPad

namespace OAI
/-! # Replicating the same public gate table at every row of the RAM trace -/

namespace ThreeFlat.Diagonal.TraceStaticRow

open Computability.VPVNP BurstRAM BurstRAM.PrivateRAM RAMMemory TraceRows TraceBanks TraceCompose
open TraceRowPackets TraceProgram
variable {F : Type*} [CommRing F] [Fintype F] {w p r k f S d : ℕ}

noncomputable def gateTable (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base f : ℕ) (st : Word w) (r k d : ℕ) : BitNetwork F (Fintype.card (Port w p r k d)) :=
  TracePacketArray.one (template hF hw hp base f st) TraceUniformRow.coefficient

noncomputable def network (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k d : ℕ) : BitNetwork F (S*w) :=
  let table := gateTable hF hw hp base f st r k d
  TraceCircuit.assemble (fun _ : Fin (2^d) => TraceCircuit.networkCells table)
    (fun v i => portSource hw hs hf base v ((Fintype.equivFin (Port w p r k d)).symm i))

@[simp] theorem table_internal (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base f : ℕ) (st : Word w) (r k d : ℕ) :
    (gateTable hF hw hp base f st r k d).internal =
      ∑ a : TraceUniformRow.Check F w p k, (template (r:=r) (d:=d) hF hw hp base f st a).1 :=
  TracePacketArray.one_internal ..

theorem table_internal_le_cells (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base f : ℕ) (st : Word w) (r k d : ℕ) :
    (gateTable hF hw hp base f st r k d).internal ≤ (gateTable hF hw hp base f st r k d).cells := by
  unfold gateTable
  rw [TracePacketArray.one_count]
  omega

@[simp] theorem count_cells (hF : Fintype.card F ≤ 2^w) (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1))
    (base : ℕ) (st : Word w) (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (r k d : ℕ) :
    (network hF hw hp base st hs hf r k d).cells = 2^d*(gateTable hF hw hp base f st r k d).cells := rfl

end ThreeFlat.Diagonal.TraceStaticRow

end OAI
