import OAI.ThreeFlat.Diagonal.CompressorStageBlocks

namespace OAI
/-! # A single width-independent row-work coefficient for the shrink navigator -/

namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ}

def Pass.bounded (p : Pass w) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w) (B : ℕ) : Prop :=
  match p with
  | .one s => (headerRead m current s.length).val ≤ B
  | .seq a b => a.bounded current pub m B ∧ b.bounded current pub (a.execute current pub m).2 B

theorem Recipe.time_le (p : Recipe) (current : Word w) (pub : Fin 1 → Word w) (m : Memory w)
    (B : ℕ) (bound : (p.install current).bounded current pub m B) :
    ((p.install current).execute current pub m).1 ≤ (B+1)*p.cost := by
  induction p generalizing m with
  | one f lo len =>
    change 11+(headerRead m current len).val*(2*(Template.emit current f).binds+4) ≤ (B+1)*(15+2*f.work)
    rw [Template.emit_work]
    have h : (headerRead m current len).val ≤ B := bound
    calc
      _ ≤ 11+B*(2*f.work+4) := Nat.add_le_add_left (Nat.mul_le_mul_right _ h) _
      _ ≤ _ := by nlinarith
  | seq a b ia ib =>
    have h := Nat.add_le_add (ia _ bound.1) (ib _ bound.2)
    simpa only [Recipe.cost,Nat.mul_add,Pass.execute,Recipe.install] using h

/-- One coefficient serves all word sizes, pointer cells, and input memories.
The fixed base degree, full degree, and finite surviving multiplicities
determine it before the simulator scale is chosen. -/
def coefficient (s : Graph.Stage) (tagBits : ℕ) := (before s tagBits).cost+(afterRecipe s).cost

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
