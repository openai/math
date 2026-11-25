import OAI.Hierarchy.TaggedShorterHistoryOrder
import OAI.ThreeFlat.Diagonal.TraceLocalNetwork

namespace OAI
/-! # Trivalent predecessor checks on the actual sorted record bits -/

noncomputable section
namespace Hierarchy.TaggedShorterHistoryOrder
open ThreeFlat Routing Diagonal
open Computability.VPVNP.BurstRAM Computability.VPVNP.RAMMemory Computability.VPVNP.RAMSerialization
open TraceAdjacent
open scoped Classical BigOperators

variable {w m : ℕ}

def offset : (l : List (Fin 7)) → Fin l.length → Fin w → Fin (width w l)
  | [], i, _ => Fin.elim0 i
  | _::l, i, j => Fin.cases (Fin.natAdd (width w l) j) (fun k => (offset l k j).castAdd w) i

theorem read_offset (v : Fin 7 → Word w) (l : List (Fin 7)) (i : Fin l.length) (j : Fin w) :
    pack v l (offset l i j) = (addressEquiv w).symm (v (l.get i)) j := by
  induction l with
  | nil => exact Fin.elim0 i
  | cons a l ih =>
    induction i using Fin.cases with
    | zero => exact Fin.append_right _ _ j
    | succ i =>
      exact (Fin.append_left (pack v l) ((addressEquiv w).symm (v a)) (offset l i j)).trans (ih i)

theorem field_at (hw : 2≤w) (s : Option (WordRecord w)) (i : Fin 7) (j : Fin w) :
    bits hw s (offset TraceSlots.keyIndices i j) = TraceWords.bits (TraceSlots.fields hw s i) j := by
  have key : TraceSlots.keyIndices.get i = i := by fin_cases i <;> rfl
  calc
    _ = (addressEquiv w).symm (TraceSlots.fields hw s (TraceSlots.keyIndices.get i)) j :=
      read_offset (TraceSlots.fields hw s) TraceSlots.keyIndices i j
    _ = (addressEquiv w).symm (TraceSlots.fields hw s i) j :=
      congrArg (fun k => (addressEquiv w).symm (TraceSlots.fields hw s k) j) key
    _ = _ := by
      obtain ⟨v,eqn⟩ := (addressEquiv w).surjective (TraceSlots.fields hw s i)
      rw [←eqn,Equiv.symm_apply_apply]
      exact (ExactQuantumFactoring.bitsValue_bit v j).symm

abbrev ScanPins (m w : ℕ) := Fin (2^m+1) × Fin (RecordWidth w)

def scanWires (m w : ℕ) (i : Fin (2^m)) : PairWords (Fin w → ScanPins m w) :=
  slices (fun f j => (i.castSucc,offset TraceSlots.keyIndices f j))
    (fun f j => (i.succ,offset TraceSlots.keyIndices f j))

/-- An extra initial row supplies the fixed padding sentinel. -/
def scanInput (hw : 2≤w) (rows : Fin (2^m) → Option (WordRecord w)) : ScanPins m w → Bool :=
  Function.uncurry (bits hw ∘ withPrevious none rows)

def scan (F : Type*) [Zero F] [One F] (m w : ℕ) : BitNetwork F (Fintype.card (ScanPins m w)) :=
  let packet : TraceCompose.Packet (ScanPins m w) := ⟨_,(arrayFrame (scanWires m w)).circuit ()⟩
  TraceCircuit.localNetwork (fun _ : Fin 1 => packet) (Fintype.equivFin _)
    (fun _ b => if b then 1 else 0)

theorem scan_eval {F : Type*} [CommRing F] (hw : 2≤w) (rows : Fin (2^m) → Option (WordRecord w)) :
    TypedWiring.value (scan F m w) (scanInput hw rows) =
      if PaddedCheck none (List.ofFn fun i => (rows i).map WordRecord.record) then 1 else 0 := by
  have slicesAt i : Represents (addressed (scanWires m w i)) (scanInput hw rows)
      (pairWords (withPrevious none rows i.castSucc) (rows i)) := by
    apply represents_slices hw (scanInput hw rows) _ _
      (fun f j => .input (i.castSucc,offset TraceSlots.keyIndices f j))
      (fun f j => .input (i.succ,offset TraceSlots.keyIndices f j))
    · intro f j
      exact field_at hw _ _ _
    · intro f j
      change bits hw (withPrevious none rows i.succ) _ = _
      simp only [withPrevious,Fin.cons_succ]
      exact field_at hw (rows i) f j
  have ok := arrayCircuit_eval hw (scanWires m w) (scanInput hw rows) none rows slicesAt
  simp only [TypedWiring.value,scan,TraceCircuit.localNetwork_eval,Fin.prod_univ_one,
    Function.comp_def,Equiv.symm_apply_apply]
  by_cases good : PaddedCheck none (List.ofFn fun i => (rows i).map WordRecord.record)
  · rw [ite_eq_left (ok.mpr good),ite_eq_left good]
  · rw [ite_eq_right (fun h => good (ok.mp h)),ite_eq_right good]

theorem scan_cells {F : Type*} [Zero F] [One F] :
    (scan F m w).cells ≤ 4*((2^m)*(50*w+11)+2*2^m+1)+1 := by
  simpa only [scan,TraceCircuit.localNetwork_cells,Fin.sum_univ_one] using
    Nat.add_le_add_right (arrayCircuitSize_le (scanWires m w)) 1

end Hierarchy.TaggedShorterHistoryOrder

end
end OAI
