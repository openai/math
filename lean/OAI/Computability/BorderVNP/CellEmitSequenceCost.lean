import OAI.Computability.BorderVNP.CellEmitListCost
import OAI.Computability.BorderVNP.CellEmitLists

/-! # Indexed command sequences on the actual native compiler -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Packet.Emit

open ExactQuantumFactoring.BitStackProgram ExactQuantumFactoring.BitStackProgram.Procedure

/-- A sequence printer invokes its actual row printer once per stored row. Only the
compact printed word of each row is retained, before their final concatenation. -/
theorem meter_sequenceMapIdx {A B : Type} (ea : A → List Bool) (eb : B → List Bool) (d : B) :
    ∃ K : ℕ, ∀ {rows : A → List B} {f : A → ℕ → B → Stmt}
      (hl : Procedure ea (listCode eb) rows)
      (hf : Statement (prodCode ea (prodCode Nat.bits eb)) (fun z => f z.1 z.2.1 z.2.2))
      (x : A) {L C : ℕ},
      (∀ i : Fin (rows x).length, (CellMacro.Generator.serialized 8 (f x i (rows x)[i])).length ≤ L) →
      (∀ i : Fin (rows x).length, hf.cost (x,i.val,(rows x)[i]) ≤ C) →
      (sequenceMapIdx d hl hf).meter x ≤ K*(hl.meter x+((rows x).length+1)*
        (C+((prodCode ea (listCode eb) (x,rows x)).length+1)^9+
        (tabSpan (prodCode ea (listCode eb)) (rows x).length (x,rows x) L)^2+1)) := by
  obtain ⟨K,hK⟩ := meter_flatMapIdxList ea eb d
  refine ⟨K,?_⟩
  intro rows f hl hf x L C hL hC
  unfold sequenceMapIdx
  rw [meter_congrFun]
  exact hK (f:=fun x i b => CellMacro.Generator.serialized 8 (f x i b)) hl hf x hL hC

end CellSparse.Packet.Emit

end BorderVNP
end Computability
end OAI
