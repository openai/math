import OAI.Computability.NearSquareRoot.FixedCandidateCRTDispatchCases

/-! # Tape boundaries of the batches within one physical CRT half-stage -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTStream.Half
open IntegerMultiplication Code DigitPacking FixedPoint

noncomputable section

abbrev which {u : ℕ} (s : Switch u) :=
  CRTDispatch.which (box u).length s.1.val (CRTDispatch.Cap (addressBits u))

abbrev widths {u : ℕ} (s : Switch u) (r : CRTTable.TargetIndex (box u).length s.1.val) :=
  CRTTable.axisWidth (box u) (CRTTable.targetAxis _ _ r)

def tables {u : ℕ} (h : Directory u) (inv : Bool) (s : Switch u) :=
  letI := BoxFin.modulus_neZero h
  CRTTable.packedTables _ _ (fits h) s.1.val inv

def batch {u : ℕ} (h : Directory u) (inv : Bool) (s : Switch u) (β : ℕ) : Equiv.Perm (Packed u s) :=
  Benes.batchStage (which s) (widths s) (tables h inv s) s.2 β

def key {u : ℕ} (inv : Bool) (s : Switch u) (β : ℕ) : Tree :=
  send (CRTDispatch.issue CRTDispatch.low (seed inv s,tally β))

variable {I : Type} (n : I → ℕ) (hs : ∀ i, Directory (n i)) (inv : Bool)

abbrev KernelIndex :=
  (x : Input n inv) × Fin (CRTBudget.batches (addressBits (n x.1))) × Equiv.Perm (Packed (n x.1) x.2.1.val)

def before (z : KernelIndex n inv) : Tree :=
  .fork (key inv z.1.2.1.val z.2.1.val)
    (packedRows (hs z.1.1) z.1.2.1.val (Benes.scatter z.2.2 (pack (hs z.1.1) z.1.2.1.val z.1.2.2)))

def after (z : KernelIndex n inv) : Tree :=
  packedRows (hs z.1.1) z.1.2.1.val
    (Benes.scatter (batch (hs z.1.1) inv z.1.2.1.val z.2.1.val)
      (Benes.scatter z.2.2 (pack (hs z.1.1) z.1.2.1.val z.1.2.2)))

def original (x : Input n inv) : Tree :=
  packedRows (hs x.1) x.2.1.val (pack (hs x.1) x.2.1.val x.2.2)

def beforeStage (x : Input n inv) : Tree := .fork (send (seed inv x.2.1.val)) (original n hs inv x)

def afterStage (x : Input n inv) : Tree :=
  packedRows (hs x.1) x.2.1.val (Benes.scatter (packedSlot (hs x.1) inv x.2.1.val)
    (pack (hs x.1) x.2.1.val x.2.2))

def forest (x : Input n inv) : Tree :=
  Task.forest (key inv x.2.1.val) (List.range (CRTBudget.batches (addressBits (n x.1))))

end
end FixedCandidate.CRTStream.Half

end NearSquareRoot
end Computability
end OAI
