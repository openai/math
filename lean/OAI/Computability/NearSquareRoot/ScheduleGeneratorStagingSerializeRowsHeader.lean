import OAI.Computability.NearSquareRoot.ScheduleStagingSerialize
import Mathlib.Computability.Primrec.List
import Mathlib.Data.List.GetD

/-! # Computing the literal letters of a staged serialization header -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.SerializeRows

open IntegerMultiplication.Code

def codeLetter : Ltr → ℕ
  | .node => 0
  | .bit false => 1
  | .bit true => 2
  | .sep => 3

private def tallyBytes (k : ℕ) : List ℕ := k.rec [1] fun _ prev => 0::1::prev

private theorem tallyBytes_primrec : Primrec tallyBytes :=
  Primrec.nat_rec' Primrec.id (Primrec.const [1])
    (Primrec.list_cons.comp (Primrec.const 0) (Primrec.list_cons.comp (Primrec.const 1)
      (Primrec.snd.comp Primrec.snd))).to₂

private theorem tallyBytes_eq (k : ℕ) : tallyBytes k = (send (tally k)).spell.map codeLetter := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [tally_succ]
    change 0::1::tallyBytes k = 0::1::((send (tally k)).spell.map codeLetter)
    rw [ih]

/-- The default outside the header is the node code. -/
def headerLetter (k j : ℕ) : ℕ := (0::tallyBytes k ++ [0]).getD j 0

theorem computable_headerLetter : Computable₂ headerLetter :=
  ((Primrec.list_getD 0).comp (Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_append.comp (tallyBytes_primrec.comp Primrec.fst) (Primrec.const [0]))) Primrec.snd).to_comp.to₂

theorem headerLetter_get (k : ℕ) (j : Fin (StagingSerialize.header k).length) :
    headerLetter k j.val = codeLetter (StagingSerialize.header k)[j] := by
  have eq : 0::tallyBytes k ++ [0] = (StagingSerialize.header k).map codeLetter := by
    simp [StagingSerialize.header,tallyBytes_eq,codeLetter]
  have hj : j.val < ((StagingSerialize.header k).map codeLetter).length := by simpa using j.isLt
  rw [headerLetter,eq,List.getD_eq_getElem _ 0 hj,List.getElem_map]
  simp only [Fin.getElem_fin]

end Generator.SerializeRows

end NearSquareRoot
end Computability
end OAI
