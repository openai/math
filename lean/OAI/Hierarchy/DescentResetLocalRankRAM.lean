import OAI.Hierarchy.DescentResetWindowRankInput
import OAI.Hierarchy.DescentResetWindowRanksRAM

namespace OAI
/-! # Native all-receiver rank program and arbitrary-input execution -/
namespace Hierarchy.DescentResetLocalRankRun
open DescentResetSignedScan DescentSIMDLookup DescentPackedColony DescentPackedZip
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical
noncomputable section
variable {X K w : ℕ}

def rankBase (base b M : ℕ):=RankInput.endAddress base b M
def endAddress (base X K b M H G : ℕ):=Ranks.endAddress (rankBase base b M) X K b M H G
def query (base b M : ℕ) (header ticket : Fin X→Fin K→Expr) : Ranks.Request X K :=
  fun x _ j=>RankInput.expr base b M (header x j) (ticket x j)
def items (base b M : ℕ) (header ticket : Fin X→Fin K→Expr) : Ranks.Inputs X K :=
  fun x _ _ j=>RankInput.expr base b M (header x j) (ticket x j)
def program (base X K b M H G w : ℕ) (header ticket : Fin X→Fin K→Expr) :=
  (RankInput.program base b M w).seq (Ranks.program (rankBase base b M) b b M H G w
    (query base b M header ticket) (items base b M header ticket))
def memory (base X K b M H G : ℕ) (header ticket : Fin X→Fin K→Expr) (m : Memory w) :=
  Ranks.memory (rankBase base b M) b b M H G (query base b M header ticket) (items base b M header ticket) (RankInput.memory base b M m)
def time (base X K b M H G : ℕ) (header ticket : Fin X→Fin K→Expr) :=
  (4+10*(2*2^(RankInput.width b M)))+Ranks.time (rankBase base b M) b b M H G (query base b M header ticket) (items base b M header ticket)
def bank (base X K b M H G : ℕ) (x : Fin X) (p : Fin 3) (j : Fin K) :=
  Ranks.output (rankBase base b M) X K b M H G x p j
theorem lower (base X K b M H G : ℕ) : rankBase base b M≤endAddress base X K b M H G :=
  (Nat.le_add_right ..).trans (Nat.le_add_right ..)

theorem any (base X K b M H G : ℕ) (header ticket : Fin X→Fin K→Expr) (m : Memory w)
    (raw : ∀x j,(header x j).Fits w base) (old : ∀x j,(ticket x j).Fits w base)
    (space : endAddress base X K b M H G<2^w) :
    let done:=memory base X K b M H G header ticket m
    (program base X K b M H G w header ticket).Exec m done (time base X K b M H G header ticket) ∧
    (∀a,a<base ∨ endAddress base X K b M H G≤a→done a=m a) ∧ CheapCode (program base X K b M H G w header ticket) := by
  intro done
  have upto:=lower base X K b M H G
  have fit:=upto.trans_lt space
  have after_:=RankInput.any base b M m fit
  have guard (x j):=RankInput.expr_fits base (header x j) (ticket x j) (raw x j) (old x j) fit
  obtain ⟨live,back,ok⟩:=Ranks.any (rankBase base b M) (q:=query base b M header ticket)
    (a:=items base b M header ticket) (mem:=RankInput.memory base b M m) (fun x _ j=>guard x j)
    (fun x _ _ j=>guard x j) (paid:=b) space
  let readProgram := RankInput.program base b M w
  let rankProgram := Ranks.program (rankBase base b M) b b M H G w
    (query base b M header ticket) (items base b M header ticket)
  let rankTicks := Ranks.time (rankBase base b M) b b M H G
    (query base b M header ticket) (items base b M header ticket)
  refine ⟨@Procedure.Exec.then w readProgram rankProgram m (RankInput.memory base b M m) done
    (4+10*(2*2^(RankInput.width b M))) rankTicks after_.1 live,?_,?_⟩
  · intro a away
    rcases away with left|right
    · exact (back a (.inl (left.trans_le (Nat.le_add_right ..)))).trans (after_.2.1 a (.inl left))
    · exact (back a (.inr right)).trans (after_.2.1 a (.inr (upto.trans right)))
  · apply ProtocolRAM.cheap_seq
    · exact @after_.2.2.2
    · exact @ok

end
end Hierarchy.DescentResetLocalRankRun

end OAI
