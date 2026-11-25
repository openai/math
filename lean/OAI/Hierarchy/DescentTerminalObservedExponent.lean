import OAI.Hierarchy.DescentPrivateExponentRAM
import OAI.Hierarchy.DescentPrivateSpectrum
import OAI.Hierarchy.DescentTerminalPrivateCount

namespace OAI
/-! # One native terminal exponent for all true hidden operands -/

namespace Hierarchy.DescentTerminalObservedExponent
open DescentKernelHistory DescentBundleHistory Computability.BorderVNP.Crossing DescentTerminalPrivateCount
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {U P : Type} {p D : ℕ} {bits : P→ℕ}
variable (hp : 0<p) (N : Network D P bits) (r : SiteBits (U:=U) N) (s : ∀v,Shape p (r v))
local notation "rows" => (fun v => Shape.recipe hp (s v))

def volume := ∑v,∑h,(r v).hiddenWidth h
def liveCount := ∑v,Fintype.card (rows v).UsedWord
def deadCount := ∑v,(rows v).deadBits

/-- Every p-bit label of the original local contractions occurs either in a fetched operand
or in the exponent. The equality is in natural bits before the RAM word cast. -/
theorem partition : liveCount hp N r s*p+deadCount hp N r s=volume N r := by
  unfold liveCount deadCount volume
  rw [Finset.sum_mul,←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro v _
  rw [dead_exponent hp N r s v,←Nat.add_mul]
  have contained : Fintype.card (rows v).UsedWord≤Fintype.card (Private (r v) p) :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  rw [Nat.add_sub_of_le contained]
  have count : Fintype.card (Private (r v) p)=privateGrains p (r v) := by
    simp [Private,privateGrains,Fintype.card_sigma]
  rw [count,(s v).privateGrains_mul]

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
variable {n w K : ℕ} (slot : Slots (fun v => (s v).recipe hp) ↪ Fin n) (distinct : DescentDistinctRAM.Banks)
    (out : DescentPrivateExponentRAM.Banks) (m : Memory w)
local notation "labels" => tags rows slot

def image := out.result p (liveCount hp N r s) (distinct.result labels m K)

theorem run (cs : distinct.Room w K n) (source : distinct.Read labels m) (locality : DescentDistinctWindow.Local labels K)
    (endCell : out.usedWords=distinct.starts+n) (space : out.Room w) :
    ((distinct.program w K n).seq (out.program w p)).Exec m (image hp N r s slot distinct out m (K:=K))
      (((4+n*(2*(distinct.fresh K).work+4))+(10+(3+12*n)))+out.steps p) := by
  have read := observed_word rows slot distinct m locality
  have seen : distinct.result labels m K out.usedWords =
      (liveCount hp N r s : Computability.VPVNP.BurstRAM.Word w) := by
    simpa only [endCell,liveCount] using read
  have finish : (out.program w p).Exec (distinct.result labels m K)
      (image hp N r s slot distinct out m (K:=K)) (out.steps p) :=
    out.run p (liveCount hp N r s) (distinct.result labels m K) space seen
  have start : (distinct.program w K n).Exec m (distinct.result labels m K)
      ((4+n*(2*(distinct.fresh K).work+4))+(10+(3+12*n))) := distinct.run labels m cs source
  exact @Procedure.Exec.then w (distinct.program w K n) (out.program w p) m
    (distinct.result labels m K) (image hp N r s slot distinct out m (K:=K)) _ _
    (@start) (@finish)

theorem read (cs : distinct.Room w K n) (space : out.Room w)
    (before : out.totalBits<distinct.flags) (held : m out.totalBits=(volume N r:Computability.VPVNP.BurstRAM.Word w)) :
    image hp N r s slot distinct out m (K:=K) out.deadBits=(deadCount hp N r s:Computability.VPVNP.BurstRAM.Word w) := by
  have belowStarts : out.totalBits<distinct.starts :=
    before.trans_le ((Nat.le_add_right distinct.flags n).trans cs.sep)
  have keep : distinct.result labels m K out.totalBits=m out.totalBits := by
    exact (ProtocolRAMEndpointPrefix.frame distinct.starts (DescentDistinctRAM.countPrefix labels K)
      (ProtocolRAM.image distinct.flags n (distinct.fresh K) m) n out.totalBits (Or.inl belowStarts)).trans
      (ProtocolRAMGeneratedWrite.frame_image distinct.flags n (distinct.fresh K) m out.totalBits (Or.inl before))
  have total := partition hp N r s
  have fits : liveCount hp N r s*p≤volume N r :=
    (Nat.le_add_right _ (deadCount hp N r s)).trans total.le
  have remaining : volume N r-liveCount hp N r s*p=deadCount hp N r s := by
    rw [←total,Nat.add_sub_cancel_left]
  exact (out.read p (liveCount hp N r s) (volume N r) (distinct.result labels m K) space
    (keep.trans held) fits).trans (congrArg (fun k : ℕ => (k : Computability.VPVNP.BurstRAM.Word w)) remaining)

end
end Hierarchy.DescentTerminalObservedExponent

end OAI
