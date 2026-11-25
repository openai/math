import OAI.Hierarchy.DescentExteriorRejectWord
import OAI.Hierarchy.DescentExteriorMachine

namespace OAI
/-! # Executing every exterior proposal, including malformed histories and matrices -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentExteriorFetch DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {w e j r t : ℕ} (origin : ℕ)
local notation "R" => 2^(j+r)
local notation "n" => e*R
local notation "I" => Fin n
local notation "k" => j+(j+r)
local notation "H" => span j r t e
local notation "keyPos" => keyAt j r t e origin
local notation "first" => start j r t e origin
local notation "kb" => keyBanks j r t e origin
local notation "gg" => gatherBanks j r t e origin
local notation "gb" => guesses j r t e origin

theorem run_unconditional (space : origin+22*H<2^w) (m : Memory w) :
    (service w j r t e origin).Exec m (serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin m) (16+364*n) ∧
    CheapCode (service w j r t e origin) := by
  have hp : 0<H:=Nat.two_pow_pos _
  have endRoom : origin+19*H<2^w := by omega
  obtain ⟨kfit,cap⟩:=layout_ready (j:=j) (r:=r) (t:=t) (e:=e) origin endRoom
  have keyFits : (joinKey kb).Fits w keyPos := by
    simp only [joinKey,Expr.Fits,kfit (kb).owner (by simp [KeyBanks.all]),
      kfit (kb).matrix (by simp [KeyBanks.all]),kfit (kb).offsets (by simp [KeyBanks.all]),
      kfit (kb).row (by simp [KeyBanks.all]),and_self]
  have guessFit (s : Fin 2) : (gb s).Fits w first :=
    fit_to j r t e origin (i:=15+s.val) (z:=18) (by have:=s.isLt;omega) endRoom
  have fits (s : Fin 3) : (gather (gg s)).Fits w first := by
    have all:=(cap s).fits
    simp only [gather,Expr.Fits,all (gg s).key (by simp [Banks.all]),
      all (gg s).slab (by simp [Banks.all]),all (gg s).source (by simp [Banks.all]),
      all (gg s).data (by simp [Banks.all]),all (gg s).offsets (by simp [Banks.all]),
      all (gg s).table (by simp [Banks.all]),and_self]
  have ready (s : Fin 3) : (columns gg gb s).Fits w first := by
    fin_cases s
    · exact ⟨fits 0,⟨guessFit 0,trivial⟩,trivial,trivial⟩
    · exact ⟨fits 1,⟨guessFit 1,trivial⟩,trivial,trivial⟩
    · exact fits 2
  have rr : n≤H := row_room j r t e
  have firstRoom : keyPos+n≤first := by change origin+17*H+n≤origin+18*H;omega
  have lastRoom : first+3*n<2^w := by change origin+18*H+3*n<2^w;omega
  exact ⟨@DescentExteriorFetch.run w keyPos first n kb gg gb keyFits firstRoom ready lastRoom m,
    DescentExteriorFetch.cheap w keyPos first n kb gg gb⟩

end
end Hierarchy.DescentExteriorShelf

namespace Hierarchy.DescentExteriorRejectWord
open DescentExteriorShelf DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def destination {w : ℕ} (n : ℕ) (flag : Bank) (out : ℕ) (m : Memory w) :=
  fillSegment out (2*n+1) (SumScores.word out 1 (fun i : Fin (2*n)=>mismatch flag m i)) m

theorem run_unconditional {w n : ℕ} (flag : Bank) (out : ℕ) (safe : flag.Fits w out) (span : 2*n≤flag.size)
    (room : out+(2*n+1)<2^w) (m : Memory w) :
    (SumScores.procedure w out (2*n) 1 (indicator flag)).Exec m (destination n flag out m) (4+(2*n+1)*64) ∧
    CheapCode (SumScores.procedure w out (2*n) 1 (indicator flag)) := by
  let s : Fin (2*n)→ℕ:=mismatch flag m
  have bill : (∑i,s i)≤2*n := by
    calc
      _≤∑_i:Fin (2*n),1:=Finset.sum_le_sum fun i _=>by unfold s mismatch;split <;>decide
      _=2*n:=by simp
  have fit : (indicator flag).Fits w out := ⟨⟨safe,trivial⟩,trivial,trivial,trivial⟩
  have one : (1:ℕ)<2^w := by have:=safe.1;have:=safe.2.1;omega
  have scan : (SumScores.procedure w out (2*n) 1 (indicator flag)).Spec
      (fun a=>SumScores.Reads a (indicator flag) s)
      (fun a o=>o=fillSegment out (2*n+1) (SumScores.word out 1 s) a) (4+(2*n+1)*64) :=
    @SumScores.run w (2*n) out 1 (indicator flag) s fit room one (by omega)
  have reads : SumScores.Reads m (indicator flag) s := by
    intro i
    have bits := i.isLt.trans_le span
    have addr : flag.read m (i.val:Word w)=m (flag.base+i.val) := by
      simp [Bank.read,Fin.val_cast_of_lt (bits.trans safe.2.1),Nat.mod_eq_of_lt bits]
    by_cases hz : m (flag.base+i.val)=0 <;>
      simp [indicator, Expr.eval, DescriptorExpr.Comparison.test, beq_iff_eq, addr, s, mismatch, hz]
  exact ⟨@Procedure.Spec.exec w (SumScores.procedure w out (2*n) 1 (indicator flag)) (4+(2*n+1)*64)
      (fun a=>SumScores.Reads a (indicator flag) s)
      (fun a=>fillSegment out (2*n+1) (SumScores.word out 1 s) a) (@scan) m reads,
    @PruneFlag.cheap w out (2*n) 1 (indicator flag)⟩

theorem read_flag {w n : ℕ} (flag : Bank) (out : ℕ) (m : Memory w) :
    destination n flag out m (out+2*n)=if ∀s:Fin 2,∀i:Fin n,m (flag.base+s.val*n+i.val)=0 then 0 else 1 := by
  rw [destination,SumScores.read_flag]
  by_cases zero : (∑i:Fin (2*n),mismatch flag m i)=0
  · rw [ite_eq_right (show ¬1≤∑i:Fin (2*n),mismatch flag m i by omega),
      ite_eq_left ((failed (n:=n) flag m).mp zero)]
  · rw [ite_eq_left (show 1≤∑i:Fin (2*n),mismatch flag m i by omega),
      ite_eq_right (fun all=>zero ((failed (n:=n) flag m).mpr all))]

theorem before {w n : ℕ} (flag : Bank) (out : ℕ) (m : Memory w) {i : ℕ} (h : i<out) :
    destination n flag out m i=m i := by simp [destination,fillSegment,not_le.mpr h]

end
end Hierarchy.DescentExteriorRejectWord

end OAI
