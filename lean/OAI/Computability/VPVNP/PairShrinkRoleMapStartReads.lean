import OAI.Computability.VPVNP.PairShrinkRoleMapStart
import OAI.Computability.VPVNP.PairSimulationFieldReadSafety

/-!
# The five external addresses at entry to a shrinking map row
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkVertexImage

open BurstRAM CompressorRecords Compression ShrinkMapImage.Registers
open MapResidentInputs MapResidentRows
open scoped Fin.CommRing
open private fetch from OAI.Computability.VPVNP.PairSimulationMapResidentInputs

variable {w : ℕ} {m : Memory w} {level owner : Word w} {data : ℕ → Prop}

/-- Only four header cells and the selected site's count word are probed. -/
theorem mapStart_reads
    (header : ∀ n ∈ ({34, 35, 36, 37} : Finset ℕ), data (level + (n : Word w)).val)
    (countCell : data (m (level + 34).val + owner).val) :
    SourceTransport.Reads data (List.replicate 4 .tick ++ headerEvents m level owner) := by
  intro a v h
  simp only [headerEvents, fetch, List.mem_append, List.mem_replicate, List.mem_cons,
    List.not_mem_nil, reduceCtorEq, Event.read.injEq, and_false, false_or, or_false] at h
  rcases h with ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩ | ⟨rfl, _⟩
  · exact header 34 (by decide)
  · exact countCell
  · exact header 35 (by decide)
  · exact header 36 (by decide)
  · exact header 37 (by decide)

variable {K : Type} [_root_.Field K] {S : BlockSchedule K} (B : S.Templates) (i : Fin S.steps)
    {g : ℕ} {Z : State (oldExponent i) (packingLaneBits (oldExponent i) g)}
    {sel : Z.ShrinkSelection B.shrink} {side : Bool} {term : Word w}
    (source : MapRowSource Z sel side m level term) (site : Site Z)

/-- The live level and count regions both precede the terminal header. The chronological
prefix consequently reads only cells that survive the enclosing worker's state splice. -/
theorem mapStart_worker_reads (H : Word w) (hfit : H.val + 31 < 2 ^ w)
    (hlevel : level.val + 38 ≤ H.val)
    (hdir : (ShrinkResidentLayout.layout Z source.first).endAddr ≤ H.val)
    (published : Published m level
      ((ShrinkResidentLayout.layout Z source.first).params (oldExponent i) true w 3)
      ((ShrinkResidentLayout.layout Z source.first).params (oldExponent i) true w 5) term 10) :
    SourceTransport.Reads (TerminalLink.workerCell H) (List.replicate 4 .tick ++
      headerEvents m level ((siteIndex Z site).val : Word w)) := by
  let L := ShrinkResidentLayout.layout Z source.first
  let owner := (siteIndex Z site).val
  have addr (n : ℕ) (hn : n ≤ 37) : (level + (n : Word w)).val = level.val + n := by
    rw [Fin.val_add, Fin.val_natCast, Nat.mod_eq_of_lt (show n < 2 ^ w by omega),
      Nat.mod_eq_of_lt (show level.val + n < 2 ^ w by omega)]
  have howner : owner < L.sites := (siteIndex Z site).isLt
  obtain ⟨_, _, hc, hr⟩ := L.ranges true
  have low : L.counts true + owner < H.val :=
    (Nat.add_lt_add_left howner _).trans_le
      (hc.le.trans ((Nat.le_add_right ..).trans (hr.trans hdir)))
  obtain ⟨_, _, _, _, counts, _, _⟩ := ShrinkResidentLayout.frame Z source.first true source.fit
  apply mapStart_reads
  · intro n hn
    have bound : n ≤ 37 := by
      simp only [Finset.mem_insert, Finset.mem_singleton] at hn
      omega
    apply TerminalLink.workerCell_of_lt hfit
    rw [addr n bound]
    omega
  · have actual : m (level + 34).val = L.params (oldExponent i) true w 3 := by
      rw [show (34 : Word w) = ((34 : ℕ) : Word w) from rfl, addr 34 (by decide)]
      exact published.countsAt
    apply TerminalLink.workerCell_of_lt hfit
    rw [actual, Fin.val_add, Fin.val_natCast, counts]
    change (L.counts true + owner % (2 ^ w)) % (2 ^ w) < H.val
    have total : L.counts true + owner < 2 ^ w := low.trans H.isLt
    rw [Nat.mod_eq_of_lt (show owner < 2 ^ w by omega), Nat.mod_eq_of_lt total]
    exact low

end PairSimulation.ShrinkVertexImage

end VPVNP
end Computability
end OAI
