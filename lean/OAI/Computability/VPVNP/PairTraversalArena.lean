import OAI.Computability.VPVNP.PairTraversalDirectoryRun
import OAI.Computability.VPVNP.PairTraversalLevelDirectories
import OAI.Computability.VPVNP.PairTraversalRoleDispatch

/-!
# Native traversal arena for a selected compressor branch

The actual level-indexed placement scans feed a fixed leaf worker followed by
a fixed fiber worker. A fixed tag writer marks the same selected layers from
their retained pass origins. The programs share one external memory, and
their writes preserve the final-arc bit words between rows and tags.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalRoles

open BurstRAM CompressorRecords TraversalRows DirectoryRun LocalHistory Compression
open scoped Fin.CommRing

variable {w : ℕ} {k A : Type*} [Field k] [CommRing A] {S : BlockSchedule k}
variable (B : S.Templates) (f : B.Entry → A) (hf : B.IsSolution f) {n : ℕ}
variable (T : ℕ) (hT : T * S.laneBits ≤ n) (X : State (S.degreeExponent 0) n)
variable (z : (B.execute f hf T hT X).Choices)

private theorem one_probe_each (rs : List (Report w)) (h : ∀ r ∈ rs, r.probes = 1) :
    countProbes (eventLog rs) = rs.length := by
  induction rs with
  | nil => rfl
  | cons r tail ih =>
    change countProbes (r.events ++ eventLog tail) = tail.length + 1
    rw [BurstRAM.countProbes_append, show countProbes r.events = 1 from h r List.mem_cons_self,
      ih (fun t ht => h t (List.mem_cons_of_mem _ ht)), Nat.add_comm]

/-- Construct the selected descriptor arena in a shared native memory. Its
DFS rows and role words are read back at their actual native addresses and
every final bit remains available. Each worker costs a bounded number of
probes and bursts per selected row, independently of all wire widths. -/
theorem native_arena (base F : ℕ) (m : Memory w)
    (ds : let vs := executeLevels B f hf T hT X z
      (i : Fin vs.length) → LevelDirectory vs[i] m base)
    (fit : base + 2 * words B.recordLimit (selectedLayers B f hf T hT X z) + F < 2 ^ w) :
    let E := B.execute f hf T hT X
    let data := B.records f hf T hT X
    let c := E.termChain data z
    let ords := branchOrders E data z
    let old := siteOrder X
    let cap := B.recordLimit
    let ls := selectedLayers B f hf T hT X z
    let offset := words cap ls + F
    let roles := selected B f hf T hT X z
    let dirs := selectedDirectories B f hf T hT X z m base ds
    let rowJobs := Worker.leaf cap base old.length ::
      workers c ords old dirs cap base (address cap base old.length)
    ∃ ts rs, RolePasses offset cap base roles m ts ∧
      Segments rowJobs (after m (eventLog ts)) rs ∧
      let final := after m (eventLog (ts ++ rs))
      final = build cap base base ls (writeTags offset cap base roles m) ∧
        Reads w final offset cap base roles ∧ AllRows w final cap base base ls ∧
        (∀ i < F, final (base + words cap ls + i) = m (base + words cap ls + i)) ∧
        ts.length + rs.length ≤ 2 * (((S.steps + 1) * T + 1) * X.positions) ∧
        countProbes (eventLog (ts ++ rs)) ≤
          (2 * cap + 4) * (((S.steps + 1) * T + 1) * X.positions) := by
  intro E data c ords old cap ls offset roles dirs rowJobs
  let visits := ((S.steps + 1) * T + 1) * X.positions
  let size := words cap ls
  have room : base + size < 2 ^ w := by change base + 2 * size + F < _ at fit; omega
  obtain ⟨ts, ht, tagMem, _, tagCalls, tagCost, _⟩ := native_selected_roles B f hf T hT X z
    base F m fit.le
  let tagged := after m (eventLog ts)
  have ag (x : ℕ) (hx : x < base) : tagged x = m x := by
    dsimp only [tagged]
    rw [tagMem]
    exact write_tags_outside offset cap base roles m x (Or.inl (hx.trans_le (Nat.le_add_left _ _)))
  obtain ⟨rs, hr, mem, calls, probes⟩ := DirectoryRun.selected_run B f hf T hT X z base m
    tagged ag room dirs
  let final := after m (eventLog (ts ++ rs))
  have hfinal : final = build cap base base ls (writeTags offset cap base roles m) := by
    change after m (eventLog (ts ++ rs)) = _
    rw [show after m (eventLog (ts ++ rs)) = after tagged (eventLog rs) from by
      simp only [eventLog, List.flatMap_append, after, List.foldl_append, tagged], mem]
    exact congrArg (build cap base base ls) tagMem
  obtain ⟨reads, bits, rows⟩ := selected_tags_and_rows B f hf T hT X z base F m room
  have visitsBound : (ls.map Layer.count).sum ≤ visits := selected_count_sum_le B f hf T hT X z
  have tc := one_probe_each ts (fun t ht => (tagCost t ht).2)
  refine ⟨ts, rs, ht, hr, hfinal, ?_, ?_, ?_, ?_, ?_⟩
  · change Reads w final offset cap base roles
    rw [hfinal]
    exact reads
  · change AllRows w final cap base base ls
    rw [hfinal]
    exact rows
  · change ∀ i < F, final _ = _
    rw [hfinal]
    exact bits
  · have h := calls.trans_le visitsBound
    change ts.length ≤ visits at tagCalls
    omega
  · change countProbes (eventLog (ts ++ rs)) ≤ (2 * cap + 4) * visits
    simp only [eventLog, List.flatMap_append, BurstRAM.countProbes_append]
    change countProbes (eventLog ts) + countProbes (eventLog rs) ≤ _
    have h := Nat.add_le_add (tc.trans_le tagCalls)
      (probes.trans (Nat.mul_le_mul_left _ visitsBound))
    exact h.trans_eq (by change visits + (2 * cap + 3) * visits = _; ring)

end PairSimulation.TraversalRoles

end VPVNP
end Computability
end OAI
