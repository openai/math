import OAI.Computability.VPVNP.CompressorSourceOnline
import OAI.Computability.VPVNP.RAMFinite

/-!
# Guard progress and work of a native packet

An ordered list of successful cursor returns determines the guard
progress needed to replay that packet in the online dispatcher. The
same report list also determines its calls-plus-probes charge.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.SourceOnline

open BurstRAM
open scoped Fin.CommRing

variable {w : ℕ}

theorem Progress.ofOrdinals (stop start count : ℕ) (fits : stop < 2^w) (endAt : start+count = stop)
    (rs : List (Report w))
    (returns : rs.map Report.result = (List.range' (start+1) count).map (fun j : ℕ => some (j : Word w))) :
    Progress (stop : Word w) (start : Word w) rs := by
  induction count generalizing start rs with
  | zero =>
    have hz : rs = [] := List.map_eq_nil_iff.mp returns
    rw [hz]
    apply Progress.done
    rw [show start = stop by omega]
  | succ n ih =>
    cases rs with
    | nil => simp [List.range'_succ] at returns
    | cons r rs =>
      simp only [List.map_cons,List.range'_succ,List.cons.injEq] at returns
      have hs : start < stop := by omega
      refine Progress.next ?_ returns.1 (ih (start+1) (by omega) rs returns.2)
      change start % (2^w) < stop % (2^w)
      rwa [Nat.mod_eq_of_lt (hs.trans fits),Nat.mod_eq_of_lt fits]

theorem packet_cost (rs : List (Report w)) :
    RAMBuckets.cost Report.probes rs = rs.length+countProbes (eventLog rs) := by
  rw [RAMBuckets.cost_eq_length_add_probes]
  congr 1
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change r.probes + RAMBuckets.probeCount Report.probes rs = countProbes (r.events ++ eventLog rs)
    rw [ih]
    rw [Greedy.probes_append]; rfl

end CompressorRecords.SourceOnline

end VPVNP
end Computability
end OAI
