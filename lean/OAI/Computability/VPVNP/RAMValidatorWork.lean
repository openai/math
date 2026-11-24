import OAI.Computability.VPVNP.RAMValidatorBucket
import OAI.Computability.VPVNP.RAMValidatorPost
import OAI.Computability.VPVNP.RAMBitLocality
import OAI.Computability.VPVNP.RAMClock

/-!
# The executable single-site RAM transcript validator

Each processor receives its own header word, a contiguous vector of incident
link bits, and a private binary branch path. It checks the two successor
fields, simulates the site's burst calls, and runs the local bitonic sorting
and memory boundary checks. The returned report sequence identifies the
successful path exactly, including coincident branches.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace BurstRAM.PrivateRAM

open BurstRAM RAMLayout RAMSort

variable {w p r k d e : ℕ}

/-- Apply the memory checks only to a successful bucket, preserving the work
already incurred when a malformed bit or unsuccessful call caused rejection. -/
private def afterBucket (hw : 2 ≤ w) (v : Fin (2^d)) (header : Word w) (raw : ℕ → Bool)
    (edges : SiteSuccessors w) (bucket : Option (List (Report w))) :
    Option (List (Report w)) × ℕ :=
  match bucket with
  | none => (none, 2)
  | some rs =>
    let check := checkSiteMemory (e := e) hw v header raw edges rs
    (if check.1 then some rs else none, check.2 + 4)

private theorem afterBucket_iff (hw : 2 ≤ w) (v : Fin (2^d)) (header : Word w) (raw : ℕ → Bool)
    (edges : SiteSuccessors w) (bucket : Option (List (Report w))) (rs : List (Report w)) :
    (afterBucket (e := e) hw v header raw edges bucket).1 = some rs ↔
      bucket = some rs ∧ (checkSiteMemory (e := e) hw v header raw edges rs).1 = true := by
  cases bucket with
  | none => simp [afterBucket]
  | some t =>
    by_cases he : t = rs
    · subst t
      simp [afterBucket]
    · simp [afterBucket, he]

/-- The interpreter's only inputs depending on the instance at other sites are
the bits delivered at this site's physical ports. -/
def Machine.validateIncident (M : Machine w p r k) (fuel : ℕ) (initial header : Word w)
    (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (v : Fin (2^d))
    (inc : Fin (width d (2^e) w) → Bool) (choices : List Bool) : Option (List (Report w)) × ℕ :=
  let raw := readIncident inc
  let edges := scanSuccessors hw hc initial v raw
  if edges.1.valid then
    let bucket := M.runBucket fuel (2^d) (2^e) v.val edges.1.input edges.1.output choices
    let post := afterBucket (e := e) hw v header raw edges.1 bucket.1
    (post.1, edges.2 + bucket.2 + post.2 + 8)
  else (none, edges.2 + 4)

private theorem physical_iff (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (a : SendArrays d (2^e) w)
    (v : Fin (2^d)) :
    (SuccessorSendOK hw hc a v ∧ SuccessorReceiveOK hw hc a v) ∧ SortCanonical hw hc a v ↔
      OutgoingOK hw hc a v ∧ IncomingOK hw hc a v := by
  constructor
  · rintro ⟨⟨hs, hr⟩, hsort⟩
    exact ⟨⟨hs, fun l => (hsort l).1⟩, hr, fun l => (hsort l).2⟩
  · rintro ⟨⟨hs, hso⟩, hr, hro⟩
    exact ⟨⟨hs, hr⟩, fun l => ⟨hso l, hro l⟩⟩

/-- On an arbitrary shared assignment, one local binary string accepts with
the given reports precisely when the physical bit validator accepts them and
the string contains exactly the choices and read guesses of those reports. -/
theorem Machine.validateIncident_iff (M : Machine w p r k) (fuel : ℕ) (initial : Word w)
    (header : ℕ → Word w) (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (bits : RawAssignment d e w)
    (v : Fin (2^d)) (choices : List Bool) (rs : List (Report w)) :
    (M.validateIncident fuel initial (header v) hw hc v (BurstRAM.incidentBits bits v) choices).1 = some rs ↔
      BitValidator M.program fuel initial header hw hc bits v rs ∧
        choices = rs.flatMap (fun r => guessBits r.events) := by
  let a := sendArraysEquiv d (2^e) w bits
  let raw := sortIncident a v
  let edges := scanSuccessors hw hc initial v raw
  have he := scanSuccessors_spec hw hc initial v raw a (sortIncident_offset a v)
  let m := unpackMessages (parseMessages hw hc a)
  change edges.1.Spec hw hc initial v a at he
  change (if edges.1.valid then _ else (none, edges.2 + 4)).1 = some rs ↔ _
  by_cases hv : edges.1.valid = true
  · rw [ite_eq_left hv]
    dsimp only
    rw [afterBucket_iff, Machine.runBucket_iff M (Nat.two_pow_pos e)]
    change ((SiteCheck M.program fuel (2^d) (2^e) v.val edges.1.input edges.1.output rs ∧
      choices = rs.flatMap (fun r => guessBits r.events)) ∧
      (checkSiteMemory (e := e) hw v (header v) (sortIncident a v) edges.1 rs).1 = true) ↔ _
    rw [checkSiteMemory_iff hw hc a v header initial edges.1 he rs]
    rw [he.input_eq, he.output_eq]
    obtain ⟨hs, hr⟩ := he.valid_iff.mp hv
    constructor
    · rintro ⟨⟨hb, hbits⟩, hsort, hmem⟩
      exact ⟨⟨(physical_iff hw hc a v).mp ⟨⟨hs, hr⟩, hsort⟩, hb, hmem⟩, hbits⟩
    · rintro ⟨⟨hcan, hb, hmem⟩, hbits⟩
      exact ⟨⟨hb, hbits⟩, ((physical_iff hw hc a v).mpr hcan).2, hmem⟩
  · rw [ite_eq_right hv]
    constructor
    · intro h; cases h
    · rintro ⟨⟨hcan, _⟩, _⟩
      exact (hv (he.valid_iff.mpr ((physical_iff hw hc a v).mpr hcan).1)).elim

private theorem overhead_le (k w H fuel : ℕ) :
    102 + (2*H)*(12*fuel+9) + 64*(4*H) + 48 + 256*(H+1)*(fuel+1)*(fuel+1)*(w+2) +
      (2*H)*(16*fuel+16) ≤ 2048*(H+1)*(fuel+1)*(fuel+1)*(w+k+2) := by
  ring_nf
  omega

/-- All received vectors and private bit streams meet the same bound,
including invalid control fields and rejected partial reads. -/
theorem Machine.validateIncident_work (M : Machine w p r k) (fuel : ℕ) (initial header : Word w)
    (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (v : Fin (2^d)) (inc : Fin (width d (2^e) w) → Bool)
    (choices : List Bool) (hf : 2^e ≤ 2*fuel) :
    (M.validateIncident fuel initial header hw hc v inc choices).2 ≤
      transcriptWorkBound k w (2^e) ((2+e)+d) fuel := by
  let raw := readIncident inc
  let edges := scanSuccessors hw hc initial v raw
  let bucket := M.runBucket fuel (2^d) (2^e) v.val edges.1.input edges.1.output choices
  have he := scanSuccessors_cost hw hc initial v raw
  change edges.2 ≤ _ at he
  have hb := M.runBucket_work fuel (2^d) (2^e) v.val edges.1.input edges.1.output choices
    (Nat.two_pow_pos e) hf
  change bucket.2 ≤ _ at hb
  have ho := overhead_le k w (2^e) fuel
  unfold transcriptWorkBound
  by_cases hv : edges.1.valid = true
  · unfold Machine.validateIncident
    rw [ite_eq_left hv]
    change edges.2 + bucket.2 + (afterBucket (e := e) hw v header raw edges.1 bucket.1).2 + 8 ≤ _
    cases hx : bucket.1 with
    | none =>
      change edges.2 + bucket.2 + 2 + 8 ≤ _
      omega
    | some rs =>
      have hs := ((M.runBucket_iff (Nat.two_pow_pos e)).mp hx).1.1
      have hm := checkSiteMemory_work hw v header raw edges.1 rs hs
      change edges.2 + bucket.2 + ((checkSiteMemory (e := e) hw v header raw edges.1 rs).2 + 4) + 8 ≤ _
      omega
  · unfold Machine.validateIncident
    rw [ite_eq_right hv]
    change edges.2 + 4 ≤ _
    omega

/-- The paper's word-step cap for every path of the executable validator. -/
theorem Machine.validateIncident_clock (M : Machine w p r k) (n u : ℕ) (initial header : Word w)
    (hw : 2 ≤ w) (hc : 2^d * 2^e < 2^w) (v : Fin (2^d)) (inc : Fin (width d (2^e) w) → Bool)
    (choices : List Bool) (hn : 2048 ≤ n) (hu : 1 ≤ u) (hk : k+2 ≤ n) (hw' : w ≤ n)
    (hH : 2^e ≤ 2*n) (hstages : ((2+e)+d)+1 ≤ n) :
    (M.validateIncident (n^u) initial header hw hc v inc choices).2 ≤ n^(10*u+30) := by
  have hf : 2^e ≤ 2*n^u := hH.trans (Nat.mul_le_mul_left 2 (Nat.le_self_pow (by omega) n))
  exact (M.validateIncident_work (n^u) initial header hw hc v inc choices hf).trans
    (transcriptWorkBound_le_clock hn hk hw' hH hstages)

end BurstRAM.PrivateRAM

end VPVNP
end Computability
end OAI
