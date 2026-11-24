import OAI.Computability.VPVNP.PairShrinkNodeClock
import OAI.Computability.VPVNP.PairVertexLevelSchedule
import OAI.Computability.VPVNP.PairVertexOrdinalRoleCost
import OAI.Computability.VPVNP.PairDispatchedRowEffects

/-! # Uniform resources of a shrinking node in the ordinal traversal

The level locator is the only source of length-dependent external probes.
The old and hidden bit streams contribute private instructions linear in
the current maximum width. The dispatch costs one probe and nine instructions.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkNodeCost

open Compression CompressorRecords BurstRAM DFS Filter

variable {k : Type*} [_root_.Field k] (S : BlockSchedule k)

private def fixedProbes (i : Fin S.steps) (mapC fieldC : ℕ) :=
  26 + (1+3*2^(S.degreeExponent i.castSucc))*fieldC + 3*fieldC + mapC

/-- One common coefficient for all shrinking passes in the installed schedule. -/
def probeRate (mapC fieldC : ℕ) :=
  Finset.univ.sup (fun i : Fin S.steps => fixedProbes S i mapC fieldC + (S.steps+1))

private noncomputable def fixedTicks (i : Fin S.steps) (header fieldC : ℕ) :=
  let degree := 2^(S.degreeExponent i.castSucc)
  97 + S.steps + 2*i.val + degree + VertexLevel.hiddenCount + header +
    (10+15*degree)*fieldC + 25*fieldC

private noncomputable def tickRate (i : Fin S.steps) (header mapC fieldC : ℕ) :=
  fixedTicks S i header fieldC + 6*(S.steps+1) + 12*fieldC + mapC

/-- At a single eventual threshold every stage's instruction coefficient
fits. Header lengths can differ between stages. -/
def RateRoom (header : Fin S.steps → ℕ) (mapC fieldC n : ℕ) : Prop :=
  1 ≤ n ∧ ∀ i, 2*tickRate S i (header i) mapC fieldC ≤ n

theorem eventually_job_rate_room (header : Fin S.steps → ℕ) (mapC fieldC : ℕ) :
    ∀ᶠ n : ℕ in atTop, RateRoom S header mapC fieldC n := by
  let rates := fun i : Fin S.steps => 2*tickRate S i (header i) mapC fieldC
  filter_upwards [eventually_ge_atTop (max 1 (Finset.univ.sup rates))] with n hn
  exact ⟨(le_max_left ..).trans hn,fun i =>
    (Finset.le_sup (f := rates) (Finset.mem_univ i)).trans ((le_max_right ..).trans hn)⟩

/-- The two count identities are the output of `native_cost` for a single
successful shrinking reader. The map-loop charges include its final exit
test and every selected row, including the case of an empty loop. -/
theorem job_rates (i : Fin S.steps) (header : Fin S.steps → ℕ) (mapC fieldC n : ℕ)
    (room : RateRoom S header mapC fieldC n)
    {later width sites oldBits hiddenRows hiddenBits mapTicks mapProbes ticks probes : ℕ}
    (level : later ≤ (S.steps+1)*(n.log2+1)) (wire : width ≤ n)
    (children : sites ≤ fieldC) (demand : oldBits ≤ fieldC*(width+1))
    (hidden : hiddenRows ≤ fieldC) (payload : hiddenBits ≤ fieldC*(width+1))
    (mapTime : mapTicks ≤ mapC*(width+1)) (mapReads : mapProbes ≤ mapC)
    (time : ticks = 88+6*later+S.steps+2*i.val+2^(S.degreeExponent i.castSucc)+VertexLevel.hiddenCount+
      header i+(10+15*2^(S.degreeExponent i.castSucc))*sites+6*oldBits+
      25*hiddenRows+6*hiddenBits+mapTicks)
    (reads : probes = 25+later+(1+3*2^(S.degreeExponent i.castSucc))*sites+3*hiddenRows+mapProbes) :
    probes+1 ≤ probeRate S mapC fieldC*(n.log2+1) ∧ ticks+9 ≤ n^43 := by
  let fixed := fixedProbes S i mapC fieldC
  let t := tickRate S i (header i) mapC fieldC
  have degree := Nat.mul_le_mul_left (1+3*2^(S.degreeExponent i.castSucc)) children
  have hs := Nat.mul_le_mul_left 3 hidden
  have work := Nat.mul_le_mul_left (10+15*2^(S.degreeExponent i.castSucc)) children
  have hh := Nat.mul_le_mul_left 25 hidden
  have loc := Nat.mul_le_mul_left 6 (level.trans (Nat.mul_le_mul_left _ (Nat.succ_le_succ (Nat.log2_le_self n))))
  have enlarge (c : ℕ) := Nat.mul_le_mul_left c (Nat.succ_le_succ wire)
  have old := Nat.mul_le_mul_left 6 (demand.trans (enlarge fieldC))
  have bits := Nat.mul_le_mul_left 6 (payload.trans (enlarge fieldC))
  have maps := mapTime.trans (enlarge mapC)
  constructor
  · have sup : fixed+(S.steps+1) ≤ probeRate S mapC fieldC :=
      Finset.le_sup (f := fun j => fixedProbes S j mapC fieldC + (S.steps+1)) (Finset.mem_univ i)
    refine le_trans ?_ (Nat.mul_le_mul_right (n.log2+1) sup)
    have pad : fixed ≤ fixed*(n.log2+1) := Nat.le_mul_of_pos_right fixed (Nat.succ_pos _)
    rw [Nat.add_mul]
    dsimp only [fixed,fixedProbes] at pad ⊢
    omega
  · have scaled : ticks+9 ≤ t*(n+1) := by
      have pad := Nat.le_mul_of_pos_right (fixedTicks S i (header i) fieldC) (Nat.succ_pos n)
      dsimp only [t,tickRate,fixedTicks] at pad ⊢
      rw [time]
      linarith only [pad,loc,work,hh,old,bits,maps]
    have fit : 2*t ≤ n := room.2 i
    have hn := room.1
    calc
      ticks+9 ≤ t*(n+1) := scaled
      _ ≤ t*(2*n) := Nat.mul_le_mul_left t (by omega)
      _ = 2*t*n := by ring
      _ ≤ n^2 := by rw [pow_two]; exact Nat.mul_le_mul_right n fit
      _ ≤ n^43 := Nat.pow_le_pow_right hn (by decide : 2 ≤ 43)

/-- The real tag lookup adds exactly the one probe and at most the nine
instructions already allowed in the two bounds on the underlying role. -/
theorem dispatched_ordinal_cost {w endAddr n rate : ℕ} (m : Memory w) (offset node : Word w)
    (saved : DFS.Scratch w endAddr) (body : DFS.VisitPath w endAddr)
    (probes : countProbes body.trace+1 ≤ rate*(n.log2+1)) (ticks : body.trace.length+9 ≤ n^43) :
    VertexImage.ordinalJobCost n 1 rate (VertexImage.dispatchJob m offset node saved body) := by
  obtain ⟨p,t⟩ := VertexImage.dispatchJob_cost (m := m) (offset := offset) (node := node) (saved := saved) body
  exact ⟨by simpa only [p,pow_one] using probes,t.trans ticks⟩

variable {S} {R : Type*} [CommRing R] (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f)
variable {lanes : ℕ} (T : ℕ) (hT : T*S.laneBits ≤ lanes) (X : State (S.degreeExponent 0) lanes)
variable (z : (B.execute f hf T hT X).Choices)

/-- The pass list appearing in the actual level search gives the logarithmic
number of later headers for every popped ordinal. -/
theorem selected_later_le_log {n : ℕ} (blocks : T ≤ n.log2+1) (level : ℕ) :
    (executeLevels B f hf T hT X z).length - (level+1) ≤ (S.steps+1)*(n.log2+1) := by
  rw [VertexLevel.selected_pass_count B f hf T hT X z]
  exact (Nat.sub_le ..).trans ((Nat.mul_le_mul_right _ blocks).trans_eq (Nat.mul_comm ..))

end PairSimulation.ShrinkNodeCost

end VPVNP
end Computability
end OAI
