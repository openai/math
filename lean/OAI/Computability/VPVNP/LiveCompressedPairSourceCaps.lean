import OAI.Computability.VPVNP.LiveCompressedPairExecutionCaps
import OAI.Computability.VPVNP.LiveCompressedPairTerminalShare
import OAI.Computability.VPVNP.PairOnlineLiveBudget

/-! # Simultaneous native pair bounds at a fixed input length -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.CompressedPair

open BurstRAM Compression CursorNetwork CursorBounds CompressorRecords Schedule PairSimulation
open Filter LocalHistory PhaseVisits

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k}

set_option exponentiation.threshold 10000 in
theorem private_clock_room (G : PairStages.Group) {n : ℕ} (hn : 128 ≤ n) (clock : G.clock = n^10000) :
    n^9999+107 ≤ G.clockAt LiveProgram.Stage.pair := by
  have disp : (LiveStageLink.dispatchEvents G.addr LiveProgram.Stage.pair).length ≤ 44 := by
    simp only [LiveStageLink.dispatchEvents,List.length_cons,List.length_replicate]
    decide
  have large : 151 ≤ n^9999 := by
    have n2 : 151 ≤ n^2 := (by decide : 151 ≤ 128^2).trans (Nat.pow_le_pow_left hn 2)
    exact n2.trans (Nat.pow_le_pow_right (by omega) (by decide))
  have grow : 2*n^9999 ≤ n^10000 := by
    exact (Nat.mul_le_mul_right (n^9999) (by omega : 2 ≤ n)).trans_eq (pow_succ' n 9999).symm
  change n^9999+107 ≤ G.clock-_
  rw [clock]
  omega

/-- Bounds on the selected online rows and the canonical terminal charge at
one length. The same length threshold works for every field model, term
choice and native memory, after fixing the program and its address exponent. -/
theorem eventually_native_source_caps (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) (bs : Bootstrap) (P : Plan S)
    (workerCap initialFactor onlinePower : ℕ) {d i j : ℕ} {C : Catalog d} (plan : Online.Config C i j)
    (boot close site terminalPower : ℕ) :
    let localCoeff := workerCap+30+2*(i+j)+20+6*(arity C+1)+2*Online.N d (i+j)+5
    let terminalCoeff := terminalCoefficient S.baseDegree S.steps B.recordLimit boot close site
    ∀ᶠ n : ℕ in atTop,
      let R := processorCount b n
      let H := liveCapacity u n
      let w := wordBits b n
      let T := blockCount (u.θ : ℝ) n
      128 ≤ n ∧ 128 ≤ R ∧ 16 ≤ H ∧ T ≤ n.log2+1 ∧
      (∀ idx : Fin 8, sourceFuel bs i j n idx+5 ≤ H ∧ sourceFuel bs i j n idx+77 ≤ n) ∧
      ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes) (hD : 1 < virtualBits b n)
        (hT : T*S.laneBits ≤ lanes) (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
        let X := pairInput S labels hD
        let E := B.execute f hf T hT X
        ∀ z : E.Choices, let Y := E.finalState z
          let chain := E.termChain (B.records f hf T hT X) z
          320*branchAccesses X Y chain terminalCoeff terminalPower n ≤ R*H ∧
          (∀ v, siteAccesses Y chain site terminalPower n v+9 ≤ H) ∧
          ∀ (p : Ports w) (initial : List (Directory.Row d w))
            (groups : ∀ v : SelectedLevel B f hf, LevelRows (d := d) (w := w) X.positions v)
            (steps : List (Online.Run.Step d (i+j) w)) (m : Memory w),
            calls initial ≤ initialFactor*X.positions →
            Online.Run.Valid plan p (localCoeff*(n.log2+1)^onlinePower) m steps →
            m p.tag.val = LiveStageLink.tagWord w (Online.calendarIndex d (i+j)) →
            steps.map Online.Run.Step.row = branchRows P X.positions (executeLevels B f hf T hT X z) initial groups →
            let rs := Online.Run.reports plan p m steps
            64*RAMBuckets.cost Report.probes rs ≤ R*H ∧ ∀ r ∈ rs, r.probes+11 ≤ H ∧ r.events.length+101 ≤ n := by
  intro localCoeff terminalCoeff
  filter_upwards [eventually_terminal_share B u b hb boot close site terminalPower,
    eventually_selectedOnline B u P workerCap initialFactor onlinePower b hb plan 10 101 (ε := 1/64) (by norm_num),
    eventually_startup_burst u bs i j 5, eventually_sourceFuel bs i j 77,
    eventually_liveCapacity_ge u 16, eventually_numeric B u b 1 hb (by decide),
    eventually_ge_atTop 128] with n terminal online hb' hf' Hge geometry hn
  intro R H w T
  refine ⟨hn,(by have := geometry.2.2.1; omega),Hge,terminal.1,fun idx => ⟨hb' idx,hf' idx⟩,?_⟩
  intro base lanes labels hD hT A _ f hf X E z Y chain
  have ⟨global,vertex⟩ := terminal.2 labels hD hT A f hf z
  refine ⟨global,vertex,?_⟩
  intro p initial groups steps m init valid tag rows rs
  have output := online labels hD hT A f hf z p initial groups steps m 0 init valid tag rows
  have cap := integer_cost_share (by decide : 0<64) output.2.2.2.2
  change 64*RAMBuckets.cost Report.probes rs ≤ processorCount b n*liveCapacity u n ∧
    ∀ r ∈ rs, r.probes+11 ≤ liveCapacity u n ∧ r.events.length+101 ≤ n
  rw [liveCapacity_eq]
  exact ⟨cap,fun r hr => by
    obtain ⟨a,t⟩ := output.2.2.2.1 r hr
    exact ⟨by omega,t⟩⟩

end LiveProgram.CompressedPair

end VPVNP
end Computability
end OAI
