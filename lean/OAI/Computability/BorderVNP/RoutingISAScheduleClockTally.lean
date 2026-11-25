import OAI.Computability.BorderVNP.CellTeamOperandClock
import OAI.Computability.BorderVNP.DiagonalTallyAlignedEvaluation
import OAI.Computability.BorderVNP.DiagonalResidueRAMLeadSum
import OAI.Computability.BorderVNP.TransmissionChosenPacket
import OAI.Computability.BorderVNP.RoutingISAScheduleClockRate

/-! # Charging the aligned tally and final lead-team reader

Sparse work is counted on the physically emitted cell reports and owned
vertices. The remaining work processes the complete rectangular table of
team subtotals. Both that rectangle and the lead team's exact staged reader
fit one fixed polynomial in the chosen reader charge and the number of teams.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.ScheduleClock

open VPVNP.BurstRAM DiagonalTallyRAM DiagonalTallyMaterialize DiagonalTallyCellReports
open ResidueRates DiagonalResidueRAM Filter

/-- Sparse, rectangular and fixed scalar charges of the complete aligned
arena. The count and the materializer's bit visits use the actual record list. -/
theorem alignedWork_le (a : Arena) {l : ReportLayout} (cs : List (ReportCell l)) (q : ReportCursor)
    (vertices : ℕ) (record : Fin vertices → Operand) (cube : ∀ j, (record j).digits.length=1)
    (pubWords powers w : ℕ) (countFields : cs.length*(l.gadgets+l.gadgets*l.countWidth) ≤ pubWords)
    (use : teamWeighted cs ≤ powers) (count : a.count=(cellOperands cs q ++ List.ofFn record).length)
    (width : a.width ≤ w) :
    let os := cellOperands cs q ++ List.ofFn record
    alignTallies.slots+allocateTallies.slots+a.work w os ≤
      64*(pubWords+powers+vertices)+512*(a.teams+1)*(a.dim+1)*(w+1) := by
  intro os
  have mat := materialize_charge cs q vertices record cube pubWords powers countFields use
  have simple : a.count ≤ pubWords+powers+vertices := by
    rw [count,List.length_append,List.length_ofFn,(actual_operand_sizes cs q).1]
    rw [Nat.mul_add] at countFields
    omega
  change 16+21*os.length+8*(os.map fun o => o.digits.length).sum+1 ≤ 16+1+21*pubWords+29*(powers+vertices) at mat
  change 14+49+(16+21*os.length+8*(os.map fun o => o.digits.length).sum+1+(11+4*a.dim+1)+
    (19+22+20+18+(13*a.count+3)+(8*(a.teams*a.dim)*(a.width+1)+8)+(6*a.dim+1)+((5*a.teams+8)*a.dim+1))+
    19+10*(a.dim*w)+1) ≤ _
  calc
    _ ≤ 14+49+(17+21*pubWords+29*(powers+vertices)+(11+4*a.dim+1)+
      (19+22+20+18+(13*(pubWords+powers+vertices)+3)+(8*(a.teams*a.dim)*(w+1)+8)+(6*a.dim+1)+
      ((5*a.teams+8)*a.dim+1))+19+10*(a.dim*w)+1) := by gcongr
    _ ≤ _ := by ring_nf; omega

/-- Aligned allocation and all tally stages execute on the emitted count/use
descriptors and vertex suffix. The serialized words are the exact natural
team sums. The sparse bound counts only occupied descriptors and bits. -/
theorem aligned_natural_run {w : ℕ} (a : Arena) {l : ReportLayout} (cs : List (ReportCell l))
    (q : ReportCursor) (vertices : ℕ) (record : Fin vertices → Operand) (cube : ∀ j, (record j).digits.length=1)
    (pubWords powers : ℕ) (countFields : cs.length*(l.gadgets+l.gadgets*l.countWidth) ≤ pubWords)
    (use : teamWeighted cs ≤ powers) (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (ptr : ℕ) (rows : Fin a.teams → Fin a.dim → ℕ) :
    let os := cellOperands cs q ++ List.ofFn record
    a.alignedSeed pub m ptr → ∀ fit : a.Fits w (pub 0).val, (pub 0).val+101 < 2^w →
    supplied m a.fresh ptr os →
    (∀ j, operandReads ptr os j → outsidePointers (pub 0).val j ∧ j≠(pub 0).val+34) →
    (∀ j, a.raw≤j → j<a.raw+(a.teams*a.dim)*a.width → outsidePointers (pub 0).val j ∧ j≠(pub 0).val+34) →
    os.length=a.count → (∀ o∈os,o.pair.1<a.dim) →
    DiagonalTallyBits.WordsAt m a.raw (broadcast a.width rows) →
    (∀ c,a.localRow os c.val=rows ⟨a.team,fit.team⟩ c) →
    (∀ i c,rows i c<2^a.width) → (∀ c,∑ i, rows i c<2^w) →
    ∃ es t m', Runs pub mac alignedAllocateAndEvaluate s m es t m' ∧
      traceCost es ≤ 64*(pubWords+powers+vertices)+512*(a.teams+1)*(a.dim+1)*(w+1) ∧
      (∀ e∈es,e.choices=[] ∧ e.sign=.plus ∧ e.action.extra=0) ∧
      ∀ c : Fin a.dim, ∀ j<w, m' ((a.bitFrame w).dst+(c.val*w+j))=word w (((∑ i,rows i c).testBit j).toNat) := by
  intro os seed fit header ops opSep rawSep count coords bits localCounts rowFit sumFit
  obtain ⟨es,t,mt,run,cost,trace,out⟩ := alignedAllocateAndEvaluate_natural_runs a pub mac s m os ptr rows
    seed fit header ops opSep rawSep count coords bits localCounts rowFit sumFit
  exact ⟨es,t,mt,run,cost.trans (alignedWork_le a cs q vertices record cube pubWords powers w
    countFields use count.symm fit.width),trace,out⟩

/-- The exact lead-team staging and gate/guess scan fit the same charge as
the selected finite-field verifier. The other teams' seven instructions
fit the same upper bound. -/
theorem leadTicks_le (x : ReaderSizes) (k v : ℕ) (hv : v ≤ x.guessBits) :
    max 7 (6+(prepareTicks x.publicBits k x.word+ticks k v)) ≤ 7+x.stagedCharge k := by
  let B := x.publicBits+x.guessBits+k+x.word
  have h := staged_ticks_le (u:=x.publicBits) (k:=k) (v:=v) (w:=x.word) (B:=B)
    (by dsimp [B]; omega) (by dsimp [B]; omega) (by dsimp [B]; omega) (by dsimp [B]; omega)
  dsimp only [ReaderSizes.stagedCharge]
  dsimp only [B] at h
  omega

/-- For either physical team role, every returning actual lead fragment is
charged to its staged certificate. The word-room and source premises are
needed only for the reader invoked on team zero. -/
theorem lead_traceCost {w u v k : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (x : ReaderSizes) (hu : u=x.publicBits) (hw : w=x.word) (hv : v ≤ x.guessBits)
    (s : Bank w) (mem : Memory w) (base start dense : ℕ) (src : Fin u → ℕ)
    (c : VPVNP.BooleanTranscript.Circuit (Fin u ⊕ Fin v) k) (bits : Fin u → Bool)
    (zero : mem (pub 0).val = 0 → DiagonalResidueRAM.Layout base start dense src v k w ∧ (pub 0).val+30<2^w ∧
      packFrame pub mem dense start (6+3*k+u) ∧
      DiagonalTallyBits.WordsAt mem dense ((payload w base start c src).map wordBits) ∧
      ∀ i, mem (src i)=wordBit w (bits i))
    {es t mt} (run : Runs pub mac leadEntry s mem es t mt) : traceCost es ≤ 7+x.stagedCharge k := by
  have bound := leadTicks_le x k v hv
  by_cases h : mem (pub 0).val = 0
  · obtain ⟨L,frameFit,pack,advice,source⟩ := zero h
    obtain ⟨_,_,_,cost,_⟩ := lead_zero_ticks pub mac s mem base start dense src c bits L frameFit pack advice source h run
    rw [cost,hu,hw]
    exact (le_max_right ..).trans bound
  · rw [(lead_other_ticks h run).1]
    exact (le_max_left ..).trans bound

/-- Actual rectangular word work and the final reader fit one polynomial of
the stage certificate. The public pin and count input widths cover every
local coordinate when the transmitted subtotal has at least one bit. -/
theorem readerRectangle_le (x : ReaderSizes) (k R : ℕ) (tally : 1 ≤ x.tally) :
    512*(R+1)*(x.h+x.labels+1)*(x.word+1) + (7+x.stagedCharge k) ≤
      1024*(R+1)*(x.stagedCharge k+1)^2 := by
  let C := x.stagedCharge k
  have dim0 : x.h+x.labels ≤ (x.h+x.labels)*x.tally := Nat.le_mul_of_pos_right _ tally
  have dim : x.h+x.labels ≤ C := by dsimp only [C,ReaderSizes.stagedCharge,ReaderSizes.publicBits]; omega
  have word : x.word ≤ C := by
    have sq := Nat.le_self_pow (by decide : 2 ≠ 0) (x.publicBits+x.guessBits+k+x.word+1)
    dsimp only [C,ReaderSizes.stagedCharge]
    omega
  have rect : 512*(R+1)*(x.h+x.labels+1)*(x.word+1) ≤ 512*(R+1)*(C+1)^2 := by
    rw [pow_two,← Nat.mul_assoc]
    gcongr
  change _ + (7+C) ≤ 1024*(R+1)*(C+1)^2
  calc
    _ ≤ 512*(R+1)*(C+1)^2+(7+C) := Nat.add_le_add_right rect _
    _ ≤ _ := by ring_nf; omega

/-- The geometric stretch absorbs all dense native tally work and the
lead-team entry call uniformly over the later chosen chart and layout. -/
theorem eventually_readerRectangle {σ ρ : ℝ} (positive : 0 < σ) (gap : σ<ρ)
    (ceiling : ℕ → ℕ) (poly : VPVNP.PolynomiallyBounded ceiling) (A C E J : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (x : ReaderSizes) (k R : ℕ), let M := Diagonal.adviceScale σ ρ n
      R ≤ E*(M+1)^J → x.stagedCharge k ≤ A*(ceiling M+1)^C → 1 ≤ x.tally →
      512*(R+1)*(x.h+x.labels+1)*(x.word+1)+(7+x.stagedCharge k) < Diagonal.stretch ρ n := by
  let R (M : ℕ) := E*(M+1)^J
  let K (M : ℕ) := A*(ceiling M+1)^C
  let bound (M : ℕ) := 1024*(R M+1)*(K M+1)^2
  have r : VPVNP.PolynomiallyBounded R := (VPVNP.PolynomiallyBounded.const E).mul
    ((VPVNP.PolynomiallyBounded.id.add (.const 1)).pow J)
  have c : VPVNP.PolynomiallyBounded K := (VPVNP.PolynomiallyBounded.const A).mul ((poly.add (.const 1)).pow C)
  have b : VPVNP.PolynomiallyBounded bound := ((VPVNP.PolynomiallyBounded.const 1024).mul
    (r.add (.const 1))).mul ((c.add (.const 1)).pow 2)
  filter_upwards [Diagonal.polynomial_at_adviceScale_lt_batch positive gap b] with n room
  intro x k teams M teamSize entry tally
  apply (readerRectangle_le x k teams tally).trans_lt
  apply lt_of_le_of_lt _ room
  change _ ≤ 1024*(R M+1)*(K M+1)^2
  gcongr

end RoutingISA.Evaluator.ScheduleClock

end BorderVNP
end Computability
end OAI
