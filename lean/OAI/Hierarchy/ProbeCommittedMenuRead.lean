import OAI.Hierarchy.ProbeCommittedLive
import OAI.Hierarchy.ProbeStripScore
import OAI.Hierarchy.ProtocolRAMCalendarMenuROM

namespace OAI
/-! # From an observed affirmative failure bit to the actual selected packet -/

namespace Hierarchy.ProtocolRAM.Calendar.MenuROM
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage.Native StripDirectory
open LinearAlgebra.SpectralBooks.ChordGraph
open scoped Classical Fin.CommRing
noncomputable section
variable {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
  {s : ℕ} [Nonempty (Fin s)] {edge : E→Chord s} {req : A→E} {box : Set (E→ℝ)}
  {ε tree : ℝ} {N w digits phases q goods : ℕ}

/-- The affirmative failure threshold is computed on the rounded price grid.
This gives a failed-menu witness on precisely the grid queried by the packet ROM. -/
theorem selected_score (test : StripTest digits) (grid : (Fin digits→Fin test.radix)→E→ℝ)
    (mem : Memory w) (i : Fin test.rows) (key : Fin digits→Fin test.radix)
    (cut : test.tolerance=ε) (he : 0≤ε) (_hp : 0<test.precision)
    (affirmative : test.failure.cut<test.failure.value mem i)
    (xs : ∀j,(test.quoted j).eval mem (i.val:Word w)=((key j).val:Word w))
    (rom : test.table.read mem ((finFunctionFinEquiv key).val:Word w)=
      (AttemptGate.discrepancyWord F edge req grid test.precision key:Word w))
    (fit : AttemptGate.discrepancyWord F edge req grid test.precision key<2^w) :
    ε≤Probe.discrepancy F edge req (grid key) := by
  have live : test.live.eval mem (i.val:Word w)≠0 := by
    intro asleep
    have zero : test.failure.value mem i=0 := by
      simp [FailureWords.value,FailureWords.effective,StripTest.failure,Expr.eval,asleep,
        ThreeFlat.RAM.DescriptorExpr.Comparison.test]
    omega
  have read := resident_score test edge req grid mem i key live xs rom fit
  rw [read] at affirmative
  change ⌊2*test.tolerance*test.precision⌋₊<_ at affirmative
  rw [cut] at affirmative
  by_contra! small
  have below : (test.precision:ℝ)*Probe.discrepancy F edge req (grid key)≤2*ε*test.precision := by
    have bounds := mul_le_mul_of_nonneg_right (show Probe.discrepancy F edge req (grid key)≤2*ε by linarith)
      (Nat.cast_nonneg (α:=ℝ) test.precision)
    linarith
  exact (not_le_of_gt affirmative) (Nat.floor_mono below)

/-- The price key is read before the three scans. The later batch reads the
very same key from live words; codes and term counts come from immutable pages. -/
theorem selected_packet (menu : Probe.FixedMenu F edge req box ε tree N)
    (test : StripTest digits) (base alphabet : ℕ) (price : Fin phases→(Fin digits→Fin test.radix)→E→ℝ)
    (u : Fin phases) (b : Batch q goods) (mem post : Memory w) (i : Fin test.rows)
    (key : Fin digits→Fin test.radix)
    (cut : test.tolerance=ε) (he : 0≤ε) (hp : 0<test.precision)
    (affirmative : test.failure.cut<test.failure.value mem i)
    (xs : ∀j,(test.quoted j).eval mem (i.val:Word w)=((key j).val:Word w))
    (rom : test.table.read mem ((finFunctionFinEquiv key).val:Word w)=
      (AttemptGate.discrepancyWord F edge req (price u) test.precision key:Word w))
    (fit : AttemptGate.discrepancyWord F edge req (price u) test.precision key<2^w)
    (inside : price u key∈box)
    (page : b.menu=(menus menu base test.radix price).bank u) (rad : b.radix=test.radix)
    (quotes : b.quotes=List.ofFn test.quoted) (terms : b.termCount=(alphabets menu alphabet).bank 0)
    (resident : (menus menu base test.radix price).Resident post) (letters : (alphabets menu alphabet).Resident post)
    (after : ∀j,(test.quoted j).eval post (i.val:Word w)=((key j).val:Word w)) :
    ∃ h : ε≤Probe.discrepancy F edge req (price u key),
      let j:=menu.select ⟨price u key,inside,h⟩
      b.packet.eval post (i.val:Word w)=(((Fintype.equivFin menu.index j).val+1:ℕ):Word w) ∧
      b.termCount.read post (b.packet.eval post (i.val:Word w))=((menu.packet j).terms:Word w) := by
  have failed := selected_score test (price u) mem i key cut he hp affirmative xs rom fit
  exact ⟨failed,packet_failed menu base alphabet test.radix price u b test.quoted post _ key page rad quotes terms
    resident letters after inside failed⟩


end
end Hierarchy.ProtocolRAM.Calendar.MenuROM

end OAI
