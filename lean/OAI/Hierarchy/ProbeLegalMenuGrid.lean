import OAI.Hierarchy.ProbePublicPrices
import OAI.Hierarchy.ProbePayloadWords
import OAI.Hierarchy.ProbeCommittedMenuRead
import OAI.Hierarchy.ProbeScoreCeiling

namespace OAI
/-! # Both active RAM quote keys belong to their precomputed compact packet menus -/

namespace Hierarchy.ProtocolRAM.StripDirectory
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseCT
open scoped Classical
noncomputable section
open scoped Fin.CommRing

/-- Rounding the actual coordinate stock quote gives a public legal price
and the same one-sided error for every height, inventory and activation phase. -/
theorem rounded_public {a M W T s : ℝ} (N width precision kind stock : ℕ)
    (ha : 0<a) (hm : 0≤M) (hs : 0<s) (hp : 0<precision) :
    let phase:=publicPhase N a M W T s width precision
    let rounded:=(phase.word kind stock:ℝ)/precision
    rounded∈Set.Icc 0 (phase.cap kind) ∧
      rounded≤phase.quote kind stock ∧ phase.quote kind stock<rounded+1/(precision:ℝ) := by
  intro phase rounded
  have cap : 0≤phase.cap kind := by
    change 0≤ if kind=0 then (N:ℝ) else M+1
    split <;> positivity
  have bonus : 0≤phase.bonus kind := by dsimp [phase,publicPhase];split <;> positivity
  have q := phase.approx kind stock ha bonus hm hs cap hp
  change rounded ≤ phase.quote kind stock ∧
    phase.quote kind stock - rounded < 1 / (precision : ℝ) at q
  have box := public_quote_mem (W := W) (T := T) ha hm hs N width precision kind stock
  exact ⟨⟨by dsimp [rounded];positivity,q.1.trans box.2⟩,q.1,by linarith only [q.2]⟩

def payloadKind {N k : ℕ} : PayloadStrip.Quotes N k→ℕ := Sum.elim (fun _=>0) (fun _=>1)

/-- The precise source (including its compulsory payload demand) which witnesses
image membership of the actual payload role price in its fixed menu. -/
theorem payload_grid {N k radix width precision : ℕ} {a M W T s : ℝ}
    (ha : 0<a) (hm : 0≤M) (hs : 0<s) (hp : 0<precision)
    (stock : PayloadStrip.Quotes N k→ℕ)
    (key : Fin (Fintype.card (PayloadStrip.Quotes N k))→Fin radix)
    (read : ∀i,(key (Fintype.equivFin _ i)).val=
      (publicPhase N a M W T s width precision).word (payloadKind i) (stock i)) :
    let y:=payloadGrid radix precision key
    (PayloadStrip.prices N k M y∈(PayloadStrip.prices N k M) '' Set.Icc 0 (PayloadStrip.ceiling N k M)) ∧
      ∀i,y i≤(publicPhase N a M W T s width precision).quote (payloadKind i) (stock i) ∧
        (publicPhase N a M W T s width precision).quote (payloadKind i) (stock i)<y i+1/(precision:ℝ) := by
  intro y
  have all (i) := rounded_public (W := W) (T := T) N width precision (payloadKind i) (stock i) ha hm hs hp
  have fit (i) : y i∈Set.Icc 0 (PayloadStrip.ceiling N k M i) := by
    change ((key (Fintype.equivFin _ i)).val:ℝ)/precision∈_
    rw [read]
    cases i <;> exact (all _).1
  refine ⟨⟨y,⟨fun i=>(fit i).1,fun i=>(fit i).2⟩,rfl⟩,?_⟩
  intro i
  simpa only [y,payloadGrid,read] using (all i).2

/-- Every nonconstant coordinate of the post-purchase strip is an altimeter
lookup on its actual retained tile. All read distinct addresses may share the
signed-kind price table. -/
theorem purchased_grid {N depth k radix width precision : ℕ} {a M W T s : ℝ}
    (ha : 0<a) (hm : 0≤M) (hs : 0<s) (hp : 0<precision)
    (stock : ChainStrip.Axes depth k→ℕ)
    (key : Fin (Fintype.card (ChainStrip.Axes depth k))→Fin radix)
    (read : ∀i,(key (Fintype.equivFin _ i)).val=
      (publicPhase N a M W T s width precision).word 1 (stock i)) :
    let y:=gridAxes radix precision key
    (ChainStrip.prices depth k M y∈(ChainStrip.prices depth k M) '' Set.Icc 0 (fun _=>M+1)) ∧
      ∀i,y i≤(publicPhase N a M W T s width precision).quote 1 (stock i) ∧
        (publicPhase N a M W T s width precision).quote 1 (stock i)<y i+1/(precision:ℝ) := by
  intro y
  have all (i) := rounded_public (W := W) (T := T) N width precision 1 (stock i) ha hm hs hp
  have fit (i) : y i∈Set.Icc 0 (M+1) := by
    change ((key (Fintype.equivFin _ i)).val:ℝ)/precision∈_
    rw [read]
    exact (all i).1
  refine ⟨⟨y,⟨fun i=>(fit i).1,fun i=>(fit i).2⟩,rfl⟩,?_⟩
  intro i
  simpa only [y,gridAxes,read] using (all i).2

/-- The static printed prices and all their legitimate live digits give a bound
on each actual discrepancy word used in a paid-row count. -/
theorem resident_ceiling {F E A : Type*} [Field F] [Fintype E] [Nonempty E] [Fintype A]
    {k digits w : ℕ} [Nonempty (Fin k)] (edge : E→LinearAlgebra.SpectralBooks.ChordGraph.Chord k) (req : A→E)
    (test : StripTest digits) (grid : (Fin digits→Fin test.radix)→E→ℝ)
    (mem : Memory w) (i : Fin test.rows) (key : Fin digits→Fin test.radix) (B : ℝ)
    (pos : 0≤B) (hp : 0<test.precision) (printed : ∀e,0≤grid key e ∧ grid key e≤B)
    (xs : ∀j,(test.quoted j).eval mem (i.val:Word w)=((key j).val:Word w))
    (rom : test.table.read mem ((finFunctionFinEquiv key).val:Word w)=
      (AttemptGate.discrepancyWord F edge req grid test.precision key:Word w))
    (fit : AttemptGate.discrepancyWord F edge req grid test.precision key<2^w) :
    (test.failure.value mem i:ℝ)/test.precision≤B := by
  by_cases asleep : test.live.eval mem (i.val:Word w)=0
  · simpa [FailureWords.value,FailureWords.effective,StripTest.failure,Expr.eval,asleep,
      ThreeFlat.RAM.DescriptorExpr.Comparison.test] using pos
  have read:=resident_score test edge req grid mem i key asleep xs rom fit
  rw [read]
  let trueScore:=Probe.discrepancy F edge req (grid key)
  have bounded : trueScore≤B := Probe.discrepancy_box_bound edge req (grid key) B pos printed
  by_cases nn : 0≤trueScore
  · exact Probe.quantized_ceiling hp nn bounded
  have low : (test.precision:ℝ)*trueScore≤0 := mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg _) (by linarith)
  rw [show ⌊(test.precision:ℝ)*Probe.discrepancy F edge req (grid key)⌋₊=0 from Nat.floor_of_nonpos low]
  simpa using pos


end
end Hierarchy.ProtocolRAM.StripDirectory

end OAI
