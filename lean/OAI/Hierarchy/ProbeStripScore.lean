import OAI.Hierarchy.ProbeNamingSymmetry
import OAI.Hierarchy.ProbeRetainedLive
import OAI.Hierarchy.ProbeStripFormat
import OAI.Hierarchy.ProbeSortedActivation

namespace OAI
/-! # One physical quote ROM scores the distinct retained rows in their true order -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage PurchaseFrozen AttemptGate
open scoped Classical Fin.CommRing

variable {w depth k digits : ℕ} {F : Type*} [Field F]

/-- A score ROM need only be resident in the replay memory. Fresh scratch
outside the ROM may contain the earlier two threshold sums. -/
theorem resident_score (s : StripTest digits) {E A : Type*} [Fintype E] [Nonempty E] [Fintype A]
    {n : ℕ} [Nonempty (Fin n)] (edge : E→LinearAlgebra.SpectralBooks.ChordGraph.Chord n) (req : A→E)
    (grid : (Fin digits→Fin s.radix)→E→ℝ) (m : Memory w) (i : Fin s.rows)
    (v : Fin digits→Fin s.radix)
    (live : s.live.eval m (i.val:Word w)≠0)
    (xs : ∀ j,(s.quoted j).eval m (i.val:Word w)=((v j).val:Word w))
    (rom : s.table.read m ((finFunctionFinEquiv v).val:Word w) =
      (discrepancyWord F edge req grid s.precision v:Word w))
    (fit : discrepancyWord F edge req grid s.precision v<2^w) :
    s.failure.value m i=⌊(s.precision:ℝ)*Probe.discrepancy F edge req (grid v)⌋₊ := by
  have choose : (menuLookup s.table s.radix (List.ofFn s.quoted)).eval m (i.val:Word w) =
      (discrepancyWord F edge req grid s.precision v:Word w) := by
    change s.table.read m _=_
    rw [eval_menuKey _ _ _ v xs]
    exact rom
  simp only [FailureWords.value,FailureWords.effective,StripTest.failure,Expr.eval,
    ThreeFlat.RAM.DescriptorExpr.Comparison.test,Nat.cast_zero,beq_iff_eq,
    ite_eq_right live]
  exact (congrArg Fin.val choose).trans (Fin.val_cast_of_lt fit)

/-- Counted pointer, mutable physical stock and immutable phase-price ROM
at the exact live replay state. The bits and prices are computed globally
once, before individual bought strips are considered. -/
structure QuoteCells {U : Type*} (phase : PhasePrice) (m : Memory w)
    (price offsets stocks : Bank) (slot lane bits : U→ℕ) (stride : ℕ) : Prop where
  offset : ∀ i,offsets.read m (slot i : Word w)=((lane i*stride:ℕ):Word w)
  stock : ∀ i,stocks.read m (slot i : Word w)=(bits i:Word w)
  rom : ∀ i,price.read m ((lane i*stride+bits i:ℕ):Word w)=(phase.word (lane i) (bits i):Word w)

theorem QuoteCells.read {U : Type*} {phase : PhasePrice} {m : Memory w}
    {price offsets stocks : Bank} {slot lane bits : U→ℕ} {stride : ℕ}
    (C : QuoteCells phase m price offsets stocks slot lane bits stride)
    (addr : Fin digits→Expr) (j : Fin digits) (row : Word w) (i : U)
    (atSlot : (addr j).eval m row=(slot i:Word w)) :
    (quoted price offsets stocks addr j).eval m row=(phase.word (lane i) (bits i):Word w) := by
  rw [quoted_read,atSlot,C.offset,C.stock,←Nat.cast_add]
  exact C.rom i

/-- Fixed payload, fee, catalyst and horizontal components are exact.
Only the read-back altimeter price can lose a phase rounding unit. -/
theorem price_error (M : ℝ) (p q : ChainStrip.Axes depth k→ℝ) {η : ℝ} (hη : 0≤η)
    (h : ∀i,|p i-q i|≤η) (e) :
    |ChainStrip.prices depth k M p e-ChainStrip.prices depth k M q e|≤η := by
  cases e with
  | catalyst => simpa only [ColumnWires.quote,sub_self,abs_zero] using hη
  | radius => simpa only [ColumnWires.quote,sub_self,abs_zero] using hη
  | cross => simpa only [ColumnWires.quote,sub_self,abs_zero] using hη
  | horizontal => simpa only [ColumnWires.quote,sub_self,abs_zero] using hη
  | extra u => cases u with
    | inl a => exact h a
    | inr a => simpa only [ChainStrip.prices,ColumnWires.quote,LocalCommodity.extraPrice,sub_self,abs_zero] using hη

def gridAxes (radix precision : ℕ) (v : Fin (Fintype.card (ChainStrip.Axes depth k))→Fin radix)
    (i : ChainStrip.Axes depth k) : ℝ := ((v (Fintype.equivFin _ i)).val:ℝ)/precision

/-- Read the discrepancy of an arbitrary *physical* naming from the
single statically mounted canonical score table for this local format. -/
theorem named_score [SiteNaming (ChainStrip.Site depth k)] (s : StripTest (Fintype.card (ChainStrip.Axes depth k)))
    (M : ℝ) (precision : ℕ) (name : ChainStrip.Naming depth k) (m : Memory w) (i : Fin s.rows)
    (v : Fin (Fintype.card (ChainStrip.Axes depth k))→Fin s.radix)
    (live : s.live.eval m (i.val:Word w)≠0) (xs : ∀j,(s.quoted j).eval m (i.val:Word w)=((v j).val:Word w))
    (rom : s.table.read m ((finFunctionFinEquiv v).val:Word w)=
      (discrepancyWord F (ChainStrip.wires depth k) (ChainStrip.demands depth k)
        (fun u=>ChainStrip.prices depth k M (gridAxes _ precision u)) s.precision v:Word w))
    (fit : discrepancyWord F (ChainStrip.wires depth k) (ChainStrip.demands depth k)
      (fun u=>ChainStrip.prices depth k M (gridAxes _ precision u)) s.precision v<2^w) :
    s.failure.value m i=⌊(s.precision:ℝ)*ChainStrip.namedError F depth k name M (gridAxes s.radix precision v)⌋₊ := by
  let prices := fun u => ChainStrip.prices depth k M (gridAxes s.radix precision u)
  have measured := resident_score (F:=F) s (ChainStrip.wires depth k) (ChainStrip.demands depth k)
    prices m i v live xs rom fit
  let canonical := SiteNaming.labels (X:=ChainStrip.Site depth k)
  have rename := ChainStrip.namedError_eq F depth k canonical name M (gridAxes s.radix precision v)
  exact measured.trans (congrArg (fun x : ℝ => ⌊(s.precision:ℝ)*x⌋₊) rename)

/-- Exact integer discrepancy measured on a rounded grid costs at most
one quote unit plus one final score unit, independently of the candidate
board's padding. -/
theorem measured_named (s : StripTest (Fintype.card (ChainStrip.Axes depth k))) (M : ℝ)
    (name : ChainStrip.Naming depth k) (m : Memory w) (i : Fin s.rows)
    (actual rounded : ChainStrip.Axes depth k→ℝ) {η : ℝ} (hη : 0≤η) (close : ∀j,|actual j-rounded j|≤η)
    (pos : 0<s.precision) (score : s.failure.value m i=⌊(s.precision:ℝ)*ChainStrip.namedError F depth k name M rounded⌋₊) :
    ChainStrip.namedError F depth k name M actual≤(s.failure.value m i:ℝ)/s.precision + (η+1/s.precision) := by
  let : SiteNaming (ChainStrip.Site depth k) := ⟨name⟩
  have conn : Probe.Connected (ChainStrip.wires depth k) := by
    apply ColumnWires.connected (testBase (Strip.steps (ChainStrip.edgeCount depth)) 0 (ChainStrip.edgeCount depth))
    apply test_connects
    intro x y near
    obtain ⟨e,_,ends⟩ := Strip.hosts (ChainStrip.length depth) (fun e=>by dsimp [ChainStrip.length]; split <;> norm_num) x y near
    exact ⟨e,ends⟩
  have dist := Probe.discrepancy_lipschitz F (ChainStrip.wires depth k) (ChainStrip.demands depth k)
    conn _ _ (price_error M actual rounded hη close)
  have diff : ChainStrip.namedError F depth k name M actual-ChainStrip.namedError F depth k name M rounded≤η := (abs_le.mp dist).2
  have hp : (0:ℝ)<s.precision := Nat.cast_pos.mpr pos
  have low := Nat.lt_floor_add_one ((s.precision:ℝ)*ChainStrip.namedError F depth k name M rounded)
  rw [←score] at low
  have below : ChainStrip.namedError F depth k name M rounded ≤ ((s.failure.value m i:ℝ)+1)/s.precision :=
    (le_div_iff₀ hp).2 (by linarith)
  rw [add_div] at below
  linarith

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
