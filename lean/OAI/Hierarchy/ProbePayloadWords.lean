import OAI.Hierarchy.ProbeStripScore
import OAI.Hierarchy.ProbeSortedPayload

namespace OAI
/-! # Resident discrepancy words for every original payload row -/

noncomputable section
namespace Hierarchy.ProtocolRAM.StripDirectory

open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage AttemptGate
open scoped Classical Fin.CommRing

variable {z N k w : ℕ}
local notation "Q" => PayloadStrip.Quotes N k
local notation "U" => Commodity (Fin (2^z)) N k

def checkedPayload (z N k : ℕ) (test : StripTest (Fintype.card (PayloadStrip.Quotes N k)))
    (price offsets stocks : Bank) : StripTest (Fintype.card (PayloadStrip.Quotes N k)) :=
  let c := payloadChannels z N k
  tested {test with live := c.live, rows := 2^z, population := 2^z} price offsets stocks c.digit

def payloadGrid (radix precision : ℕ) (v : Fin (Fintype.card Q) → Fin radix) (i : Q) : ℝ :=
  ((v (Fintype.equivFin Q i)).val:ℝ)/precision

def payloadDiscrepancyCode (F : Type*) [Field F] [SiteNaming (PayloadStrip.Site N k)]
    (s : PhasePrice) (scorePrecision radix : ℕ) (v : Fin (Fintype.card Q) → Fin radix) :=
  discrepancyWord F (PayloadStrip.wires N k) (PayloadStrip.demands N k)
    (fun u => PayloadStrip.prices N k s.M (payloadGrid _ s.precision u)) scorePrecision v

private theorem payload_named_eq (F : Type*) [Field F] (a b : PayloadStrip.Naming N k)
    (M : ℝ) (y : Q → ℝ) :
    PayloadStrip.namedError F N k a M y = PayloadStrip.namedError F N k b M y :=
  discrepancy_rename a b (ColumnWires.ends (Strip.horizontal (PayloadStrip.edgeCount N))
    (LocalCommodity.extraEnds (PayloadStrip.commodity N k) (PayloadStrip.noProbe N))) _ _

private theorem payload_measure (F : Type*) [Field F] (name : PayloadStrip.Naming N k)
    (M : ℝ) (actual rounded : Q → ℝ) {η : ℝ} (hn : 0≤η) (close : ∀ i,|actual i-rounded i|≤η)
    {sp n : ℕ} (positive : 0<sp)
    (observed : n=⌊(sp:ℝ)*PayloadStrip.namedError F N k name M rounded⌋₊) :
    PayloadStrip.namedError F N k name M actual ≤ (n:ℝ)/sp+(η+1/sp) := by
  let : SiteNaming (PayloadStrip.Site N k) := ⟨name⟩
  have conn : Probe.Connected (PayloadStrip.wires N k) := by
    apply ColumnWires.connected (testBase (Strip.steps (PayloadStrip.edgeCount N)) 0 (PayloadStrip.edgeCount N))
    apply test_connects
    intro x y near
    obtain ⟨e,_,ends⟩ := Strip.hosts (PayloadStrip.length N)
      (fun e => by dsimp [PayloadStrip.length]; split <;> norm_num) x y near
    exact ⟨e,ends⟩
  have same (e) : |PayloadStrip.prices N k M actual e-PayloadStrip.prices N k M rounded e|≤η := by
    cases e with
    | catalyst => simpa only [ColumnWires.quote,sub_self,abs_zero] using hn
    | radius => simpa only [ColumnWires.quote,sub_self,abs_zero] using hn
    | cross => simpa only [ColumnWires.quote,sub_self,abs_zero] using hn
    | horizontal => simpa only [ColumnWires.quote,sub_self,abs_zero] using hn
    | extra u => cases u with
      | inl a => exact close a
      | inr a => exact a.elim
  have dist := Probe.discrepancy_lipschitz F (PayloadStrip.wires N k) (PayloadStrip.demands N k)
    conn _ _ same
  have diff : PayloadStrip.namedError F N k name M actual-PayloadStrip.namedError F N k name M rounded≤η :=
    (abs_le.mp dist).2
  have hp : (0:ℝ)<sp := Nat.cast_pos.mpr positive
  have floor := Nat.lt_floor_add_one ((sp:ℝ)*PayloadStrip.namedError F N k name M rounded)
  rw [←observed] at floor
  have bound : PayloadStrip.namedError F N k name M rounded ≤ ((n:ℝ)+1)/sp :=
    (le_div_iff₀ hp).mpr (by linarith)
  rw [add_div] at bound
  linarith

/-- Every dense row reads its own stock addresses and resident discrepancy
word. One score table serves every physical site naming, including the
specific numbering induced by the embedding of each payload strip. -/
theorem payload_scores (F : Type*) [Field F] [SiteNaming (PayloadStrip.Site N k)]
    (s : PhasePrice) (m : Memory w) (test : StripTest (Fintype.card Q))
    (price offsets stocks : Bank) (stride : ℕ) (bits : U → ℕ)
    (cell : QuoteCells s m price offsets stocks PurchaseInventory.slot PurchaseInventory.lane bits stride)
    (room : 2^z<2^w) (pos : 0<s.a) (bonus : ∀ i : U,0≤ s.bonus (PurchaseInventory.lane i))
    (hM : 0≤ s.M) (time : 0<s.time) (cap : ∀ i : U,0≤ s.cap (PurchaseInventory.lane i))
    (qp : 0<s.precision) (sp : 0<test.precision)
    (digit : ∀ i : U,s.word (PurchaseInventory.lane i) (bits i)<test.radix)
    (rom : ∀ v,test.table.read m ((finFunctionFinEquiv v).val:Word w) =
      (payloadDiscrepancyCode (N:=N) (k:=k) F s test.precision test.radix v:Word w))
    (fit : ∀ v,payloadDiscrepancyCode (N:=N) (k:=k) F s test.precision test.radix v<2^w) :
    let check := checkedPayload z N k test price offsets stocks
    let post := fun i : U => s.quote (PurchaseInventory.lane i) (bits i)
    ∀ (p : Fin (2^z)) (name : PayloadStrip.Naming N k),
      PayloadStrip.namedError F N k name s.M (PayloadStrip.rowQuotes post p) ≤
        (check.failure.value m p:ℝ)/test.precision+(1/s.precision+1/test.precision) := by
  intro check post p name
  let slot := PayloadStrip.rowAddress (N:=N) (k:=k) p
  let code (i : Q) : Fin test.radix := ⟨s.word (PurchaseInventory.lane (slot i)) (bits (slot i)),digit _⟩
  let v (j : Fin (Fintype.card Q)) := code ((Fintype.equivFin Q).symm j)
  let y := payloadGrid test.radix s.precision v
  have : Nontrivial (Word w) := Fin.nontrivial_iff_two_le.mpr (by have := Nat.two_pow_pos z; omega)
  have live : check.live.eval m (p.val:Word w)≠0 := by
    have below : (p.val : Word w) < ((2^z : ℕ) : Word w) := by
      rw [Fin.lt_def, Fin.val_cast_of_lt (p.isLt.trans room), Fin.val_cast_of_lt room]
      exact p.isLt
    change (if decide ((p.val : Word w) < ((2^z : ℕ) : Word w)) = true then (1 : Word w) else 0) ≠ 0
    simp only [below, decide_true, ite_true]
    intro zero
    have narrow := congrArg Fin.val zero
    change 1 % 2^w = 0 at narrow
    have wide : 1 < 2^w := by have positive := Nat.two_pow_pos z; omega
    exact Nat.one_ne_zero ((Nat.mod_eq_of_lt wide).symm.trans narrow)
  have real (j : Fin (Fintype.card Q)) : (check.quoted j).eval m (p.val:Word w)=((v j).val:Word w) :=
    cell.read _ j _ (slot ((Fintype.equivFin Q).symm j)) (payloadSlot_read m p _)
  have observed : check.failure.value m p =
      ⌊(test.precision:ℝ)*PayloadStrip.namedError F N k name s.M y⌋₊ := by
    let prices := fun u => PayloadStrip.prices N k s.M (payloadGrid test.radix s.precision u)
    have measured := resident_score (F:=F) check (PayloadStrip.wires N k) (PayloadStrip.demands N k)
      prices m p v live real (rom v) (fit v)
    have rename := payload_named_eq F (SiteNaming.labels (X:=PayloadStrip.Site N k)) name s.M y
    exact measured.trans (congrArg (fun x : ℝ => ⌊(test.precision:ℝ)*x⌋₊) rename)
  apply payload_measure F name s.M (PayloadStrip.rowQuotes post p) y (by positivity) _ sp observed
  intro i
  have real := s.approx (PurchaseInventory.lane (slot i)) (bits (slot i)) pos (bonus _) hM time (cap _) qp
  have address : PayloadStrip.rowQuotes post p i = post (slot i) := by cases i <;> rfl
  rw [address]
  change |post (slot i)-((v (Fintype.equivFin Q i)).val:ℝ)/s.precision|≤1/s.precision
  dsimp only [v,code,post]
  rw [Equiv.symm_apply_apply,abs_of_nonneg (sub_nonneg.mpr real.1)]
  exact real.2.le

end Hierarchy.ProtocolRAM.StripDirectory
end

end OAI
