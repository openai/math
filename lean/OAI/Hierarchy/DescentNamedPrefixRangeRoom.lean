import OAI.Hierarchy.DescentNamedSiteBill
import OAI.Hierarchy.DescentArchivePalette
import OAI.Hierarchy.DescentChronologicalGrains
import OAI.Hierarchy.DescentResetRetainedCalendarWidths

namespace OAI
/-! # Node capacity at every real prefix in the selected physical register timeline -/
namespace Hierarchy.DescentSixParty.GroupStage
open DescentCompiler StarKeys
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d k : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A : GroupStage W G q ε J V k) (S : AtomSchedule)
set_option quotPrecheck false
local notation "unit" => (A.z*G.b)
local notation "U" => (A.wire*unit*A.cap)
local notation "charge" => W.siteUnits (fun v=>A.hub (A.pos v).2) A.records A.wire 256 A.hist

theorem token_room_of_unit {i : ℕ} (v : W.graph.Site) (positive : 0<S.height) (hh : 0<A.hist)
    (age : i≤S.length) (unitLe : unit≤A.hist)
    (wire : A.wire=S.epochPower^S.priceExponent) (capacity : A.cap≤2^(8+S.capGain*i)) :
    (A.records v).length≤S.epochPower^S.localTokenExponent := by
  have bounded : A.hist*(A.records v).length≤U :=
    (Nat.le_add_left _ _).trans (A.site_units_room v)
  have upstairs : U≤A.hist*(A.wire*A.cap) := by
    calc
      _ ≤ A.wire*A.hist*A.cap := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ unitLe)
      _ = _ := by ring
  have count := Nat.le_of_mul_le_mul_left (bounded.trans upstairs) hh
  rw [wire] at count
  exact count.trans ((Nat.mul_le_mul_left _ (S.local_capacity positive age capacity)).trans_eq
    (pow_add _ _ _).symm)

end
end Hierarchy.DescentSixParty.GroupStage

namespace Hierarchy.DescentKernelHistory.BitDescription
open DescentSixParty Computability.BorderVNP.Crossing DescentCompiler
open scoped Classical BigOperators
noncomputable section
variable {F P H : Type} [Field F] [Fintype P] {d : ℕ} {bits : P→ℕ} {A : MarkedWorld F d P bits}
variable (O : BitDescription A) (old : A.graph.Site→List H)

variable {q ε : ℝ}
variable {k : ℕ} {G : PoweredGadget F} {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
variable (A₀ : GroupStage A G q ε J V k) (S : AtomSchedule)
set_option quotPrecheck false
local notation "tag" => fun v=>A₀.hub (A₀.pos v).2

theorem local_nodes_of_unit {i : ℕ} (rec : O.Tokenized A₀.records) (hJ : 0<S.height) (hh : 0<A₀.hist)
    (age : i≤S.length) (unitLe : A₀.z*G.b≤A₀.hist)
    (wire : A₀.wire=S.epochPower^S.priceExponent) (capacity : A₀.cap≤2^(8+S.capGain*i))
    (allPins : ∀pin,tag (A.graph.attach pin)=true) (widths : ∀pin,bits pin=A₀.hist)
    (hubs : A.HubExterior tag) (v : A.graph.Site) :
    Fintype.card (O.recipe v).Node≤S.epochPower^S.localTokenExponent := by
  rw [rec v]
  cases known : tag v with
  | false=>
    rw [A.exterior_eq_zero tag allPins v known,Nat.add_zero]
    exact A₀.token_room_of_unit S v hJ hh age unitLe wire capacity
  | true=>
    rw [A₀.noHubAtoms v known,List.length_nil,Nat.zero_add]
    have bound := A.hub_token_room A₀ hubs A₀.hist widths hh unitLe v known
    have few : A.exteriorTokens v≤A₀.cap := (Nat.le_mul_of_pos_left _ (by decide : 0<256)).trans bound
    exact (few.trans (S.local_capacity hJ age capacity)).trans (Nat.pow_le_pow_right (Nat.two_pow_pos _)
      (Nat.le_add_left _ _))

end
end Hierarchy.DescentKernelHistory.BitDescription

namespace Hierarchy.DescentSixParty.SeedNamed.Branch
open DescentKernelHistory DescentPrimitivePalette DescentCompiler Chronology
open DescentInitialHost DescentColonies Catalyst DescentMixedRouter DescentResetInvoice
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

variable {F : Type} [Field F] {cp pins : ℕ} (X : Approximation F cp pins) (G : PoweredGadget F) (S : AtomSchedule)
variable {k n h C f g p R : ℕ}
attribute [local irreducible] Origin.source
variable {he : 0 ≤ ((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower}
    {hu : 0 ≤ 1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)) *
      (S.epochPower ^ S.priceExponent : ℝ)}
    {radix : S.radix = 2 ^ k}
    {run : Epochs G hu he (h := h) (C := C) (Ht := GroupStage.depthBound (atRound S.rounds) n f g)
      (t := S.rounds) S.height
      (initial X S.copies (S.firstWidth G.b p) (S.groupCount 0) k (S.initialDigits radix))}
    {c : (Epochs.finish G hu he run).Choice} (br : Branch X G S radix R run c)
variable {W : MarkedWorld F 0 (Σ _ : Fin S.copies, Fin (Fintype.card (Port pins X.width)))
      (fun _ => S.firstWidth G.b p * 1)} {i z D : ℕ}
    {tick : Reached W G (1 / ((S.firstWidth G.b p : ℝ) * (S.epochPower ^ S.priceExponent : ℝ)))
      (((S.initialSites * S.copies : ℕ) : ℝ) / S.epochPower) S k i z D
      (S.epochPower ^ S.priceExponent) (S.firstWidth G.b p)}
    (hp : 0<p) (hh : 0<S.height)
    (before : Path br.origin.source tick) (after : Path tick br.target)
    (cut : before.append after=br.path)

private theorem recorded_before {F Q : Type} [Field F] {d : ℕ} {bits : Q→ℕ}
    {W₀ W₁ W₂ : MarkedWorld F d Q bits} {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {k i₀ z₀ D₀ i₁ z₁ D₁ i₂ z₂ D₂ wire hist : ℕ}
    {a : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist} {b : Reached W₁ G q ε S k i₁ z₁ D₁ wire hist}
    {c : Reached W₂ G q ε S k i₂ z₂ D₂ wire hist} (p : ℕ) (left : Path a b) (right : Path b c) :
    (left.append right).recorded p → left.recorded p := by
  induction right with
  | here=>exact id
  | ordinary _ _ ih=>exact ih
  | reset _ _ ih=>exact fun r=>ih r.1

include after cut in
theorem prefix_tokenized (whole : before.whole p) :
    (before.archive p hp br.origin.archive whole).bit.Tokenized tick.placement.records := by
  have recorded := recorded_before p before after (by simpa only [cut] using br.recorded)
  exact (before.particles p hp br.origin.archive recorded br.origin.particles).nodes

include after cut hh in
theorem prefix_nodes (whole : before.whole p) (v : W.graph.Site) :
    Fintype.card (((before.archive p hp br.origin.archive whole).bit.recipe v).Node)≤S.retainedNodes := by
  have recorded := recorded_before p before after (by simpa only [cut] using br.recorded)
  have real:=before.particles p hp br.origin.archive recorded br.origin.particles
  have time:=after.kinds_length
  have limit : i≤S.length:=by omega
  have unitLe : tick.placement.z*G.b≤tick.placement.hist:=by
    rw [tick.grain,tick.atoms]
    exact Nat.mul_le_mul_right _ (grain_le before)
  apply (before.archive p hp br.origin.archive whole).bit.local_nodes_of_unit tick.placement S real.nodes hh tick.valid.atom
    limit unitLe tick.edges tick.valid.capacity real.attached _ real.balance v
  intro pin
  change S.firstWidth G.b p * 1 = tick.placement.hist
  simpa using tick.atoms.symm

end
end Hierarchy.DescentSixParty.SeedNamed.Branch

end OAI
