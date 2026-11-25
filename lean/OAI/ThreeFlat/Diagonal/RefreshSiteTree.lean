import OAI.ThreeFlat.Diagonal.RefreshPartyPorts
import OAI.ThreeFlat.Diagonal.HistoryDirectParty
import OAI.ThreeFlat.Diagonal.RefreshDensePins
import OAI.ThreeFlat.Diagonal.HistogramPartyBudget
import OAI.ThreeFlat.Diagonal.FixedTileCapacity

namespace OAI
/-! # Compiled local coefficient of an actual degree-refresh history step -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression Computability.VPVNP.MotifSelector LinearAlgebra.SpectralBooks Expander HistoryContraction MotifOuterTerms HistogramTileNetwork
open scoped Classical BigOperators
noncomputable section

variable {V C L F : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field F]
  {m h p : ℕ} (G : LiftedSlots V m (C×L)) (port : Fin m ≃ C) (c : Fin m → Fin m → ℕ)
  (w : Address (V×L) m → ℕ) (base : V×L → Bool×Fin m×Fin m → ℕ) (r : V×L → ℕ)
  (T : ∀ u, FixedMotifTile (RefreshMotif.denseGraph m) (ports c) (base u) F) (x : Histories c base r T)
  (hm : 2 ≤ m) (hh : 0<h) (pad : ℕ) (sym : ∀ i j, c i j=c j i) (rows : ∀ i, ∑ j, c i j=h)
  (zero : ∀ i, c i i=0) {γ : ℝ} (bound : Bound (transition c h) ℝ γ) (u : V×L) (v : Fin m)

local notation "π" => arrival G port
local notation "Y" => actualPortGraph (outputGraph G c sym rows zero hm pad)
local notation "sparseW" => sparseWidth c base r T x
local notation "bw" => termWidth c w sparseW
local notation "newW" => freshWidth c rows bw pad
local notation "D" => RefreshMotif.denseGraph m
local notation "P" => (fun _ : V×L => ports c)
local notation "S" => DoublePorts.connectedSupply c hh rows sym bound
set_option quotPrecheck false in
local notation "idT" => Fintype.equivFin (T u).Alphabet
set_option quotPrecheck false in
local notation "selector" => (fun j e => SlotRefinement.selectorWord (r j) (T j).bits (histWidth (T j).output (x j) e))

/-- Actual output-bit locations, with the raw widths held fixed. -/
private abbrev outputPins (b : RawEdge (fun _ : V × L => Arc c) m → ℕ)
    (j : (V × L) × Fin m) (p : ℕ) :=
  (a : (Y).Port j) → Fin (freshWidth c rows b pad a.1.1) → Fin p

/-- Keep the genuine raw-width function abstract when pulling back the output pins. -/
private def pullPins (b : RawEdge (fun _ : V × L => Arc c) m → ℕ)
    (j : (V × L) × Fin m) (p : ℕ) (pins : outputPins G c hm pad sym rows zero b j p) :
    (a : (rawGraph (externalSite G) P).Port j) → Fin (b a.1.1) → Fin p :=
  actualBit G c sym rows zero hm pad b (v:=j) (p:=p) pins

variable (old : (a : (oldPortGraph (arrival G port)).Port (u,v)) → Fin (w a.1.1) → Fin p)
  (new : outputPins G c hm pad sym rows zero (termWidth c w (sparseWidth c base r T x)) (u,v) p)

attribute [local irreducible] actualPortGraph freshWidth

set_option maxHeartbeats 1000000 in
def siteTree : Tree F p := by
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  letI := (T u).hasLetter
  let B : Header ((D).Port v) (T u).Alphabet (fun q => base u q.1.1) (T u).bits _ := ⟨RefreshParty.denseOrder v,(T u).encode⟩
  let sa := RefreshParty.sparseOrder c sym rows v
  let height := siteHeight (r u) (T u).bitCap
  let src := pullPins G c hm pad sym rows zero bw (u,v) p new
  exact Tree.directParty (F:=F) (p:=p) (k:=(T u).bits) (d:=(T u).bitCap)
    (r:=r u) (e:=2*h) (n:=4*m) (H:=(T u).Alphabet) D S v (profile G port w u) (base u) B sa (T u).output (fun z q => (T u).output_le_cap z _)
    (T u).entry idT (x u) (MotifNativeCompactors.partialInput F (r u*(T u).bitCap) height) (MotifNativeCompactors.partialInput F (r u) height)
    (demandPin π (externalSite G) (external_site G port) P w sparseW u v old src)
    (sparsePin (externalSite G) P w sparseW u v src)

/-- Reading all the physical bits of a state, at the ports of one vertex. -/
private def portReads {U E : Type} (g : PortGraph U E) (width : E → ℕ) (j : U)
    (src : (q : g.Port j) → Fin (width q.1.1) → Fin p)
    (state : g.State (fun e => Fin (2^width e)) j) (pin : Fin p → Bool) : Prop :=
  ∀ (q : g.Port j) (t : Fin (width q.1.1)), pin (src q t) = (state q).val.testBit t.val

set_option maxHeartbeats 1200000 in
omit [Fintype V] [Fintype L] in
theorem siteTree_eval [NeZero m] (fits : ∀ u e, profile G port w u e ≤ base u e*r u) (pin : Fin p → Bool)
    (a : (oldPortGraph π).State (fun e => Fin (2^w e)) (u,v)) (ys : (Y).State (fun e => Fin (2^newW e)) (u,v))
    (aRead : portReads (oldPortGraph π) w (u,v) old a pin)
    (yRead : portReads Y newW (u,v) new ys pin) :
    (siteTree G port c w base r T x hm hh pad sym rows zero bound u v old new).compile.eval pin =
      localEntry G port (fun e => Fin (2^w e)) (fun j => Histogram (T j).Alphabet (r j))
        (fun _ : V×L => Arc c) P (fun j z e => HistogramTileNetwork.Label z (T j).output (T j).bits e)
        (fun j z l => histogramKernel D S (profile G port w j) (base j) (fits j) (T j).output (T j).encode (T j).entry z l)
        x (u,v) a ((physicalRefresh G c sym rows zero hm pad _ bw (termWord c w sparseW _ selector)).read (u,v) ys) := by
  let : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  let := (T u).hasLetter
  let src := pullPins G c hm pad sym rows zero bw (u,v) p new
  let y := (physicalRefresh G c sym rows zero hm pad _ bw (termWord c w sparseW _ selector)).read (u,v) ys
  have read (q : (rawGraph (externalSite G) P).Port (u,v)) (t : Fin (bw q.1.1)) :
      pin (src q t) = (packRaw w sparseW selector q.1.1 (y q)).val.testBit t.val := by
    have e := actualBit_read G c sym rows zero hm pad bw (v:=(u,v)) (p:=p) (termWord c w sparseW _ selector) new pin ys yRead q t
    obtain ⟨⟨(j|j),side⟩,eq⟩ := q <;> exact e
  unfold siteTree localEntry
  refine Tree.directParty_eval (F:=F) (p:=p) (k:=(T u).bits) (d:=(T u).bitCap)
    (r:=r u) (e:=2*h) (n:=4*m) (H:=(T u).Alphabet) D S v (profile G port w u) (base u)
    ⟨RefreshParty.denseOrder v,(T u).encode⟩ (RefreshParty.sparseOrder c sym rows v)
    (T u).output (fun z q => (T u).output_le_cap z _) (T u).entry idT (x u)
    (MotifNativeCompactors.partialInput F (r u*(T u).bitCap) (siteHeight (r u) (T u).bitCap))
    (MotifNativeCompactors.partialInput F (r u) (siteHeight (r u) (T u).bitCap))
    (demandPin π (externalSite G) (external_site G port) P w sparseW u v old src)
    (sparsePin (externalSite G) P w sparseW u v src) (fits u) ?_ ?_ pin _ _ ?_ ?_
  · exact MotifNativeCompactors.partialInput_eval _ _ ((Nat.le_max_right _ _).trans (siteHeight_room _ _))
  · exact MotifNativeCompactors.partialInput_eval _ _ ((Nat.le_max_left _ _).trans (siteHeight_room _ _))
  · exact demandPin_read π (externalSite G) (external_site G port) P w sparseW u v old src selector pin a y aRead read
  · exact sparsePin_read (externalSite G) P w sparseW u v src selector pin y read

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
