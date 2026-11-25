import OAI.Computability.BorderVNP.PackedInheritedWorkRound
import OAI.Computability.BorderVNP.PackedInheritedWorkDirectory
import OAI.Computability.BorderVNP.PackedInheritedWorkParallel
import OAI.Computability.BorderVNP.PackedInheritedWorkHistogram
import OAI.Computability.BorderVNP.PackedTerminalEndpointFields
import OAI.Computability.BorderVNP.PackedInheritedDenseOrder

/-! # Permanent work/extent output of the actual named crossing node

The circuit reads the extents in the child rectangles, the physical guess
bits, and the stored cable rows. Its choice depends only on the static row
shapes and the port naming. Every attained dense output then has both
arithmetic words at its genuine site number.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Shortening Shortening.StaticRows Shortening.PublicParallel Shortening.PublicEndpoints
open Epoch Cover PackedHistoryCircuit PackedHistoryCircuit.Normalized
open Diagonal.ExternalSew.FieldExport ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {D m k V E n np w : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A B σ : Type} [Fintype A] [Fintype σ] (seed : A ↪ Fin n)
local notation3 "sites" => siteCapacity e (k*V) n

/-- Pin aliases and static port attachment fields of the common gate input.
The geometry front-end and its validity bit may have been produced jointly
with other retained block operands. -/
structure NodeFields (B σ : Type) where
  /-- Input pin for one bit of the program extent at a given child site row. -/
  child : Fin k × Fin V × Fin w → σ
  /-- Input pin for a bit of the guessed multiplicity of a summand at a given seed. -/
  guess : A × Fin e.count × Fin w → σ
  /-- Input pins carrying the saved directory, including cable endpoints and widths. -/
  saved : Inputs B (siteCapacity e (k*V) n) E w w → σ
  /-- Site row to which each occupied external port slot is attached. -/
  host : Fin np → ℕ
  /-- Bit width of each external port slot, with zero width for unused slots on a valid input. -/
  width : Fin np → ℕ
  siteFit : siteCapacity e (k*V) n ≤ 2^w

variable (a : NodeFields (A := A) (k := k) (V := V) (E := E) (n := n) (np := np) (w := w) e B σ)

private noncomputable abbrev childRows := Frame.initial (Sum.inl ∘ a.child : Fin k × Fin V × Fin w → σ ⊕ Bool)
private noncomputable abbrev guesses := Frame.initial (Sum.inl ∘ a.guess : A × Fin e.count × Fin w → σ ⊕ Bool)
private noncomputable abbrev counts := (exists_counts (guesses e a)).choose
private noncomputable abbrev work := (exists_round e seed (parallelRows (childRows e a)) (counts e a)).choose
private abbrev physical := TerminalCells.endpointFields a.siteFit a.saved a.host a.width
private noncomputable abbrev words := (exists_directory (physical e a) (work e seed a)).choose

/-- Literal arithmetic side output for the common selected history node. -/
noncomputable def node : Frame σ (Fin (siteCapacity e (k*V) n) × Bool × Fin w) :=
  (words e seed a).subst (constants σ)

/-- Only one copy of the work circuit and the virtual incidence scan is charged. -/
theorem node_size : (node e seed a).size ≤ 7 +
    Fintype.card A*((2*e.count+1) + birthNodes e)*(100*(w+1)^2) +
    (Views.frame (physical e a)).size + sites*3*(100*(w+1)^2) := by
  have hc := (exists_counts (guesses e a)).choose_spec.1
  have hw := (exists_round e seed (parallelRows (childRows e a)) (counts e a)).choose_spec.1
  have he := (exists_directory (physical e a) (work e seed a)).choose_spec.1
  have hz := constants_size σ
  change (counts e a).size ≤ _ at hc
  change (work e seed a).size ≤ _ at hw
  change (words e seed a).size ≤ _ at he
  simp only [guesses,childRows,parallelRows,Frame.initial_size,Frame.select_size,zero_add] at hc hw
  rw [Nat.mul_add (Fintype.card A) (2*e.count+1) (birthNodes e),Nat.add_mul]
  simp only [node,Frame.subst_size]
  omega

set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency false
variable {lev d : ℕ} {Bin P : Type} [Fintype Bin] [Fintype P] {bits : P → ℕ}
variable {child : Fin k → PlacedPack D P bits K (Cube D) d}
local notation3 "seeds" => ((Cube D → Deck (lev+1)) × Bin)
variable (s : Stage m Bin lev child) (names : ∀ i, (child i).pack.layout.Site ↪ Fin V)
variable (q : s.Index e) (pdir : Directory (s.result e q) (siteCapacity e (k*V) n) E)
variable (seedID : ((Cube D → Deck (lev+1)) × Bin) ↪ Fin n)
variable (src : NodeFields (A := ((Cube D → Deck (lev+1)) × Bin)) (k := k) (V := V) (E := E)
    (n := n) (np := np) (w := w) e B σ)
variable (port : (Fin k × P) ↪ Fin np) (position : e.Entry → ℕ) (binName : ((Cube D → Deck (lev+1)) × Bin) → ℕ)
variable (old : ∀ i, (child i).pack.layout.Site → Site) (cuts : s.input.layout.Site → List Slice)
local notation3 "site" => siteRows e s.input (parallelName names) seedID
local notation3 "program" => roundSites e s.input s.label s.perm s.orient (0,false) q binName position
  pdir.sites pdir.cables port (fun z => old z.1 z.2) cuts
local notation3 "savedN" => ((s.result e q).dense pdir.cables).pack.layout

/-- Specialization to the actual named branch, including its dense cable save.
The external site pointers, widths and holes come from the static public
port rectangle. No private work word is supplied for the successor. -/
theorem node_covers (room : ∀ t, s.matched t < 2^w) (x : σ → Bool)
    (hsite : pdir.sites = site)
    (childOK : ∀ i, Covers (names i) (fun v => (old i v).size)
      (Frame.initial fun z => src.child (i,z)) x)
    (hist : x ∘ src.guess = NamedReceipt.word s room q)
    (ready : PublicEndpoints.Represents savedN pdir.dense.sites pdir.dense.cables pdir.dummy (x ∘ src.saved))
    (addr : ∀ p, src.host (port p) = (pdir.dense.sites ((savedN).attach p)).val)
    (sizes : ∀ p, src.width (port p) = bits p.2) (fits : ∀ i, src.width i < 2^w)
    (holes : ∀ i ∉ Set.range port, src.width i = 0) (space : ∀ v, (program v).size < 2^w) :
    Covers pdir.dense.sites (fun v => (program v).work) (column (node e seedID src) false) x ∧
      Covers pdir.dense.sites (fun v => (program v).size) (column (node e seedID src) true) x := by
  let y := (constants σ).eval x
  have prev := parallel_covers names (fun i v => (old i v).size) (childRows e src) y
    (fun i => by
      obtain ⟨hl,hh⟩ := childOK i
      constructor
      · simpa only [childRows,Frame.select_eval,Frame.initial_eval,Function.comp_apply,y,constants_eval,
          Sum.elim_inl] using hl
      · simpa only [childRows,Frame.select_eval,Frame.initial_eval,Function.comp_apply,y,constants_eval,
          Sum.elim_inl] using hh)
  have gg : (guesses e src).eval y = NamedReceipt.word s room q := by
    funext i
    simpa only [guesses,Frame.initial_eval,Function.comp_apply,y,constants_eval,Sum.elim_inl] using congrFun hist i
  have hh := named_counts e s room q gg (counts e src) ((exists_counts (guesses e src)).choose_spec.2 y)
  have cw := (exists_round e seedID (parallelRows (childRows e src)) (counts e src)).choose_spec.2 s.input s.label
    s.perm s.orient (0,false) q binName position (parallelName names) pdir.cables port _ cuts y prev hh (hsite ▸ space)
  have cp := TerminalCells.named_endpoints src.siteFit src.saved src.host src.width savedN pdir.dense.sites
    pdir.dense.cables pdir.dummy port x ready addr sizes fits holes
  simp only [Directory.dense_sites] at cp ⊢
  have hin (v) : (program v).incoming = incoming savedN v :=
    (roundSites_incoming e s.input s.label s.perm s.orient (0,false) q binName position pdir.sites pdir.cables port
      (fun z => old z.1 z.2) cuts v).trans (dense_incoming (s.result e q).pack.layout pdir.cables v).symm
  rw [← hsite] at cw
  have ⟨_,hw,he⟩ := (exists_directory (physical e src) (work e seedID src)).choose_spec
  have ok := directory_covers (physical e src) (work e seedID src) savedN pdir.sites pdir.dense.cables port cp
    program hin cw space (words e seedID src) (hw y) (he y)
  have transfer (b : Bool) (length : (savedN).Site → ℕ)
      (h : Covers pdir.sites length (column (words e seedID src) b) y) :
      Covers pdir.sites length (column (node e seedID src) b) x := by
    obtain ⟨live,unused⟩ := h
    constructor
    · simpa only [column,node,Frame.select_eval,Frame.subst_eval,y] using live
    · simpa only [column,node,Frame.select_eval,Frame.subst_eval,y] using unused
  exact ⟨transfer false _ ok.1,transfer true _ ok.2⟩

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
