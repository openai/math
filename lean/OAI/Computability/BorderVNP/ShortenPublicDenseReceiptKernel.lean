import OAI.Computability.BorderVNP.PackedHistoryDenseReconstruction
import OAI.Computability.BorderVNP.ShortenPublicRoundInput
import OAI.Computability.BorderVNP.ShortenPublicDenseSiteReads
import OAI.Computability.BorderVNP.ShortenDenseSourceReceipts

/-! # One physical cut, guarded by the guessed count words

The actual computed numeric directory and site mover share a single prefix.
The separate input block contains exactly the profile count bits. All
successor fields, the presence column and the validity bit are produced on
the saved physical ordering of the selected dense crossing.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicDenseReceipt

open Cover Cover.Frame Cover.AddressCircuit Crossing Epoch Catalog StaticRows CombiningStep
open PreparedBins PublicSegments PublicRelative Packing DirectoryCircuit PublicDirectory
open BankCircuit VPVNP.VerifierNetwork ParseBatchSort BorderVNP.PackedHistoryCircuit.Normalized
open scoped Classical BorderVNP.Epoch.Cube

/-- Reindex the physical numeric directory operand wires. -/
def mapPins {U σ τ : Type*} {k w : ℕ} (f : σ → τ) (p : PublicPopulation.Pins U σ k w) :
    PublicPopulation.Pins U τ k w where
  active := f ∘ p.active
  key u := f ∘ p.key u
  width u := f ∘ p.width u

/-- Reindex the old cable directory operand wires. -/
def mapColumns {σ τ : Type*} {M D w : ℕ} (f : σ → τ) (c : Columns σ M D w) : Columns τ M D w where
  occupied := f ∘ c.occupied
  positive := f ∘ c.positive
  endpoint u s := f ∘ c.endpoint u s
  padding r := f ∘ c.padding r

/-- Reindexing the physical operands along a wire inclusion preserves every
numeric, presence and padding assertion. -/
theorem ready_map {D m M V seeds k w : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)
    {σ τ : Type*} {A : Type} {P : Type*} {bits : P → ℕ}
    (f : σ → τ) (p : PublicPopulation.Pins (Fin M) σ k w) (c : Columns σ M D w)
    (code : A ↪ Fin (2^k)) (seed : A ≃ Fin seeds) (N : Pack D P bits K)
    (bin : N.layout.Edge → Option A) (orient : N.layout.Edge → Bool)
    (old : N.layout.Site ↪ Fin V) (slot : N.layout.Edge ↪ Fin M)
    (dummy : Fin (edgeCapacity e M seeds) → SiteShape e (densePack N slot) A)
    (x : τ → Bool) (h : Ready e p c code seed N bin orient old slot dummy (x ∘ f)) :
    Ready e (mapPins f p) (mapColumns f c) code seed N bin orient old slot dummy x :=
  ⟨⟨h.population.active,h.population.absent,h.population.address,h.population.width⟩,
    h.room,h.widths,h.occupied,h.orientation,h.endpoints,h.padding⟩

/-- Source-independent tuple of guessed profile words. -/
abbrev Words (A : Type*) (terms w : ℕ) := A × Fin terms × Fin w

/-- Pair the common computed directory with the raw guess wires. Each
computed prefix gate appears just once. -/
noncomputable def withWords {X Table Geo W : Type*} [Fintype X] [Fintype Table] [Fintype Geo] [Fintype W]
    (f : Frame X (Table ⊕ Geo)) : Frame (X ⊕ W) ((Table ⊕ Geo) ⊕ W) :=
  parallelFrame (f.subst (Frame.initial Sum.inl)) (Frame.initial Sum.inr)

/-- Appending the guesses uses the very same gates. -/
theorem withWords_size {X Table Geo W : Type*} [Fintype X] [Fintype Table] [Fintype Geo] [Fintype W]
    (f : Frame X (Table ⊕ Geo)) : (withWords (W := W) f).size = f.size := by simp [withWords]

/-- Exact input interpretation of the checked dense successor. -/
theorem withWords_eval {X Table Geo W : Type*} [Fintype X] [Fintype Table] [Fintype Geo] [Fintype W]
    (f : Frame X (Table ⊕ Geo)) (x : X → Bool) (word : W → Bool) :
    (withWords f).eval (Sum.elim x word) = Sum.elim (f.eval x) word := by
  funext j
  rcases j with j | j
  · simp only [withWords,parallelFrame_eval_inl,Frame.subst_eval,Sum.elim_inl]
    congr 1
    funext i
    simp
  · simp [withWords]

variable {D m q : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    (enum : Fin q ≃ Cube D) (pat : Pattern (Cube D) D) (S : Finset (HyperbolicHost (Cube D)))

set_option maxHeartbeats 2000000 in
/-- The shared numeric and geometric preparation is used exactly once before
checking the count guesses and saving the occupied successor rows. -/
theorem prepared_frames (hm : 0 < m) :
    ∃ C E C' E' G H : ℕ, ∀ {B P : Type} [Fintype B] {bits : P → ℕ}
      (d lev prior copies V M seeds k w : ℕ), 1 ≤ d → (hl : lev+1=d+2*pat.depth) →
      let A := (Cube D → Deck (lev+1)) × B
      let Geo := BatchPorts q pat S d copies V seeds
      let Data := ProductSlots q (d+2*pat.depth) ⊕ ↥(pat.nextSites e S)
      ∀ {X Table : Type} [Fintype X] [Fintype Table] (pre : Frame X (Table ⊕ Geo))
        (p : PublicPopulation.Pins (Fin M) Table k w) (col : Columns Table M D w)
        (code : A ↪ Fin (2^k)) (seed : A ≃ Fin seeds) (perm : Fin D → Equiv.Perm A)
        (home : Fin V → Fin copies),
        seeds ≤ 2^w → siteCapacity e V seeds ≤ 2^w → edgeCapacity e M seeds ≤ 2^w →
        let route : Table → (Table ⊕ Geo) ⊕ Words A e.count w := Sum.inl ∘ Sum.inl
        ∃ f : Frame (X ⊕ Words A e.count w) ((Fin (edgeCapacity e M seeds) ⊕
            Raw Data (siteCapacity e V seeds) (edgeCapacity e M seeds) w w) ⊕ Unit),
          f.size ≤ pre.size + roundSourceCost (Fintype.card A) D M k w C E C' E' e.count
            (PublicPopulation.offsets (mapPins route p)).size (PublicPopulation.frame (mapPins route p) code).size +
            ((1+siteCapacity e V seeds)*G*(d+1)^H + (PublicEndpoints.Successor.cost e M seeds w+3*edgeCapacity e M seeds)) ∧
          ∀ (child : Fin copies → PlacedPack D P bits K (Cube D) prior)
            (slot : (raw child).layout.Edge ↪ Fin M) (bin : (raw child).layout.Edge → Option A)
            (pos : (raw child).layout.Edge → Bool)
            (g : Placement (m := m) (densePack (raw child) slot) (CutCircuit.denseBin (raw child).layout slot bin)
              perm (Cube D) (SurfaceHost (Cube D) (lev+1))),
            let s : Stage m B lev child := ⟨M,slot,bin,perm,pos,g⟩
            ∀ (old : (raw child).layout.Site ↪ Fin V) (dummy : Fin (edgeCapacity e M seeds) → SiteShape e s.input A)
              (x : X → Bool) (z : Words A e.count w → Bool),
              Ready e p col code seed (raw child) bin pos old slot dummy (pre.eval x ∘ Sum.inl) →
              let y := f.eval (Sum.elim x z)
              (y (.inr ()) = true ↔ Accepted e s.matched (fun a t j => z (a,t,j))) ∧
              ∀ (pub : PublicPlacement pat S s.input s.label s.perm lev s.placed),
                PlacementReads s.input s.label s.perm enum pat S home s.placed pub old seed.toEmbedding (pre.eval x ∘ Sum.inr) →
                ∀ (hist : s.Index e), (∀ a t, (hist a).val t = value (fun j => z (a,t,j))) →
                  (s.directory e old seed.toEmbedding dummy hist).dense.Reads (pat.nextSites e S)
                    (segmentField enum (pat.nextSites e S) hl) (y ∘ Sum.inl) := by
  obtain ⟨C,E,C',E',G,H,make⟩ := reconstruct_saved enum pat e S hm
  refine ⟨C,E,C',E',G,H,?_⟩
  intro B P instB bits d lev prior copies V M seeds k w hd hl A Geo Data X Table instX instTable pre
    p col code seed perm home hn hv he route
  let full := (Table ⊕ Geo) ⊕ Words A e.count w
  let geo : Frame full Geo := Frame.initial (Sum.inl ∘ Sum.inr)
  let word := fun (a : A) (t : Fin e.count) (j : Fin w) => (Sum.inr (a,t,j) : full)
  obtain ⟨check,hs,out⟩ := make d lev prior copies V M seeds k w hd hl (mapPins route p) (mapColumns route col)
    code seed perm word home geo hn hv he
  let f := check.subst (withWords pre)
  refine ⟨f,?_,?_⟩
  · simp only [f,Frame.subst_size,withWords_size]
    simp only [geo,Frame.initial_size,zero_add] at hs
    simpa only [Nat.add_assoc] using Nat.add_le_add_left hs pre.size
  intro child slot bin pos g s old dummy x z ready y
  let b : full → Bool := Sum.elim (pre.eval x) z
  have right : geo.eval b = pre.eval x ∘ Sum.inr := by funext j; simp [geo,b]
  have yread : y = check.eval b := by funext j; rw [show y j=f.eval (Sum.elim x z) j from rfl,Frame.subst_eval,withWords_eval]
  have rr := ready_map e route p col code seed (raw child) bin pos old slot dummy b ready
  obtain ⟨flag,next⟩ := out child slot bin pos g old dummy b rr
  rw [yread]
  refine ⟨flag,?_⟩
  intro pub hgeo hist vals
  rw [← right] at hgeo
  exact next pub hgeo hist vals

end Shortening.PublicDenseReceipt

end BorderVNP
end Computability
end OAI
