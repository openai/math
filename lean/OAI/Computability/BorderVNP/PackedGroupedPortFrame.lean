import OAI.Computability.BorderVNP.PackedNamedPortHeaders
import OAI.Computability.BorderVNP.PackedHistorySeedPlan
import OAI.Computability.BorderVNP.PackedFrozenHistoryCapacity

/-! # The literal bit frame of the grouped exterior-port header

The two static words of each argument slot share the same two Boolean
constant gates. The wire count depends on the number of grouped tile
arguments, even when a group holds many private block copies.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing Cover Epoch Epoch.Round Shortening Shortening.Adaptive PackedHistoryCircuit.Normalized
open PackedHistoryCircuit.Normalized.SelectedSchedule PackedHistoryCircuit.Normalized.EnrichedOuter
open Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical BorderVNP.Epoch.Cube

variable {np w D : ℕ} {σ : Type*} [Fintype σ] (p : Ports np)

/-- Two fixed public word columns, selected from the common pair of constants. -/
noncomputable def Ports.frame (p : Ports np) (w : ℕ) (σ : Type*) [Fintype σ] :
    Frame σ (Fin np × Bool × Fin w) :=
  (constants σ).select fun z => constPins w (if z.2.1 then p.width z.1 else p.host z.1) z.2.2

/-- The whole rectangular port header shares two Boolean gates. -/
theorem Ports.frame_size : (p.frame w σ).size ≤ 2 := by
  rw [Ports.frame,Frame.select_size]
  exact constants_size σ

/-- Every fitted literal word evaluates to its designated natural number. -/
theorem Ports.frame_word (x : σ → Bool) (i : Fin np) (size : Bool)
    (fits : (if size then p.width i else p.host i) < 2^w) :
    value (fun j => (p.frame w σ).eval x (i,size,j)) = (if size then p.width i else p.host i) := by
  simp only [Ports.frame,Frame.select_eval]
  exact constPins_value x w _ fits

variable {P : Type} {bits : P → ℕ} (N : Network D P bits) {V : ℕ}
    (sites : N.Site ↪ Fin V) (id : P ↪ Fin np) (reads : p.Reads N sites id)
    (vf : V ≤ 2^w) (wf : ∀ i, p.width i < 2^w) (x : σ → Bool)

include reads vf wf in
/-- The executable bit frame represents the true occupied physical rows and
zero width at each unused argument slot. -/
theorem Ports.frame_reads :
    (∀ a, value (fun j => (p.frame w σ).eval x (id a,false,j)) = (sites (N.attach a)).val) ∧
    (∀ a, value (fun j => (p.frame w σ).eval x (id a,true,j)) = bits a) ∧
    ∀ i ∉ Set.range id, value (fun j => (p.frame w σ).eval x (i,true,j)) = 0 := by
  refine ⟨fun a => ?_,fun a => (p.frame_word x (id a) true (wf _)).trans (reads.size a),
    fun i hi => (p.frame_word x i true (wf i)).trans (reads.hole i hi)⟩
  have fit : p.host (id a) < 2^w := (reads.attach a) ▸ (sites (N.attach a)).isLt.trans_le vf
  exact (p.frame_word x (id a) false fit).trans (reads.attach a)

/-- Tile-indexed exterior bank of the physical grouped grid. -/
def grouped (tiles extent : ℕ) : Ports tiles := ⟨Fin.val,fun _ => extent⟩

/-- Every base row is occupied by its own tile argument. -/
theorem grouped_widths (tiles extent : ℕ) (fit : extent < 2^w) :
    (PortTable.mk tiles (Function.Embedding.refl _) (grouped tiles extent)).Widths (fun _ => extent) w :=
  ⟨fun _ => rfl,fun i hi => (hi ⟨i,rfl⟩).elim,fun _ => fit⟩

variable {m : ℕ} [NeZero D] {K : Type} [Field K] {e : PaidIdentity K D m} (S : PackedHistoryCircuit.Normalized.SiteSchedule e)
    {n r d copies T headerFactor Q : ℕ} (plan : SeedPlan S n r d T copies headerFactor Q)
local notation "axes" => Fintype.card (Cube D)
local notation "tileN" => GridHosts.tileCount axes d
local notation "extent" => copies*GridHosts.inputBlockWidth r n axes d
local notation "word" => 60*TeamScales.logWidth r n

include plan in
/-- The accepted seed plan pays the actual grouped argument width. -/
theorem seed_widths :
    (PortTable.mk tileN (Function.Embedding.refl _) (grouped tileN extent)).Widths (fun _ => extent) word :=
  grouped_widths tileN extent ((Nat.mul_le_mul_left copies (DeckGrid.seed_capacity_le n r axes d).1).trans_lt plan.small)

/-- Every wire in the two-word frame is indexed by a grouped port slot and
one word bit. At every intermediate stage these slots fit its site rectangle. -/
theorem grouped_frame_card (t j : ℕ) :
    let rows := Parallel.nestedCapacity S.fanIn (portCapacity S (GridHosts.tileCount axes d) t) j
    Fintype.card (Fin rows × Bool × Fin w) = 2*rows*w ∧ rows ≤ (before S (d+1) t j).sites := by
  intro rows
  constructor
  · simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool]; ac_rfl
  · have size : GridHosts.tileCount axes d = CoverScale.sites (Cube D) (d+1) := by
      simp only [GridHosts.tileCount,CoverScale.sites,Fintype.card_fun,Fintype.card_fin]
    rw [show rows = S.fanIn^j*((fan S)^t*GridHosts.tileCount axes d) from path_count S t j,size]
    exact (FrozenTape.ports_fit S (d+1)).2 t j

/-- The published selector ranges bound the site pointer at every attained
intermediate stage, including the last dense save. -/
theorem path_sites_fit {r n start t : ℕ} {den cut : Fin S.rounds → ℕ}
    (ranges : ∀ i : Fin S.rounds, Ranges S r n start t i (den i) (cut i))
    (j : ℕ) (hj : j ≤ S.rounds) : (before S start t j).sites ≤ 2^(60*TeamScales.logWidth r n) := by
  by_cases hi : j < S.rounds
  · exact (Nat.le_mul_of_pos_left _ S.positiveFanIn).trans ((ranges ⟨j,hi⟩).words.2.2.2.1)
  · obtain rfl : j = S.rounds := by omega
    exact (boundary_fits (S := S) ranges).2

open TeamContraction EnrichedOuter.Boundary

variable {R time pins link inner : ℕ} {Edge : Type} (G : Wiring R r time pins link inner n Edge)


/-- The real physical seed uses its own tile ordinal for every grouped
attachment, for every installed private table and initializer assignment. -/
theorem seed_header_reads
    (order : Fin (GridHosts.tileCount (Fintype.card (Cube D)) d) ≃ (Fin (Fintype.card (Cube D)) → Deck (d+2)))
    (position : (Fin (Fintype.card (Cube D)) → Deck (d+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (table : (DeckGrid.seedBundle G (Fintype.card (Cube D)) d order position copies).Tables K)
    (words : Boundary.Pins S (d+1) (boundary S (d+1)) (60*TeamScales.logWidth r n) 0 → Bool) :
    let a := seedState S G d order position copies table words
    (grouped tileN extent).Reads a.pack.layout a.rows.site (Function.Embedding.refl _) := by
  intro a
  exact ⟨fun z => ((seedState_rows S G d order position copies table words).1 z).symm,
    fun _ => rfl,fun i hi => (hi ⟨i,rfl⟩).elim⟩

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
