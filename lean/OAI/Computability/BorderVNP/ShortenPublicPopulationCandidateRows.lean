import OAI.Computability.BorderVNP.ShortenPublicPopulationNamed
import OAI.Computability.BorderVNP.ShortenPublicMovedBin

/-! # Stable rows for the candidate population of one physical pack

Every candidate reads the same active cable rows. Only the sampled motion
changes between candidates. The deck posttranslation in these histograms
is the identity, supplied by two shared Boolean literals in each row.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PackMotions Hecke ParseBatchSort
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

/-- Wires of the stable cable table belonging to one pack. -/
structure CandidatePins (T U σ : Type*) (q deep w : ℕ) where
  /-- Active charged segment. -/
  live : U → σ
  /-- Binary cable width. -/
  width : U → Fin w → σ
  /-- One-hot catalog type of the oriented segment. -/
  kind : U → T → σ
  /-- Product tile of the source endpoint. -/
  source : U → ProductSlots q deep → σ

variable {D q d n w copies : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    {U σ : Type*} (a : CandidatePins (↥B.types) U σ q (d+2*n+2*n) w)
    {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
    (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
    (L : PreparedBins.Labels B input active sites) (i : Fin copies)
    (slot : (input i).layout.Edge ↪ U) (x : σ → Bool)

/-- Occupied rows retain the original charge, width, type and source. -/
structure CandidateReads (hd : 1 ≤ d) : Prop where
  /-- The physical charge bit of a named old edge. -/
  live : ∀ e, x (a.live (slot e)) = active i e
  /-- Reserved names without edges are inactive. -/
  empty : ∀ u, u ∉ Set.range slot → x (a.live u) = false
  /-- Width words of the active old edges. -/
  widths : ∀ e, active i e → value (x ∘ a.width (slot e)) = (input i).layout.width e
  /-- The oriented catalog type assigned by the endpoint join. -/
  kinds : ∀ e (he : active i e), x ∘ a.kind (slot e) = fun t => decide (t=L.kind ⟨i,e,he⟩)
  /-- Tile of the source site in the deep cover. -/
  sources : ∀ e, active i e → x ∘ a.source (slot e) = productWires _ (fun j =>
    addressAt _ (by omega) ((sites i ((input i).layout.src e)) (enum j)))

private noncomputable def rowOperands [Fintype σ] (u : U) :
    Frame σ (↥B.types ⊕ (ProductSlots q (d+2*n) ⊕ ProductSlots q (d+2*n+2*n))) :=
  let literals : Frame σ Bool := (Frame.initial (id : σ → σ)).step fun b => .const b
  literals.withInput.select (Sum.elim (.inl ∘ a.kind u) (Sum.elim
    (.inr ∘ productWires _ (1 : Fin q → Deck (d+2*n))) (.inl ∘ a.source u)))

private theorem rowOperands_size [Fintype σ] (u : U) : (rowOperands B a u).size ≤ 2 := by
  have h := Frame.step_size_le (Frame.initial (id : σ → σ)) (fun b : Bool => .const b) 1
    (fun _ => le_rfl)
  simpa [rowOperands] using h

private theorem rowOperands_eval [Fintype σ] {hd : 1 ≤ d}
    (reads : CandidateReads B enum a input active sites L i slot x hd) (e) (he : active i e) :
    (rowOperands B a (slot e)).eval x = rowInput (L.kind ⟨i,e,he⟩) ((1 : Cube D → Deck (d+2*n)) ∘ enum)
      (fun j => addressAt _ (by omega) ((sites i ((input i).layout.src e)) (enum j))) := by
  funext v
  rcases v with v | (v | v)
  · simpa [rowOperands,rowInput] using congrFun (reads.kinds e he) v
  · simp only [rowOperands,Frame.select_eval,Sum.elim_inr,Sum.elim_inl,Function.comp_apply,
      Frame.withInput_eval_inr,Frame.step_eval,rowInput]
    rfl
  · simpa [rowOperands,rowInput] using congrFun (reads.sources e he) v

/-- Geometric tag of the old pack for a fixed candidate before any deck translation. -/
noncomputable def candidateTag (p : Equiv.Perm (Cube D))
    (word : ProductSample (lattice 1) elliptic (Cube D) n) :
    (input i).layout.Edge → Option ((Cube D → Deck (d+2*n)) × B.Bin) :=
  B.tag input active L.kind L.lift i (p,word,1)

set_option maxHeartbeats 1500000 in
/-- One candidate histogram with its literal integral widths. The emitted circuit depends
only on the stable physical table dimensions and pin names. -/
theorem candidateRow_frames (p : Equiv.Perm (Cube D))
    (word : ProductSample (lattice 1) elliptic (Cube D) n) :
    ∃ C k : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (w : ℕ) {U σ : Type*} [Fintype U] [Fintype σ]
      (a : CandidatePins (↥B.types) U σ q (d+2*n+2*n) w),
      ∃ f : Frame σ (((Cube D → Deck (d+2*n)) × B.Bin) × Fin w),
        (let v := Fintype.card U + Fintype.card (Cube D → Deck (d+2*n))*Fintype.card B.Bin
         let r := Nat.clog 2 (Fintype.card B.Bin)
         f.size ≤ 1 + Fintype.card U*(C*(d+1)^k) + (Fintype.card U*r*(2*Fintype.card B.Bin+1) +
           2*(v+1)*laneCost (Nat.clog 2 v) (r+keyWidth q (d+2*n)) w)) ∧
        ∀ {copies : ℕ} {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites) (i : Fin copies)
          (slot : (input i).layout.Edge ↪ U) (x : σ → Bool),
          CandidateReads B enum a input active sites L i slot x hd →
          let bin := candidateTag B input active sites L i p word
          (∀ b, SeedIntervals.count (input i).layout bin b < 2^w) → ∀ b,
            value (fun j => f.eval x (b,j)) = SeedIntervals.count (input i).layout bin b := by
  obtain ⟨C,k,rows⟩ := PublicMovedBin.activeMovedBin_frames B enum p word
  refine ⟨2+C,k,?_⟩
  intro d hd w U σ instU instσ a
  obtain ⟨g,hg,sem⟩ := rows d hd
  let row (u : U) := g.subst (rowOperands B a u)
  refine ⟨namedRows enum row (binCode B.Bin) a.live a.width, ?_, ?_⟩
  · have hsize := namedRows_size enum row (binCode B.Bin) a.live a.width
    have hrow (u : U) : (row u).size ≤ (2+C)*(d+1)^k := by
      have h1 : 1 ≤ (d+1)^k := Nat.one_le_pow _ _ (by omega)
      simp only [row, Frame.subst_size,Nat.add_mul]
      exact Nat.add_le_add ((rowOperands_size B a u).trans (Nat.le_mul_of_pos_right _ h1)) hg
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hrow u)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at sum
    exact hsize.trans (Nat.add_le_add_right (Nat.add_le_add_left sum 1) _)
  · intro copies P bits K input active sites L i slot x reads bin fits b
    have mask (e) : (bin e).isSome = active i e := sampledBin_mask _ _ _ _ _ _ _ _ _
    apply namedRows_count (input i).layout enum row (binCode B.Bin) a.live a.width bin slot x
      (fun e => (reads.live e).trans (mask e).symm) reads.empty _ _ fits b
    · intro e b hb
      have he : active i e := by rw [←mask e,hb]; rfl
      obtain ⟨z,hz,hval⟩ := sem input active sites L ⟨i,e,he⟩ 1
      have ez : z = b := Option.some.inj (hz.symm.trans hb)
      subst b
      funext j
      rw [show row (slot e) = g.subst (rowOperands B a (slot e)) from rfl,
        Frame.subst_eval,rowOperands_eval B enum a input active sites L i slot x reads e he,hval]
      cases j with
      | inl j => rfl
      | inr b =>
        by_cases h : b = z.2 <;> simp [PublicMovedBin.binWires,h]
    · intro e b hb
      apply reads.widths
      rw [←mask e,hb]
      rfl

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
