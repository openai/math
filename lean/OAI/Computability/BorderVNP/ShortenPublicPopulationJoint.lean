import OAI.Computability.BorderVNP.ShortenPublicPopulationInput

/-! # Whole-pack motions and the actual combined integer populations

At each cover level the single frame below handles any legal vector of
per-pack motion choices and shifts and any widths of the named old cables.
Its output is the true integral `jointBin` population used to allocate pools.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicPopulation

open Cover Cover.Frame Cover.AddressCircuit Epoch Crossing Packing PackMotions Hecke
open ParseBatchSort
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

variable {D q n d w copies : ℕ} {S : Finset (HyperbolicHost (Cube D))} {h η : ℝ}
    (B : PreparedBins D S h η) (enum : Fin q ≃ Cube D)
    {M U σ : Type*} [Fintype M] [DecidableEq M] [Fintype U] [Fintype σ]
    (perm : M → Equiv.Perm (Cube D)) (word : M → ProductSample (lattice 1) elliptic (Cube D) n)

variable {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
    (active : ∀ i, (input i).layout.Edge → Bool)
    (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
    (L : PreparedBins.Labels B input active sites)
    (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck (d+2*n))

/-- Tags of the disjoint-union network under the chosen whole-pack motions. -/
noncomputable def jointTags : (parallelPacks input).layout.Edge → Option ((Cube D → Deck (d+2*n)) × B.Bin) :=
  jointBin input (B.tag (d := d+2*n) input active L.kind L.lift)
    (fun i => (perm (pick i),word (pick i),shift i))

omit [Fintype M] [DecidableEq M] in
/-- The true joint tag is present precisely on a positive charged input cable. -/
theorem jointTags_mask (e : (parallelPacks input).layout.Edge) :
    (jointTags B perm word input active sites L pick shift e).isSome = active e.1 e.2 :=
  sampledBin_mask _ _ _ _ _ _ _ _ _

variable (a : JointPins (↥B.types) M U σ q (d+2*n) (d+2*n+2*n) w copies)

/-- A complete population circuit with the already constructed finite-motion row classifier. -/
noncomputable def jointFrame (f : Frame (M ⊕ (↥B.types ⊕
    (ProductSlots q (d+2*n) ⊕ ProductSlots q (d+2*n+2*n)))) (ProductSlots q (d+2*n) ⊕ B.Bin)) :
    Frame σ (((Cube D → Deck (d+2*n)) × B.Bin) × Fin w) :=
  namedRows (I := Cube D) (U := U) (B := B.Bin) (σ := σ) (q := q) (l := d+2*n)
    (r := Nat.clog 2 (Fintype.card B.Bin)) (w := w) enum (fun u => f.subst (Frame.initial (a.dispatch u))) (binCode B.Bin) a.live a.width

set_option maxHeartbeats 1500000 in
/-- Finite-motion dispatch and sparse accumulation give the exact moved
histogram, with one named row per old cable and one query per legal seed. -/
theorem joint_frames :
    ∃ C p : ℕ, ∀ (d : ℕ) (hd : 1 ≤ d) (w copies : ℕ) {U σ : Type*} [Fintype U] [Fintype σ]
      (a : JointPins (↥B.types) M U σ q (d+2*n) (d+2*n+2*n) w copies),
      ∃ f : Frame σ (((Cube D → Deck (d+2*n)) × B.Bin) × Fin w),
        (let v := Fintype.card U + Fintype.card (Cube D → Deck (d+2*n))*Fintype.card B.Bin
         let r := Nat.clog 2 (Fintype.card B.Bin)
         f.size ≤ 1 + Fintype.card U*(C*(d+1)^p) + (Fintype.card U*r*(2*Fintype.card B.Bin+1) +
           2*(v+1)*laneCost (Nat.clog 2 v) (r+keyWidth q (d+2*n)) w)) ∧
        ∀ {P : Type} {bits : P → ℕ} {K : Type*} (input : Fin copies → Pack D P bits K)
          (active : ∀ i, (input i).layout.Edge → Bool)
          (sites : ∀ i, (input i).layout.Site → SurfaceHost (Cube D) (d+2*n+2*n))
          (L : PreparedBins.Labels B input active sites) (slot : (parallelPacks input).layout.Edge ↪ U)
          (pick : Fin copies → M) (shift : Fin copies → Cube D → Deck (d+2*n)) (x : σ → Bool),
          JointReads B enum a input active sites L slot pick shift x hd →
          let bin := jointTags B perm word input active sites L pick shift
          (∀ b, SeedIntervals.count (parallelPacks input).layout bin b < 2^w) → ∀ b,
            value (fun j => f.eval x (b,j)) = SeedIntervals.count (parallelPacks input).layout bin b := by
  obtain ⟨C,p,rows⟩ := PublicMovedBin.activeMotionBin_frames B enum perm word
  refine ⟨C,p,?_⟩
  intro d hd w copies U σ instU instσ a
  obtain ⟨g,hg,sem⟩ := rows d hd
  let row (u : U) : Frame σ (ProductSlots q (d+2*n) ⊕ B.Bin) := g.subst (Frame.initial (a.dispatch u))
  refine ⟨jointFrame B enum a g, ?_, ?_⟩
  · have bound := namedRows_size (l := d+2*n) (q := q) (B := B.Bin) enum row (binCode B.Bin) a.live a.width
    have each (u : U) : (row u).size ≤ C*(d+1)^p := by simpa [row] using hg
    have sum := Finset.sum_le_sum (s := Finset.univ) (fun u _ => each u)
    simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] at sum
    exact bound.trans (Nat.add_le_add_right (Nat.add_le_add_left sum 1) _)
  · intro P bits K input active sites L slot pick shift x reads bin fits b
    let N := (parallelPacks input).layout
    have mask (e : N.Edge) : (bin e).isSome = active e.1 e.2 :=
      jointTags_mask B perm word input active sites L pick shift e
    refine namedRows_count (l := d+2*n) (q := q) (B := B.Bin) N enum row (binCode B.Bin) a.live a.width bin slot x
      (fun e => (reads.live e).trans (mask e).symm) reads.empty ?_ ?_ fits b
    · intro e c hc
      let z : Active input active := ⟨e.1,e.2,by rw [←mask e,hc]; rfl⟩
      obtain ⟨v,hv,he⟩ := sem input active sites L z (pick z.1) (shift z.1)
      have ec : v = c := Option.some.inj (hv.symm.trans hc)
      subst c
      have source : (Frame.initial (a.dispatch (slot e))).eval x = x ∘ a.dispatch (slot e) :=
        funext (Frame.initial_eval _ _)
      have selected := reads.dispatch_value B enum a input active sites L slot pick shift x z
      change x ∘ a.dispatch (slot e) = _ at selected
      funext j
      rw [show row (slot e) = g.subst (Frame.initial (a.dispatch (slot e))) from rfl,
        Frame.subst_eval,source,selected]
      apply (congrFun he j).trans
      rcases j with j | b
      · rfl
      · by_cases equal : b = v.2 <;> simp [PublicMovedBin.binWires,equal]
    · intro e c hc
      exact reads.widths ⟨e.1,e.2,by rw [← mask e,hc]; rfl⟩

end Shortening.PublicPopulation

end BorderVNP
end Computability
end OAI
