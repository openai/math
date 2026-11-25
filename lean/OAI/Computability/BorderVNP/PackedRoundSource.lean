import OAI.Computability.BorderVNP.PackedRoundProfiles
import OAI.Computability.BorderVNP.ShortenPublicRelativeSerializer
import OAI.Computability.BorderVNP.ParseBatchVerifierConjunction

/-! # Checked cable fields for the geometric successor

This is the public round after the motion and old endpoint lookups. A single table supplies
the clipped intervals, inverse seed IDs, actual block counts and public profile multiplicities.
The final bit checks every seed's histogram. Each accepting guess tuple corresponds to the
same physical branch used by the next placement and tensor sum.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DirectoryCircuit

open Crossing Shortening Shortening.SeedIntervals Shortening.StaticRows Shortening.CombiningStep
open Shortening.PublicEndpoints.Successor Shortening.PublicRelative
open VPVNP.VerifierNetwork ParseBatchSort ParseBatchVerifier BankCircuit
open BinPackingGames.Foundations.Complexity.CookLevin
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
variable {A : Type} [Fintype A] {σ : Type*} [Fintype σ]
variable {M nSites nSeeds k w : ℕ} (p : PublicPopulation.Pins (Fin M) σ k w)
variable (col : Columns σ M D w) (code : A ↪ Fin (2^k)) (seed : A ≃ Fin nSeeds)
variable {P : Type*} {bits : P → ℕ} (pack : Pack D P bits K)
variable (bin : pack.layout.Edge → Option A) (positive : pack.layout.Edge → Bool)
variable (oldSite : pack.layout.Site ↪ Fin nSites) (slot : pack.layout.Edge ↪ Fin M)
variable (dummy : Fin (edgeCapacity e M nSeeds) → SiteShape e (densePack pack slot) A)

omit [Fintype σ] in
/-- Meaning of the old endpoint pins and moved bin rows. These data precede the cut pass.
The capacity is for the actual populations, uniformly across every possible next profile. -/
structure Ready (x : σ → Bool) : Prop where
  /-- Live charged rows and their decoded bin addresses. -/
  population : PublicPopulation.Represents p pack.layout bin slot code x
  /-- Fixed-multiplier population bound, covering the largest paid template cable. -/
  room : ∀ a, widthMultiplier e * count pack.layout bin a < 2^w
  /-- Old widths are available on uncharged cables too. -/
  widths : ∀ c, value (x ∘ p.width (slot c)) = pack.layout.width c
  /-- Stable occupied flags from the prior directory. -/
  occupied : ∀ u, x (col.occupied u) = true ↔ u ∈ Set.range slot
  /-- The same orientation as the chosen geometric labeling. -/
  orientation : ∀ c, x (col.positive (slot c)) = positive c
  /-- Both old endpoint pointers. -/
  endpoints : ∀ c, value (x ∘ col.endpoint (slot c) true) = (oldSite (pack.layout.src c)).val ∧
    value (x ∘ col.endpoint (slot c) false) = (oldSite (pack.layout.dst c)).val
  /-- Padding pointers are only read for unused virtual output slots. -/
  padding : ∀ r, value (x ∘ col.padding r) = (siteRows e (densePack pack slot) oldSite seed.toEmbedding
    (dummy (Names.rowSlot (bandCandidate e nSeeds r.2.2 r.1 r.2.1)))).val

private noncomputable def allChecks (A : Type*) [Fintype A] : Frame A Unit :=
  (Frame.initial id).step (fun _ => every (fun i => .input ((Fintype.equivFin A).symm i)))

private theorem allChecks_eval (x : A → Bool) : (allChecks A).eval x () = true ↔ ∀ a, x a = true := by
  have h : (Frame.initial (id : A → A)).eval x = x := funext (Frame.initial_eval id x)
  rw [allChecks,Frame.step_eval,h,every_eval]
  constructor
  · intro hx a
    exact ((Fintype.equivFin A).symm_apply_apply a) ▸ hx ((Fintype.equivFin A) a)
  · intro hx i
    exact hx _

private theorem allChecks_size (A : Type*) [Fintype A] : (allChecks A).size ≤ 2*Fintype.card A+1 := by
  have h := every_size (fun i => (StatementCircuit.Expr.input ((Fintype.equivFin A).symm i) : Expr A)) 1 (fun _ => le_rfl)
  simpa [allChecks] using Frame.step_size_le (Frame.initial (id : A → A))
    (fun _ : Unit => every (fun i => .input ((Fintype.equivFin A).symm i))) _ (fun _ => h)

/-- Gate bound of the old directory, the independently computed matched size and the profile
tests, all charged by sparse rows and legal seed bins. -/
def roundSourceCost (A D M k w C E C' E' terms offsetCost countCost : ℕ) : ℕ :=
  offsetCost + PoolCircuit.scatterCost A M D C E k w + M*Fintype.card (Band D)*(48*w) +
    1 + M*Fintype.card (Band D)*(3300*(w+1)^2) +
    (1+D*(2*(A+M+1)*PublicPopulation.laneCost (Nat.clog 2 (A+M)) k w)) +
    (countCost+2+A*(C'*(w+1)^E')) + (1+A*guardBudget terms w) + (2*A+1)

/-- The complete cable-field source required by the geometric successor, with one validity
bit. All profiles are guessed as ordinary fixed-width words; every valid geometric summand
has exactly one such bit tuple by `BankCircuit.branches`. -/
theorem checked_fields (hm : 0 < m) :
    ∃ C E C' E' : ℕ, ∀ (nSites M nSeeds k w : ℕ) {A : Type} {σ : Type*} [Fintype A] [Fintype σ]
      (p : PublicPopulation.Pins (Fin M) σ k w) (col : Columns σ M D w) (code : A ↪ Fin (2^k))
      (seed : A ≃ Fin nSeeds) (perm : Fin D → Equiv.Perm A) (guess : A → Fin e.count → Fin w → σ),
      nSeeds ≤ 2^w → ∃ f : Frame σ (CableFields e A M w ⊕ Unit),
        f.size ≤ roundSourceCost (Fintype.card A) D M k w C E C' E' e.count
          (PublicPopulation.offsets p).size (PublicPopulation.frame p code).size ∧
        ∀ {P : Type*} {bits : P → ℕ} (pack : Pack D P bits K) (bin : pack.layout.Edge → Option A)
          (positive : pack.layout.Edge → Bool) (oldSite : pack.layout.Site ↪ Fin nSites)
          (slot : pack.layout.Edge ↪ Fin M) (x : σ → Bool)
          (dummy : Fin (edgeCapacity e M nSeeds) → SiteShape e (densePack pack slot) A),
          Ready e p col code seed pack bin positive oldSite slot dummy x →
          let L := densePack pack slot
          let label := CutCircuit.denseBin pack.layout slot bin
          let j := blocks L.layout label perm m
          let words := fun a t i => x (guess a t i)
          let orient := positive ∘ (Names.denseSlot pack.layout slot).symm
          (f.eval x (.inr ()) = true ↔ Accepted e j words) ∧
          ∀ (first : Fin D × Bool) (q : Counts e L label perm),
            (∀ a t, (q a).val t = value (words a t)) → ∀ {B : Type*}
              (sites : Fin (siteCapacity e nSites nSeeds) × B → Bool),
            SourceData e L label perm orient oldSite (CutCircuit.denseRows pack.layout slot)
              seed dummy first q (Sum.elim sites (f.eval x ∘ Sum.inl)) := by
  obtain ⟨C,E,old⟩ := old_directory_frames e hm
  obtain ⟨C',E',hist⟩ := histogram_frames e hm
  refine ⟨C,E,C',E',fun nSites M nSeeds k w A σ _ _ p col code seed perm guess hn => ?_⟩
  obtain ⟨d,hd,ed⟩ := old nSites M nSeeds k w p col code seed perm hn
  obtain ⟨h,hh,eh⟩ := hist M k w p code perm guess
  let rows := parallelFrame d h
  let fields : Frame (CableFields e A M w) (A × Option (Fin e.count) × Fin w) := Frame.initial Sum.inr
  obtain ⟨test,ht,et⟩ := exists_checks e w fields
  let flag := (allChecks A).subst test
  let result := flag.withInput.subst rows
  refine ⟨result,?_,?_⟩
  · simp only [result,Frame.subst_size,Frame.withInput_size,rows,parallelFrame_size,flag]
    have hflag := allChecks_size A
    simp only [fields,Frame.initial_size,zero_add] at ht
    dsimp only [roundSourceCost]
    omega
  · intro P bits pack bin positive oldSite slot x dummy hx L label j words orient
    have hpos : 1 ≤ widthMultiplier e := Nat.le_add_right _ _
    have fit (a : A) : count pack.layout bin a < 2^w :=
      (Nat.le_mul_of_pos_left _ hpos).trans_lt (hx.room a)
    have hdir := ed pack bin positive oldSite slot x dummy hx.population fit hx.widths
      hx.occupied hx.orientation hx.endpoints hx.padding
    obtain ⟨hj,hg⟩ := eh pack.layout bin slot x hx.population fit
    have hsource (i : CableFields e A M w) : result.eval x (.inl i) = rows.eval x i := by
      simp only [result,Frame.subst_eval,Frame.withInput_eval_inl]
    have hcheck : result.eval x (.inr ()) = true ↔ ∀ a, test.eval (rows.eval x) a = true := by
      rw [show result.eval x (.inr ()) = (allChecks A).eval (test.eval (rows.eval x)) () by
        simp [result,flag,Frame.subst_eval],allChecks_eval]
    have hraw : fields.eval (rows.eval x) = h.eval x := by
      funext i
      simp [fields,rows]
    constructor
    · rw [hcheck,et,hraw]
      simp only [hj,hg,j,L,label,words,densePack]
    · intro first q hq B sites
      constructor
      · intro r
        have hleft : (fun t => Sum.elim sites (result.eval x ∘ Sum.inl) (.inr (.inl (r,.inl t)))) =
            fun t => d.eval x (r,.inl t) := by
          funext t
          simp only [Sum.elim_inr,Function.comp_apply,hsource,rows,parallelFrame_eval_inl]
        have hright : (fun t => value (fun z => Sum.elim sites (result.eval x ∘ Sum.inl)
            (.inr (.inl (r,.inr (t,z)))))) = fun t => value (fun z => d.eval x (r,.inr (t,z))) := by
          funext t
          simp only [Sum.elim_inr,Function.comp_apply,hsource,rows,parallelFrame_eval_inl]
        rw [hleft,hright]
        exact hdir r
      · intro a t
        simp only [Sum.elim_inr,Function.comp_apply,hsource,rows,parallelFrame_eval_inr]
        cases t with
        | none => exact hj a
        | some t => simpa only [hg,words,Option.elim_some] using (hq a t).symm
      · apply physical_width_fits e L label perm orient first q oldSite _ seed.toEmbedding
        intro a
        exact (Nat.mul_le_mul_left _ (CutCircuit.dense_count pack.layout slot bin a).le).trans_lt (hx.room a)

end Packing.DirectoryCircuit

end BorderVNP
end Computability
end OAI
