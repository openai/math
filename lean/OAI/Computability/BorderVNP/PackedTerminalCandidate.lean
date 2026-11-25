import OAI.Computability.BorderVNP.PackedHistoryDenseReady
import OAI.Computability.BorderVNP.PackedHistoryRouteRows
import OAI.Computability.BorderVNP.PackedTerminalMoveFrame
import OAI.Computability.BorderVNP.PackedTerminalSiteFrame

/-!
# Stable route rows for a candidate terminal motion

One parallel bank moves the physical sites. A sparse join retrieves the two
moved addresses at every cable. The resulting tests determine its new charge
and canonical move. Site numbers, port attachments, widths and occupied
zero-width cables continue to have their original public names.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Terminal

open Cover Cover.AddressCircuit Shortening Epoch Catalog PublicRelative PublicSegments PublicEndpoints Crossing
open VPVNP.VerifierNetwork (Frame)
open scoped Classical

/-- Terminal input columns in the public history circuit's ordinary wire order. -/
abbrev Input (Data : Type*) (V E w : ℕ) := Fin E ⊕ Raw Data V E w w

variable {D q lev V E w a : ℕ} {Data P : Type} [Fintype Data] {R : Type*} {bits : P → ℕ}
  (enum : Fin q ≃ Cube D) (S : Finset (HyperbolicHost (Cube D)))

/-- The relative tag and product address are read from the shared geometry column. -/
private def fromField {l : ℕ} (hl : lev+1=l) :
    ↥S ⊕ ProductSlots q l → FieldBit (↥S) (Cube D) (lev+1) :=
  Sum.elim Sum.inl (fun j => .inr (enum j.1, cast (congrArg (fun n => StackFrame.Slots (width n)) hl.symm) j.2))

private theorem fromField_projection {l : ℕ} (hl : lev+1=l) (u : HyperbolicHost (Cube D))
    (h : relative lev (productProjection (lev+1) u) ∈ S) :
    siteBits (productProjection (lev+1) u) h ∘ fromField enum S hl = liftRow enum S l u h := by
  subst l
  funext j
  cases j <;> rfl

private theorem projection_cast {I : Type} {n l : ℕ} (h : n=l) (u : HyperbolicHost I) :
    levelCast h (productProjection n u) = productProjection l u := by cases h; rfl

variable {d : ℕ} (hl : lev+1=d+2+2*a)
  (field : FieldBit (↥S) (Cube D) (lev+1) → Data) {g : Cube D → Cover.Frame.SL}
  (hg : ∀ i, Cover.Frame.Clears (g i) a)

/-- The moved quotient address used by the terminal width objective. -/
noncomputable def addressAfter (v : SurfaceHost (Cube D) (lev+1)) : Cube D → Deck (d+2) :=
  productAddress (d+1) (productMotion (d+2) (Equiv.refl _) hg (levelCast hl v))

variable {p : PlacedPack D P bits R (Cube D) lev} (dir : Normalized.Directory p V E)

/-- Exact low coordinates on each occupied site in its original row. -/
theorem movedSiteBank (one : Frame (↥S ⊕ ProductSlots q (d+2+2*a)) (ProductSlots q (d+2)))
    (ho : MovesSite enum S (g := g) (d+2) one) :
    ∃ f : Frame (Input Data V E w) (Fin V × ProductSlots q (d+2)), f.size ≤ 1+V*one.size ∧
      ∀ {P : Type} {R : Type*} {bits : P → ℕ} {p : PlacedPack D P bits R (Cube D) lev}
        (dir : Normalized.Directory p V E) (x : Input Data V E w → Bool), dir.Reads S field x →
        ∀ v j, f.eval x (dir.sites v,j) = productWires (d+2) (addressAfter hl hg (p.site v) ∘ enum) j := by
  let pin (i : Fin V) j : Input Data V E w := .inr (.inr (.inl (i,field (fromField enum S hl j))))
  let lane i := one.subst (Frame.initial (pin i))
  obtain ⟨bank,hb,he⟩ := exists_parallelFrames (out := fun _ : Fin V => ProductSlots q (d+2)) lane
  refine ⟨bank.select (fun j => ⟨j.1,j.2⟩),?_,?_⟩
  · simpa [lane] using hb
  · intro P R bits p dir x h v j
    obtain ⟨u,hu⟩ := Framed.exists_site_lift (lev+1) (p.site v)
    have hc := h.geometry.valid v
    rw [← hu] at hc
    have hr : (Frame.initial (pin (dir.sites v))).eval x = liftRow enum S (d+2+2*a) u hc := by
      rw [← fromField_projection enum S hl u hc]
      funext t
      rw [Frame.initial_eval]
      change x (.inr (.inr (.inl (dir.sites v,field (fromField enum S hl t))))) = _
      have hz := h.geometry.payload v (fromField enum S hl t)
      simpa only [Function.comp_apply,← hu] using hz
    rw [Frame.select_eval,he,show lane (dir.sites v) = one.subst (Frame.initial (pin (dir.sites v))) from rfl,
      Frame.subst_eval,hr,ho u hc]
    rw [addressAfter,← hu,projection_cast]; rfl

/-- Exact wires of a full candidate, prior to the global comparison of scores. -/
structure CandidateRows (L : ℝ) (y : RouteRows.Pins (allowedMoves (Cube D) L) q (d+2) V E w → Bool) : Prop where
  /-- The same stored addresses and widths, including holes. -/
  names : PublicEndpoints.Represents p.pack.layout dir.sites dir.cables dir.dummy (fun j => y (.inr (.inr j)))
  /-- Candidate tile coordinates at every physical vertex. -/
  origins : ∀ v j, y (.inr (.inr (.inl (dir.sites v,j)))) =
    productWires (d+2) (addressAfter hl hg (p.site v) ∘ enum) j
  /-- Stable occupancy of all physical cable names. -/
  present : ∀ i, y (.inl (i,.inl ())) = true ↔ i ∈ Set.range dir.cables
  /-- Charge mask after the endpoint test. -/
  active : ∀ e, y (.inr (.inl (dir.cables e))) = (p.charged e && decide
    (addressAfter hl hg (p.site (p.pack.layout.src e)) ≠ addressAfter hl hg (p.site (p.pack.layout.dst e))))
  /-- Padding is never charged. -/
  hole : ∀ i, i ∉ Set.range dir.cables → y (.inr (.inl i)) = false
  /-- Move selection agrees with the exact product group equality and fixed list order. -/
  moves : ∀ e t, let src := addressAfter hl hg (p.site (p.pack.layout.src e))
                 let dst := addressAfter hl hg (p.site (p.pack.layout.dst e))
                 y (.inl (dir.cables e,.inr t)) = true ↔
                   dst = src * reduceMove (d+1) t.val ∧
                     ∀ j ∈ SiteRoutes.alignedIndices L (d+1) src dst, Fintype.equivFin _ t ≤ j

set_option maxHeartbeats 1800000 in
/-- One sparse join of the candidate's moved site coordinates handles all
endpoint queries. Its two remaining gate terms are one site frame per site
and one move test per cable. -/
theorem candidate_frames (L : ℝ) (fit : V ≤ 2^w)
    (one : Frame (↥S ⊕ ProductSlots q (d+2+2*a)) (ProductSlots q (d+2)))
    (ho : MovesSite enum S (g := g) (d+2) one)
    (move : Frame (CableIn q (d+2)) (Unit ⊕ ↥(allowedMoves (Cube D) L)))
    (hm : MoveSemantics enum L (d+1) move) :
    ∃ f : Frame (Input Data V E w) (RouteRows.Pins (allowedMoves (Cube D) L) q (d+2) V E w),
      f.size ≤ (1+V*one.size) + 300*(V+2*E+1)*(Nat.clog 2 (V+2*E)+w+Fintype.card (ProductSlots q (d+2))+1)^3 +
        (1+E*move.size) ∧
      ∀ {P : Type} {R : Type*} {bits : P → ℕ} {p : PlacedPack D P bits R (Cube D) lev}
        (dir : Normalized.Directory p V E) (x : Input Data V E w → Bool), dir.Reads S field x →
        CandidateRows enum hl hg dir L (f.eval x) := by
  let T := ProductSlots q (d+2)
  let X := Input Data V E w
  obtain ⟨sites,hsites,horigin⟩ := movedSiteBank (V := V) (E := E) (w := w) enum S hl field hg one ho
  let old := Frame.initial (fun j : Fin E × (Fin w ⊕ Bool × Fin w) => (.inr (.inr (.inr j)) : X))
  let place := parallelFrame sites old
  let join := PublicEndpoints.join T w fit (cables := E)
  let both := (join.subst place).withInput
  let Aug := X ⊕ PublicEndpoints.Outputs T V E w w
  let read (e : Fin E) : CableIn q (d+2) → Aug :=
    Sum.elim (fun _ => .inl (.inr (.inl e))) (fun j => .inr (.inr ((e,j.1),j.2)))
  let lane (i : Fin E) := move.subst (Frame.initial (read i))
  obtain ⟨bank,hbank,heval⟩ := exists_parallelFrames (out := fun _ : Fin E => Unit ⊕ ↥(allowedMoves (Cube D) L)) lane
  let pin : RouteRows.Pins (allowedMoves (Cube D) L) q (d+2) V E w → Aug ⊕ (Σ _ : Fin E, Unit ⊕ ↥(allowedMoves (Cube D) L)) :=
    Sum.elim (fun j => j.2.elim (fun _ => .inl (.inl (.inl j.1))) (fun t => .inr ⟨j.1,.inr t⟩))
      (Sum.elim (fun e => .inr ⟨e,.inl ()⟩) (fun j => .inl (.inr (.inl j))))
  let f := (bank.withInput.subst both).select pin
  refine ⟨f,?_,?_⟩
  · have hj := PublicEndpoints.join_size (cables := E) T w fit
    have hb : bank.size ≤ 1+E*move.size := by simpa [lane] using hbank
    have htotal : f.size = (sites.size+join.size)+bank.size := by
      change (bank.withInput.subst both).size = _
      rw [Frame.subst_size]
      change (join.subst place).size+bank.size = _
      rw [Frame.subst_size]
      change (parallelFrame sites old).size+join.size+bank.size = _
      rw [parallelFrame_size,show old.size = 0 from rfl,add_zero]
    rw [htotal]
    exact Nat.add_le_add (Nat.add_le_add hsites hj) hb
  · intro P R bits p dir x hx
    have names : Represents p.pack.layout dir.sites dir.cables dir.dummy (place.eval x) := by
      constructor
      · intro i side
        simpa [address,place,old] using hx.geometry.names.addresses i side
      · intro i
        simpa [place,old] using hx.geometry.names.widths i
    have copied (j : PublicEndpoints.Inputs T V E w w) : f.eval x (.inr (.inr j)) = place.eval x j := by
      simp only [f,pin,Frame.select_eval,Sum.elim_inr,Frame.subst_eval,Frame.withInput_eval_inl]
      change (join.subst place).withInput.eval x (.inr (.inl j)) = _
      rw [Frame.withInput_eval_inr,Frame.subst_eval]
      exact join_input fit _ _
    have org (v : p.pack.layout.Site) (j : T) : place.eval x (.inl (dir.sites v,j)) =
        productWires (d+2) (addressAfter hl hg (p.site v) ∘ enum) j := by
      rw [show place = parallelFrame sites old from rfl,parallelFrame_eval_inl]
      exact horigin dir x hx v j
    have present (i : Fin E) : f.eval x (.inl (i,.inl ())) = x (.inl i) := by
      simp only [f,pin,Frame.select_eval,Sum.elim_inl,Frame.subst_eval,Frame.withInput_eval_inl]
      exact Frame.withInput_eval_inl _ _ _
    have test (i : Fin E) (j : Unit ⊕ ↥(allowedMoves (Cube D) L)) :
        f.eval x (j.elim (fun _ => .inr (.inl i)) (fun t => .inl (i,.inr t))) =
          move.eval ((Frame.initial (read i)).eval (both.eval x)) j := by
      cases j with
      | inl u => cases u; simp [f,pin,Frame.subst_eval,heval,lane]
      | inr t => simp [f,pin,Frame.subst_eval,heval,lane]
    have read_pair (i : Fin E) (v u : p.pack.layout.Site) (z : ℕ)
        (hj : JoinedRow fit (place.eval x) i (dir.sites v) (dir.sites u) z) :
        (Frame.initial (read i)).eval (both.eval x) = cableInput (x (.inr (.inl i)))
          (addressAfter hl hg (p.site v) ∘ enum) (addressAfter hl hg (p.site u) ∘ enum) := by
      funext j
      rcases j with t | ⟨b,j⟩
      · simp [read,both,cableInput]
      · cases b
        · simp only [Frame.initial_eval,read,Sum.elim_inr,both,Frame.withInput_eval_inr,Frame.subst_eval]
          exact (hj.2.1 j).trans (org u j)
        · simp only [Frame.initial_eval,read,Sum.elim_inr,both,Frame.withInput_eval_inr,Frame.subst_eval]
          exact (hj.1 j).trans (org v j)
    have pair (e : p.pack.layout.Edge) := read_pair (dir.cables e) (p.pack.layout.src e) (p.pack.layout.dst e)
      (p.pack.layout.width e) (join_occupied p.pack.layout dir.sites dir.cables dir.dummy fit names e)
    refine ⟨?_,fun v j => (copied _).trans (org v j),fun i => (present i).symm ▸ hx.present i,?_,?_,?_⟩
    · have h := funext copied
      exact h.symm ▸ names
    · intro e
      apply (test (dir.cables e) (.inl ())).trans
      rw [pair,hm.charge]
      exact congrArg (fun b => b && _) (hx.geometry.charge e)
    · intro i hi
      let v := dir.dummy (Packing.Names.rowSlot i)
      have h := read_pair i v v 0 (join_unused p.pack.layout dir.sites dir.cables dir.dummy fit names i hi)
      apply (test i (.inl ())).trans
      rw [h,hm.charge]
      simp
    · intro e t
      have ht := test (dir.cables e) (.inr t)
      change f.eval x (.inl (dir.cables e,.inr t)) = _ at ht
      rw [ht,pair]
      exact hm.first _ _ _ _

end PackedHistoryCircuit.Terminal

end BorderVNP
end Computability
end OAI
