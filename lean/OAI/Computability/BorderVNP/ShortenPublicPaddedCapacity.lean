import OAI.Computability.BorderVNP.ShortenStaticRows
import OAI.Computability.BorderVNP.PackedCoverScale

/-!
# Padded site and cable capacities over the full shortening history

The static old-edge rectangles reserve both hooks and a retained band, including
holes. Each combining round first places the complete arrays of all child packs
side by side and then reserves the actual bank templates. Congruence reduction
bounds the number of geometric seed tiles by the starting cover volume.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.PublicCapacity

open Cover Epoch Crossing
open scoped Classical

/-- Numbers of reserved site and cable identifiers in one stable pack. -/
structure Shape where
  /-- Number of reserved site records. -/
  sites : ℕ
  /-- Number of reserved cable records, including unused band names. -/
  edges : ℕ

/-- Global array length, counting a single query lane per available tile. -/
def Shape.volume (s : Shape) (tiles : ℕ) : ℕ := s.sites+s.edges+tiles+1

/-- Row-major disjoint union of complete child tables. -/
def Shape.parallel (s : Shape) (fan : ℕ) : Shape := ⟨fan*s.sites,fan*s.edges⟩

/-- An epoch's initial subdivision reserves up to `extra` interior sites per
old cable and up to `extra+1` resulting hop cables, including holes. -/
def Shape.subdivide (s : Shape) (extra : ℕ) : Shape :=
  ⟨s.sites+extra*s.edges,(extra+1)*s.edges⟩

/-- Actual capacity of one sparse successor serialization, including all
retained and cut band slots regardless of which histogram selects them. -/
noncomputable def Shape.sew {D m : ℕ} {K : Type*} [Field K] (s : Shape)
    (e : PaidIdentity K D m) (seeds : ℕ) : Shape :=
  ⟨StaticRows.siteCapacity e s.sites seeds,StaticRows.edgeCapacity e s.edges seeds⟩

/-- Congruence reduction gives enough distinct initial tiles for every
intermediate stage, uniformly in the varying cover level. -/
theorem tiles_mono (I : Type*) [Fintype I] {l z : ℕ} (h : l ≤ z) :
    Fintype.card (I → Deck l) ≤ Fintype.card (I → Deck z) :=
  Fintype.card_le_of_surjective (fun x i => deckReduction h (x i))
    (Function.Surjective.piMap fun _ : I => deckReduction_surjective h)

/-- Exact geometric seed arity, bounded using the common starting cover. -/
theorem seed_card_le (I B : Type*) [Fintype I] [Fintype B] {l z bins : ℕ}
    (h : l ≤ z) (hb : Fintype.card B ≤ bins) :
    Fintype.card ((I → Deck l) × B) ≤ Fintype.card (I → Deck z)*bins := by
  rw [Fintype.card_prod]
  exact Nat.mul_le_mul (tiles_mono I h) hb

/-- Subdivision and pack replication multiply the linear volume only by
their fixed arities. -/
theorem Shape.subdivide_volume (s : Shape) (extra V : ℕ) :
    (s.subdivide extra).volume V ≤ (2*extra+1)*s.volume V := by
  simp only [Shape.volume,Shape.subdivide]
  nlinarith

theorem Shape.parallel_volume (s : Shape) {fan : ℕ} (hf : 1 ≤ fan) (V : ℕ) :
    (s.parallel fan).volume V ≤ fan*s.volume V := by
  simp only [Shape.volume,Shape.parallel]
  nlinarith [Nat.mul_le_mul_right (V+1) hf]

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Fixed factor covering every rectangular old-band and seed allocation. -/
noncomputable def sewFactor (bins : ℕ) :=
  3*(2*D+1)+bins*(Fintype.card (StaticRows.TemplateSite e)+Fintype.card (StaticRows.TemplateEdge e))+1

theorem sewFactor_pos (bins : ℕ) : 1 ≤ sewFactor e bins := by unfold sewFactor; omega

/-- Concrete stable row capacity of a combine: K complete old arrays plus the
fixed cut and bank rectangles. Unused cable names are all charged in this bound. -/
theorem Shape.sew_volume (s : Shape) (bins V seeds : ℕ) (hs : seeds ≤ V*bins) :
    (s.sew e seeds).volume V ≤ sewFactor e bins*s.volume V := by
  let N := s.volume V
  let bank := Fintype.card (StaticRows.TemplateSite e)+Fintype.card (StaticRows.TemplateEdge e)
  let bands := 3*(2*D+1)
  have hsites : s.sites+V+1 ≤ N := by dsimp [N,Shape.volume]; omega
  have hedges : bands*s.edges ≤ bands*N := Nat.mul_le_mul_left _ (by dsimp [N,Shape.volume]; omega)
  have htiles : V ≤ N := by dsimp [N,Shape.volume]; omega
  have hb : seeds*bank ≤ bins*bank*N := (Nat.mul_le_mul_right _ hs).trans (by
    rw [show V*bins*bank = bins*bank*V by ring]
    exact Nat.mul_le_mul_left _ htiles)
  calc
    _ = s.sites+V+1 + bands*s.edges + seeds*bank := by
      simp only [Shape.volume,Shape.sew,StaticRows.edgeCapacity_eq,StaticRows.siteCapacity,bank,bands]; ring
    _ ≤ N + bands*N + bins*bank*N := Nat.add_le_add (Nat.add_le_add hsites hedges) hb
    _ = _ := by change _ = (bands+bins*bank+1)*N; ring

/-- State after `j` combining subrounds of one epoch. -/
noncomputable def combineRows (fan : ℕ) (seeds : ℕ → ℕ) (base : Shape) : ℕ → Shape
  | 0 => base
  | j+1 => ((combineRows fan seeds base j).parallel fan).sew e (seeds j)

/-- Capacity growth throughout the subrounds, even if every possible band
and bank is reserved at every stage. -/
theorem combineRows_le {fan : ℕ} (hf : 1 ≤ fan) (V bins : ℕ) (seeds : ℕ → ℕ)
    (hs : ∀ j, seeds j ≤ V*bins) (base : Shape) (j : ℕ) :
    (combineRows e fan seeds base j).volume V ≤ (sewFactor e bins*fan)^j * base.volume V := by
  induction j with
  | zero => simp [combineRows]
  | succ j ih =>
    calc
      _ ≤ sewFactor e bins*((combineRows e fan seeds base j).parallel fan).volume V :=
        Shape.sew_volume e _ _ _ _ (hs j)
      _ ≤ sewFactor e bins*(fan*((sewFactor e bins*fan)^j*base.volume V)) :=
        Nat.mul_le_mul_left _ ((Shape.parallel_volume _ hf _).trans (Nat.mul_le_mul_left _ ih))
      _ = _ := by rw [pow_succ]; ring

/-- The static pack at each epoch boundary. Rounding changes physical sites
and charge flags, while the row and cable shapes are those of the sewn layout. -/
noncomputable def epochRows (fan rounds extra : ℕ) (seeds : ℕ → ℕ → ℕ) (initial : Shape) : ℕ → Shape
  | 0 => initial
  | t+1 => combineRows e fan (seeds t) ((epochRows fan rounds extra seeds initial t).subdivide extra) rounds

/-- Total fixed row multiplier in one epoch, including subdivision and all pack copies. -/
noncomputable def epochFactor (fan rounds extra bins : ℕ) :=
  (sewFactor e bins*fan)^rounds*(2*extra+1)

theorem epochFactor_pos {fan : ℕ} (hf : 1 ≤ fan) (rounds extra bins : ℕ) :
    1 ≤ epochFactor e fan rounds extra bins := by
  exact Nat.mul_pos (Nat.one_le_pow _ _ (Nat.mul_pos (sewFactor_pos e bins) hf)) (by omega)

/-- Actual stable rectangle capacity at every epoch boundary. -/
theorem epochRows_le {fan : ℕ} (hf : 1 ≤ fan) (rounds extra V bins : ℕ) (seeds : ℕ → ℕ → ℕ)
    (hs : ∀ t j, seeds t j ≤ V*bins) (initial : Shape) (t : ℕ) :
    (epochRows e fan rounds extra seeds initial t).volume V ≤
      (epochFactor e fan rounds extra bins)^t * initial.volume V := by
  induction t with
  | zero => simp [epochRows]
  | succ t ih =>
    let old := epochRows e fan rounds extra seeds initial t
    calc
      _ ≤ (sewFactor e bins*fan)^rounds * (old.subdivide extra).volume V :=
        combineRows_le e hf V bins (seeds t) (hs t) _ rounds
      _ ≤ (sewFactor e bins*fan)^rounds *
          ((2*extra+1)*((epochFactor e fan rounds extra bins)^t*initial.volume V)) :=
        Nat.mul_le_mul_left _ ((old.subdivide_volume _ _).trans (Nat.mul_le_mul_left _ ih))
      _ = _ := by rw [pow_succ]; unfold epochFactor; ring

/-- Raw histogram inputs include the K children of the currently processed
node. One remaining combining step already pays for this replication. Thus
there is a single geometric-growth power per epoch, including padded holes. -/
theorem joinedRows_le {fan : ℕ} (hf : 1 ≤ fan) (rounds extra V bins : ℕ) (seeds : ℕ → ℕ → ℕ)
    (hs : ∀ t j, seeds t j ≤ V*bins) (initial : Shape) {t T j : ℕ} (ht : t<T) (hj : j<rounds) :
    let old := epochRows e fan rounds extra seeds initial t
    let sub := combineRows e fan (seeds t) (old.subdivide extra) j
    (sub.parallel fan).volume V ≤ (epochFactor e fan rounds extra bins)^T * initial.volume V := by
  intro old sub
  let C := sewFactor e bins*fan
  let G := epochFactor e fan rounds extra bins
  have hp : 1 ≤ C := Nat.mul_pos (sewFactor_pos e bins) hf
  have hfan : fan ≤ C := Nat.le_mul_of_pos_left fan (sewFactor_pos e bins)
  have pow : fan*C^j ≤ C^rounds := (Nat.mul_le_mul_right _ hfan).trans
    ((by rw [←pow_succ']; exact Nat.pow_le_pow_right hp hj : C*C^j ≤ C^rounds))
  have oldcap := epochRows_le e hf rounds extra V bins seeds hs initial t
  have subcap := combineRows_le e hf V bins (seeds t) (hs t) (old.subdivide extra) j
  calc
    _ ≤ fan*(C^j*((2*extra+1)*(G^t*initial.volume V))) :=
      (sub.parallel_volume hf _).trans (Nat.mul_le_mul_left _ (subcap.trans (Nat.mul_le_mul_left _
        ((old.subdivide_volume _ _).trans (Nat.mul_le_mul_left _ oldcap)))))
    _ = (fan*C^j)*((2*extra+1)*(G^t*initial.volume V)) := by ring
    _ ≤ C^rounds*((2*extra+1)*(G^t*initial.volume V)) := Nat.mul_le_mul_right _ pow
    _ = G^(t+1)*initial.volume V := by rw [pow_succ']; dsimp [G,epochFactor,C]; ring
    _ ≤ _ := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (epochFactor_pos e hf _ _ _) ht)

/-- Across the whole tree, the number of nodes at a level cancels the
fan-in powers already included in each node's rectangle. All levels thus
carry just one full leaf multiplicity, including every padded hole. -/
theorem tree_level_volume {fan : ℕ} (hf : 1 ≤ fan) (rounds extra V bins : ℕ) (seeds : ℕ → ℕ → ℕ)
    (hs : ∀ t j, seeds t j ≤ V*bins) (initial : Shape) {t T j : ℕ} (ht : t<T) (hj : j<rounds) :
    let old := epochRows e fan rounds extra seeds initial t
    let sub := combineRows e fan (seeds t) (old.subdivide extra) j
    fan^(rounds*T-(rounds*t+j+1))*(sub.parallel fan).volume V ≤
      (epochFactor e fan rounds extra bins)^T * initial.volume V := by
  intro old sub
  let F := sewFactor e bins
  let P := 2*extra+1
  let G := epochFactor e fan rounds extra bins
  have hF : 1 ≤ F := sewFactor_pos e bins
  have hP : 1 ≤ P := by dsimp [P]; omega
  have hdepth : rounds*t+j+1 ≤ rounds*T := by
    have hm := Nat.mul_le_mul_left rounds ht
    rw [Nat.mul_succ] at hm
    omega
  have hleaf : fan^(rounds*T-(rounds*t+j+1)) * fan^(rounds*t+j+1) = fan^(rounds*T) := by
    rw [←pow_add,Nat.sub_add_cancel hdepth]
  have each : (sub.parallel fan).volume V ≤
      fan^(rounds*t+j+1)*(F^(rounds*t+j)*P^(t+1))*initial.volume V := by
    have oldcap := epochRows_le e hf rounds extra V bins seeds hs initial t
    have subcap := combineRows_le e hf V bins (seeds t) (hs t) (old.subdivide extra) j
    apply (sub.parallel_volume hf _).trans
    apply (Nat.mul_le_mul_left fan (subcap.trans (Nat.mul_le_mul_left _
      ((old.subdivide_volume _ _).trans (Nat.mul_le_mul_left _ oldcap))))).trans_eq
    dsimp only [G,epochFactor,F,P]
    simp only [mul_pow,pow_add,pow_mul,pow_one]
    ring
  have Fbound := Nat.pow_le_pow_right hF (show rounds*t+j ≤ rounds*T by omega)
  have Pbound := Nat.pow_le_pow_right hP ht
  calc
    _ ≤ fan^(rounds*T-(rounds*t+j+1))*(fan^(rounds*t+j+1)*(F^(rounds*t+j)*P^(t+1))*initial.volume V) :=
      Nat.mul_le_mul_left _ each
    _ = fan^(rounds*T)*(F^(rounds*t+j)*P^(t+1))*initial.volume V := by
      rw [←hleaf]; ring
    _ ≤ fan^(rounds*T)*(F^(rounds*T)*P^T)*initial.volume V :=
      Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.mul_le_mul Fbound Pbound))
    _ = _ := by dsimp [epochFactor,F,P]; simp only [mul_pow,pow_mul]; ring

/-- Summing over every epoch and combining subround charges at most
the number of levels times the single terminal tree capacity. -/
theorem tree_volume {fan : ℕ} (hf : 1 ≤ fan) (rounds extra V bins : ℕ) (seeds : ℕ → ℕ → ℕ)
    (hs : ∀ t j, seeds t j ≤ V*bins) (initial : Shape) (T : ℕ) :
    (∑ tj : Fin T × Fin rounds,
      let old := epochRows e fan rounds extra seeds initial tj.1.val
      let sub := combineRows e fan (seeds tj.1.val) (old.subdivide extra) tj.2.val
      fan^(rounds*T-(rounds*tj.1.val+tj.2.val+1))*(sub.parallel fan).volume V) ≤
      T*rounds*((epochFactor e fan rounds extra bins)^T*initial.volume V) := by
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using
    Finset.sum_le_sum (s := Finset.univ) fun (tj : Fin T × Fin rounds) _ =>
      tree_level_volume e hf rounds extra V bins seeds hs initial tj.1.isLt tj.2.isLt

end Shortening.PublicCapacity

end BorderVNP
end Computability
end OAI
