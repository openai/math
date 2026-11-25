import OAI.ThreeFlat.CrossingTiling
import OAI.LinearAlgebra.SpectralBooks.SiteTensor.TensorGrouping

namespace OAI
/-! # Placing six-terminal crossing tiles in an arbitrary polygon -/

open scoped BigOperators Classical
noncomputable section

namespace ThreeFlat.CatalyticEmbedding

open LinearAlgebra.SpectralBooks ChordGraph SiteTensor

variable {k m n : ℕ}

def embedEdge (e : Fin m ↪o Fin n) (t : Chord m) : Chord n :=
  ⟨(e t.1.1,e t.1.2), e.strictMono t.2⟩

def push (e : Fin m ↪o Fin n) : Widths m →+ Widths n :=
  Finsupp.mapDomain.addMonoidHom (embedEdge e)

@[simp] theorem push_single (e : Fin m ↪o Fin n) (t : Chord m) (a : ℕ) :
    push e (Finsupp.single t a) = Finsupp.single (embedEdge e t) a :=
  Finsupp.mapDomain_single

def ordinarySite (k : ℕ) : Fin k ↪o Fin (k+2) :=
  OrderEmbedding.ofStrictMono (fun i => ⟨i.1, by omega⟩) (fun _ _ h => h)

def ordinary (k : ℕ) : Widths k →+ Widths (k+2) := push (ordinarySite k)

def reserve (k : ℕ) : ℕ →+ Widths (k+2) where
  toFun := Finsupp.single (edge (⟨k,by omega⟩ : Fin (k+2)) ⟨k+1, by omega⟩ (by simp [Fin.lt_def]))
  map_zero' := Finsupp.single_zero _
  map_add' := Finsupp.single_add _

def pre (k : ℕ) : Fin (k+2) := ⟨k,by omega⟩
def post (k : ℕ) : Fin (k+2) := ⟨k+1,by omega⟩

theorem load_push (e : Fin m ↪o Fin n) (i : Fin m) (g : Widths m) :
    load (e i) (push e g) = load i g := by
  induction g using Finsupp.induction with
  | zero => simp
  | single_add t w f h₁ h₂ ih =>
    simp [map_add, ih, embedEdge, load_single]

theorem load_push_outside (e : Fin m ↪o Fin n) (j : Fin n) (hj : j ∉ Set.range e)
    (g : Widths m) : load j (push e g) = 0 := by
  have ne (t : Fin m) : j ≠ e t := fun he => hj ⟨t,he.symm⟩
  induction g using Finsupp.induction with
  | zero => simp
  | single_add t w f h₁ h₂ ih =>
    simp [map_add, ih, embedEdge, load_single, ne]

@[simp] theorem load_ordinary_pre (g : Widths k) : load (pre k) (ordinary k g) = 0 := by
  apply load_push_outside
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change i.val = k at he
  omega

@[simp] theorem load_ordinary_post (g : Widths k) : load (post k) (ordinary k g) = 0 := by
  apply load_push_outside
  rintro ⟨i, hi⟩
  have he := congrArg Fin.val hi
  change i.val = k+1 at he
  omega

@[simp] theorem load_reserve_pre (w : ℕ) : load (pre k) (reserve k w) = w := by
  have h : pre k ≠ post k := fun hh => by
    have he := congrArg Fin.val hh
    change k = k+1 at he
    omega
  change load (pre k) (Finsupp.single (edge (pre k) (post k) _) w) = w
  simp [load_single, edge, h]

@[simp] theorem load_reserve_post (w : ℕ) : load (post k) (reserve k w) = w := by
  have h : post k ≠ pre k := fun hh => by
    have he := congrArg Fin.val hh
    change k+1 = k at he
    omega
  change load (post k) (Finsupp.single (edge (pre k) (post k) _) w) = w
  simp [load_single, edge, h]

variable {a b c d : Fin k}

def quad (hab : a < b) (hbc : b < c) (hcd : c < d) : Fin 6 ↪o Fin (k+2) :=
  OrderEmbedding.ofStrictMono
    ![ordinarySite k a, ordinarySite k b, ordinarySite k c, ordinarySite k d,
      ⟨k,by omega⟩,⟨k+1,by omega⟩] (by
    apply Fin.strictMono_iff_lt_succ.mpr
    intro i
    fin_cases i
    · exact hab
    · exact hbc
    · exact hcd
    · exact d.isLt
    · change k < k + 1
      omega)

variable (hab : a < b) (hbc : b < c) (hcd : c < d)

theorem push_demand (w R : ℕ) :
    push (quad hab hbc hcd) (CrossingSupply.crossDemand w R) =
      ordinary k (w • crossing hab hbc hcd) + reserve k (w*R) := by
  simp only [CrossingSupply.crossDemand, CrossingSupply.crossWires, CrossingSupply.wire,
    crossing, unitChord, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one,
    ordinary, map_add, push_single]
  rfl

theorem push_matching (u v : ℕ) :
    push (quad hab hbc hcd) (CrossingSupply.matching true u + CrossingSupply.matching false v) =
      ordinary k (u • parallel hab hbc hcd + v • nested hab hbc hcd) := by
  simp only [CrossingSupply.matching, CrossingSupply.wire, ↓reduceIte, Bool.false_eq_true,
    parallel, nested, unitChord, smul_add, Finsupp.smul_single, smul_eq_mul, mul_one,
    ordinary, map_add, push_single]
  rfl

variable {F : Type*} [Field F]

private theorem group_wire [Nonempty (Fin m)] [Nonempty (Fin n)] (e : Fin m ↪o Fin n) (t : Chord m) :
    groupMulHom (K := F) e (ChordGraph.wire F t) = ChordGraph.wire F (embedEdge e t) := by
  unfold ChordGraph.wire
  change ofRaw (((Raw.diagonal (Fin 2) F (Fin 2)).group _).group e) = _
  rw [ofRaw_eq_iff.mpr (Raw.group_group_equivalent _ _ _)]
  have eqn : (e ∘ ![t.1.1,t.1.2]) = ![e t.1.1,e t.1.2] := by
    funext i
    fin_cases i <;> rfl
  rw [eqn]
  rfl

theorem group_graph [Nonempty (Fin m)] [Nonempty (Fin n)] (e : Fin m ↪o Fin n) (g : Widths m) :
    groupMulHom (K := F) e (graphClass F g) = graphClass F (push e g) := by
  induction g using Finsupp.induction with
  | zero => simp
  | single_add t w f h₁ h₂ ih => simp [map_add, group_wire, ih]

/-- A coefficientwise sum continues to be a coefficientwise sum after all six
endpoints take their physical positions. Grouping restrictions preserves every
matrix witness even when the other polygon vertices are unused in this tile. -/
theorem embed_sum (e : Fin m ↪o Fin n) [Nonempty (Fin m)] [Nonempty (Fin n)]
    {J : Type*} [Fintype J] (g : Widths m) (h : J → Widths m)
    (z : J → (∀ i, (raw F g).Leg i) → F) (sum : (raw F g).coeff = ∑ j, z j)
    (terms : ∀ j, ({raw F g with coeff := z j} : Raw (Fin m) F).Restricts (raw F (h j))) :
    graphClass F (push e g) ≤ ∑ j, graphClass F (push e (h j)) := by
  let X := raw F g
  let L (j : J) := ({X with coeff := z j} : Raw (Fin m) F).group e
  have hsum : (X.group e).coeff = ∑ j, (L j).coeff := by
    change (fun x : (v : Fin n) → (p : {i // e i = v}) → (raw F g).Leg p.1 =>
      (raw F g).coeff ((groupIndexEquiv e (raw F g).Leg).symm x)) =
      ∑ j, (fun x => z j ((groupIndexEquiv e (raw F g).Leg).symm x))
    funext x
    simp only [sum, Finset.sum_apply]
  have h₀ : ofRaw (X.group e) ≤ ∑ j, ofRaw (L j) := by
    change ofCoeffs (X.group e).coeff ≤ ∑ j, ofCoeffs ((L j).coeff)
    rw [hsum]
    exact ordinary_sum_le _
  have regroup (v : Widths m) : ofRaw ((raw F v).group e) = graphClass F (push e v) := by
    change groupMulHom (K := F) e (ofRaw (raw F v)) = _
    rw [ofRaw_raw, group_graph]
  calc
    _ = ofRaw (X.group e) := (regroup g).symm
    _ ≤ _ := h₀
    _ ≤ _ := Finset.sum_le_sum fun j _ =>
      (ofRaw_le_iff.mpr (Raw.group_restricts e (terms j))).trans_eq (regroup _)

open Filter

theorem physical_step (hno : ¬ Nonempty (SpectralPlacementPrices F (EuclideanSpace ℝ (Fin 3))))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ R : ℕ, 4 ≤ R ∧ ∀ {η : ℝ}, 0 < η → ∀ᶠ w : ℕ in atTop, ∀ (k : ℕ)
      {a b c d : Fin k} (hab : a < b) (hbc : b < c) (hcd : c < d),
      ∃ (J : Type) (_ : Fintype J) (s : ℕ), Fintype.card J ≤ 2^s ∧ (s : ℝ) ≤ η*w ∧
      ∃ (u v t : J → ℕ) (H : J → Widths 6),
        (∀ j, u j + v j ≤ w ∧ (t j : ℝ) ≤ ε*w ∧
          (∀ x : Chord 6, ¬(x.1.1 < 4 ∧ 4 ≤ x.1.2) → H j x = 0) ∧
          load 4 (H j) = w*R ∧ load 5 (H j) = w*R) ∧
        graphClass F (ordinary k (w • crossing hab hbc hcd) + reserve k (w*R)) ≤
          ∑ j, graphClass F (ordinary k (u j • parallel hab hbc hcd + v j • nested hab hbc hcd) +
            push (quad hab hbc hcd) (CrossingSupply.slack (t j) + H j)) := by
  obtain ⟨R,hR,h⟩ := eventually_catalytic_crossing hno hε
  refine ⟨R,hR,fun hη => ?_⟩
  filter_upwards [h hη] with w hw
  intro k a b c d hab hbc hcd
  obtain ⟨J,inst,s,hJ,hs,z,hz,terms⟩ := hw
  let : Fintype J := inst
  choose u v t H huv ht supp hl hr hterms using terms
  refine ⟨J,inst,s,hJ,hs,u,v,t,H,fun j => ⟨huv j,ht j,supp j,hl j,hr j⟩, ?_⟩
  have transform (j : J) :
      push (quad hab hbc hcd) (CrossingSupply.matching true (u j) +
        CrossingSupply.matching false (v j) + CrossingSupply.slack (t j) + H j) =
      ordinary k (u j • parallel hab hbc hcd + v j • nested hab hbc hcd) +
        push (quad hab hbc hcd) (CrossingSupply.slack (t j) + H j) := by
    rw [add_assoc (CrossingSupply.matching true _ + CrossingSupply.matching false _),
      map_add, push_matching]
  simpa only [push_demand, transform] using
    embed_sum (quad hab hbc hcd) (CrossingSupply.crossDemand w R)
      (fun j => CrossingSupply.matching true (u j) + CrossingSupply.matching false (v j) +
        CrossingSupply.slack (t j) + H j) z hz hterms

end ThreeFlat.CatalyticEmbedding
end

end OAI
