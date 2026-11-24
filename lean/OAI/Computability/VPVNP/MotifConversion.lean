import OAI.Computability.VPVNP.MotifBlocks
import OAI.Computability.VPVNP.MotifAdmission
import OAI.Computability.VPVNP.MotifParameters
import OAI.Computability.VPVNP.MotifPowerExpansion
import OAI.Computability.VPVNP.MotifEntry

/-!
# Conversion of a fixed wire motif

Theorem 6.1 of *VP and VNP differ over every field* converts the spectral
inequality (6.1) into ordinary tensor identities. All scalar parameters and
their integer equations are chosen before the input widths. A local matrix
entry is represented independently of the coefficient ring by either failure
or the list of parameter indices whose product is the entry.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace MotifConversion

open WireTensor MotifGrid MotifBlocks MotifSelector MotifDemandPadding

universe u v
variable {k : Type u} [Field k] {J : Type v} [Fintype J]
variable {D S : Type} [Fintype D] [Fintype S]
variable {a b : D → J} {P : Supply J S} {p : D → ℚ} {q : S → ℚ} {H H' : ℝ}
variable (B : FixedBlock k a b P (realWidths p) (realWidths q) H H')

/-- The integral demand and supply arrays used in the fixed polynomial equations. -/
noncomputable abbrev parameterData := MotifParameters.wireData a b P.src P.dst
  (B.grid.demandWidths B.multiple) (B.grid.supplyWidths B.multiple) B.copyCount B.power

theorem exists_solution : ∃ κ : (parameterData B).Entry → k, (parameterData B).IsSolution κ :=
  MotifParameters.exists_wire_solution _ _ _ _ _ _ _ _ B.baseIdentity

/-- A base-identity selector, comprising a copy index and one supply-grid choice per
tensor-power factor. -/
abbrev Selector := Fin B.copyCount × (Fin B.power → B.grid.supplies)

/-- Supply widths of one selected copy of the base identity. -/
noncomputable def basePayload (σ : Selector B) : S → ℕ :=
  MotifBase.payload (B.grid.supplyWidths B.multiple) σ.2

/-- One fixed finite encoding of the base selectors, including invalid bit words. -/
noncomputable def selectorCode : Selector B ↪ Word B.selectorBits := by
  apply Classical.choice (Function.Embedding.nonempty_of_card_le ?_)
  simp only [Selector, Word, Fintype.card_fin, Fintype.card_prod, Fintype.card_fun,
    Fintype.card_coe]
  exact
    MotifWidths.selector_capacity B.copyCount B.grid.supplies.card B.power

/-- Compute the block repetitions using integer arithmetic. -/
def repetitions (w : D → ℕ) : ℕ := MotifAdmission.copies p w B.scale

theorem repetitions_eq (hp : ∀ i, 0 < p i) (w : D → ℕ) :
    repetitions B w = B.repetitions w := MotifAdmission.copies_eq _ hp w _ B.scale_pos

/-- The set of admitted outer supply payloads. Testing one supplied index uses
only the fixed integer mass coefficients, without enumerating this set. -/
noncomputable def outerIndices (w : D → ℕ) : Finset (S → ℕ) := by
  classical
  let u := repetitions B w
  let cap := MotifAdmission.payloadCap q u B.scale B.radius
  exact (Finset.univ.image (fun f : S → Fin (cap + 1) => fun e => (f e).val)).filter
    (fun v => MotifAdmission.admit q v u B.scale B.radius = true)

theorem mem_outerIndices_iff (hq : ∀ i, 0 < q i) (w : D → ℕ) (v : S → ℕ) :
    v ∈ outerIndices B w ↔ MotifAdmission.admit q v (repetitions B w) B.scale B.radius = true := by
  classical
  constructor
  · exact fun hv => (Finset.mem_filter.mp hv).2
  · intro hv
    let cap := MotifAdmission.payloadCap q (repetitions B w) B.scale B.radius
    let f : S → Fin (cap + 1) := fun i => ⟨v i, Nat.lt_succ_of_le
      (MotifAdmission.payload_le_cap q hq v _ _ _ hv i)⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_image_of_mem _ (Finset.mem_univ f), hv⟩

theorem sequence_mem_outerIndices (hq : ∀ i, 0 < q i) (w : D → ℕ)
    (θ : Fin (repetitions B w) → Selector B) :
    totalWidth (basePayload B) θ ∈ outerIndices B w := by
  rw [mem_outerIndices_iff B hq, MotifAdmission.admit_eq_true_iff q hq _ _ _ _ B.radius_pos.le]
  exact B.sequence_payload_le (fun i => Rat.cast_pos.mpr (hq i)) _ (fun i => (θ i).2)

/-- Total widths, including a complete selector list on each supply edge. -/
def supplyWidths (w : D → ℕ) (v : S → ℕ) (i : S) : ℕ := v i + repetitions B w * B.selectorBits

theorem energy_le (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) (w : D → ℕ)
    (v : S → ℕ) (hv : v ∈ outerIndices B w) :
    widthNorm (realWidths q) (fun e => (supplyWidths B w v e : ℝ)) ^ 2 ≤
      H' * widthNorm (realWidths p) (fun e => (w e : ℝ)) ^ 2 + B.energyConstant := by
  rw [mem_outerIndices_iff B hq, MotifAdmission.admit_eq_true_iff q hq _ _ _ _ B.radius_pos.le,
    repetitions_eq B hp] at hv
  unfold supplyWidths
  rw [repetitions_eq B hp]
  exact B.padded_energy_le w v hv

/-- Rounded demand grid point found by scanning the fixed table of grid points. -/
noncomputable def demandGrid (hp : ∀ i, 0 < p i) (w : D → ℕ) : B.grid.demands := by
  let table := B.grid.demands.toList
  let res := MotifAdmission.selectGrid p w table
  have hex := MotifAdmission.selectGrid_exists p hp B.grid w table
    (fun _ hz => Finset.mem_toList.mpr hz)
  have hs : res.isSome := Option.isSome_iff_exists.mpr hex
  have h := MotifAdmission.selectGrid_spec p hp w (Option.some_get hs).symm
  exact ⟨res.get hs, Finset.mem_toList.mp h.1⟩

theorem selectGrid_eq (hp : ∀ i, 0 < p i) (w : D → ℕ) :
    MotifAdmission.selectGrid p w B.grid.demands.toList = some (demandGrid B hp w).val :=
  (Option.some_get _).symm

/-- Demand width for edge `e` at grid point `z`, scaled by the block multiplier and tensor
power. -/
noncomputable abbrev baseDemand (z : B.grid.demands) (e : D) :=
  B.power * B.grid.demandWidths B.multiple z e

theorem demand_le (hp : ∀ i, 0 < p i) (w : D → ℕ) (i : D) :
    w i ≤ repetitions B w * baseDemand B (demandGrid B hp w) i := by
  let z := demandGrid B hp w
  have hz := (MotifAdmission.selectGrid_spec p hp w (selectGrid_eq B hp w)).2
  rw [repetitions_eq B hp]
  apply MotifWidths.copies_dominate (realWidths p) w _ B.scale_pos (realWidths z.val)
    (fun j => Rat.cast_nonneg.mpr (hz j).1) (fun j => (hz j).2) _ i
  intro j
  simp [baseDemand, FixedBlock.scale, realWidths, mul_assoc, z]

/-- A local entry description before substituting any scalar parameters. -/
noncomputable def entry (hp : ∀ i, 0 < p i) (w : D → ℕ) (v : S → ℕ) (j : J)
    (x : HalfBits a b w j) (y : Half P (fun e => Word (supplyWidths B w v e)) j) :
    Option (Fin (repetitions B w) → (parameterData B).Entry) :=
  (groupedIndices P (basePayload B) (selectorCode B) v j
    (fun i => demandChunk a b (demand_le B hp w) i j x) y).map
    (fun t i => ⟨demandGrid B hp w, (t i).1, j, (t i).2.1, (t i).2.2⟩)

/-- An absent description evaluates to zero. A successful description evaluates
to one parameter per copy. -/
def evalEntry {Param A : Type*} [CommMonoidWithZero A] {n : ℕ} (κ : Param → A)
    (idx : Option (Fin n → Param)) : A := idx.elim 0 fun t => ∏ i, κ (t i)

private theorem evalEntry_grouped {A : Type*} [CommRing A] (κ : (parameterData B).Entry → A)
    (hp : ∀ i, 0 < p i) (w : D → ℕ) (v : S → ℕ) (j : J)
    (x : HalfBits a b w j) (y : Half P (fun e => Word (supplyWidths B w v e)) j) :
    evalEntry κ (entry B hp w v j x y) =
      groupedMap P (basePayload B) ((parameterData B).localMap κ (demandGrid B hp w))
        (selectorCode B) v j (fun i => demandChunk a b (demand_le B hp w) i j x) y := by
  let z := demandGrid B hp w
  have aux (o : Option (EntryIndices P (HalfBits a b (baseDemand B z)) (basePayload B)
      (repetitions B w) j)) :
      evalEntry κ (o.map (fun t i => ⟨z, (t i).1, j, (t i).2.1, (t i).2.2⟩)) =
      evalIndices ((parameterData B).localMap κ z) j o := by cases o <;> rfl
  exact aux _

/-- The local description specializes to zero or a single monomial of degree at
most the number of base copies, including when that number is zero. -/
theorem entry_monomial (hp : ∀ i, 0 < p i) (w : D → ℕ) (v : S → ℕ) (j : J)
    (x : HalfBits a b w j) (y : Half P (fun e => Word (supplyWidths B w v e)) j) :
    let poly := evalEntry (MvPolynomial.X (R := ℤ)) (entry B hp w v j x y)
    (poly = 0 ∨ ∃ f, poly = MvPolynomial.monomial f 1) ∧ poly.totalDegree ≤ repetitions B w := by
  cases h : entry B hp w v j x y with
  | none => simp [evalEntry]
  | some t =>
    exact ⟨Or.inr ⟨_, MotifParameters.prod_entries_eq_monomial t⟩,
      MotifParameters.prod_entries_degree_le t⟩

/-- The ordinary sum identity in (6.2), over any commutative ring and every
assignment satisfying the fixed integral equations. -/
theorem identity [Nonempty J] {A : Type*} [CommRing A] (κ : (parameterData B).Entry → A)
    (hκ : (parameterData B).IsSolution κ) (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i)
    (w : D → ℕ) :
    (wireNetwork (k := A) a b (fun e => Word (w e))).coeff =
      ∑ v ∈ outerIndices B w, applyLocal
        (B := (wireNetwork (k := A) P.src P.dst (fun e => Word (supplyWidths B w v e))).Basis)
        (fun j x y => evalEntry κ (entry B hp w v j x y))
        (wireNetwork P.src P.dst (fun e => Word (supplyWidths B w v e))).coeff := by
  classical
  funext x
  erw [Finset.sum_apply]
  let z := demandGrid B hp w
  let c (j : J) (i : Fin (repetitions B w)) := demandChunk a b (demand_le B hp w) i j (x j)
  let L := (parameterData B).localMap κ z
  have base := (MotifParameters.wire_solution_iff _ _ _ _ _ _ _ _ κ).mp hκ z
  have hcopy (i : Fin (repetitions B w)) :
      (wireNetwork (k := A) a b (fun e => Word (baseDemand B z e))).coeff (fun j => c j i) =
      ∑ σ, baseTerm P (basePayload B) L σ (fun j => c j i) := by
    have h := congrFun base (fun j => c j i)
    erw [Finset.sum_apply] at h
    exact h.trans (Finset.sum_congr rfl fun σ _ =>
      applyLocal_wireNetwork (k := A) P.src P.dst (fun e => Word (basePayload B σ e))
        (C := HalfBits a b (baseDemand B z)) (L σ) (fun j => c j i))
  calc
    _ = ∏ i, (wireNetwork (k := A) a b (fun e => Word (baseDemand B z e))).coeff
        (fun j => c j i) := coeff_eq_prod_chunks a b (demand_le B hp w) x
    _ = ∏ i, ∑ σ, baseTerm P (basePayload B) L σ (fun j => c j i) :=
      Finset.prod_congr rfl fun i _ => hcopy i
    _ = _ := (power_expansion P (basePayload B) L (selectorCode B) (outerIndices B w)
      (sequence_mem_outerIndices B hq w) c).trans <| Finset.sum_congr rfl fun v _ => by
      unfold applyLocal
      apply Finset.sum_congr rfl
      intro y _
      congr 1
      apply Finset.prod_congr rfl
      intro j _
      exact (evalEntry_grouped B κ hp w v j (x j) (y j)).symm

/-- The fixed number of outer coordinates, and the degree of every evaluated
monomial, use at most linearly many bits of wire payload per input-width unit. -/
theorem linear_index_bound (hq : ∀ i, 0 < q i) :
    ∃ C : ℕ, ∀ (M : ℕ) (w : D → ℕ), (∀ i, w i ≤ M) →
      repetitions B w ≤ C * (M + 1) ∧ ∀ v ∈ outerIndices B w, ∀ e, v e ≤ C * (M + 1) := by
  let W := (∑ i, MotifAdmission.weight p i) + 1
  let V := W * B.scale * B.radius.num.natAbs * MotifAdmission.denominator q
  refine ⟨max W V, fun M w hw => ?_⟩
  have hu := MotifAdmission.copies_le p w B.scale M B.scale_pos hw
  constructor
  · exact hu.trans (Nat.mul_le_mul_right _ (le_max_left _ _))
  · intro v hv e
    have hv' := (mem_outerIndices_iff B hq w v).mp hv
    exact (MotifAdmission.payload_le_cap q hq _ _ _ _ hv' e).trans
      ((MotifAdmission.payloadCap_le p q w _ M B.radius B.scale_pos hw).trans
        (Nat.mul_le_mul_right _ (le_max_right _ _)))

/-- The fixed finite selector table used in the local entry evaluator. -/
noncomputable def selectorTable : List (Selector B) := Finset.univ.toList

private theorem mem_selectorTable (s : Selector B) : s ∈ selectorTable B :=
  Finset.mem_toList.mpr (Finset.mem_univ _)

/-- A base matrix entry's index in the fixed parameter vector. -/
noncomputable abbrev lookup (z : B.grid.demands) (σ : Selector B) (j : J)
    (x : HalfBits a b (baseDemand B z) j) (y : Half P (fun e => Word (basePayload B σ e)) j) :
    (parameterData B).Entry := ⟨z, σ, j, x, y⟩

/-- The bit-string evaluator specialized to this block, with fixed finite table
and code. The count records bit probes and word operations of the local scan. -/
noncomputable def runEntry [DecidableEq J] (hp : ∀ i, 0 < p i) (w : D → ℕ) (v : S → ℕ) (j : J)
    (d : MotifEntry.DemandBits a b w j)
    (x : Half P (fun e => Fin (supplyWidths B w v e) → Bool) j) :
    Option (List (parameterData B).Entry) × ℕ :=
  let z := demandGrid B hp w
  MotifEntry.run a b (baseDemand B z) w P (basePayload B) (lookup B z) (selectorTable B)
    (selectorCode B) v j d x

/-- The actual bit-string evaluator returns the matrix entry used in (6.2)
after evaluating the reported parameter list. -/
theorem runEntry_correct [DecidableEq J] {A : Type*} [CommRing A] (κ : (parameterData B).Entry → A)
    (hp : ∀ i, 0 < p i) (w : D → ℕ) (v : S → ℕ) (j : J) (d : HalfBits a b w j)
    (x : Half P (fun e => Word (supplyWidths B w v e)) j) :
    (runEntry B hp w v j (MotifEntry.demandBits a b j d)
      (mapHalf P (fun _ => MotifEntry.inputBits) x)).1.elim 0 (fun names => (names.map κ).prod) =
      evalEntry κ (entry B hp w v j d x) := by
  dsimp only [runEntry]
  erw [MotifEntry.run_value, evalEntry_grouped]
  exact MotifEntry.describe_correct a b (demand_le B hp w) P (basePayload B)
    (lookup B (demandGrid B hp w)) κ (selectorTable B) (mem_selectorTable B)
    (selectorCode B) v j d x

/-- With the motif and its tables fixed, the number of bit probes and word
operations has absolute exponent two in the largest demand width. -/
theorem runEntry_cost [DecidableEq J] (hp : ∀ i, 0 < p i) :
    ∃ K : ℕ, ∀ (M : ℕ) (w : D → ℕ), (∀ i, w i ≤ M) → ∀ v j d x,
      (runEntry B hp w v j d x).2 ≤ K * (M + 1) ^ 2 := by
  let Dmax := ∑ z : B.grid.demands, ∑ e, baseDemand B z e
  let Smax := ∑ σ : Selector B, ∑ e, basePayload B σ e
  let U := (∑ i, MotifAdmission.weight p i) + 1
  let K := Fintype.card S * (12 * B.selectorBits + 12 * Smax + 48) +
    Fintype.card D * (12 * Dmax + 7) + 2 * (selectorTable B).length + 18
  have hD (z : B.grid.demands) (e : D) : baseDemand B z e ≤ Dmax :=
    (Finset.single_le_sum (f := baseDemand B z) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ e)).trans
      (Finset.single_le_sum (f := fun z => ∑ i, baseDemand B z i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ z))
  have hS (σ : Selector B) (e : S) : basePayload B σ e ≤ Smax :=
    (Finset.single_le_sum (f := basePayload B σ) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ e)).trans
      (Finset.single_le_sum (f := fun σ => ∑ i, basePayload B σ i) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ σ))
  refine ⟨K * (U + 1) ^ 2, fun M w hw v j d x => ?_⟩
  let z := demandGrid B hp w
  have hu : repetitions B w ≤ U * (M + 1) := MotifAdmission.copies_le p w B.scale M B.scale_pos hw
  have hu' : repetitions B w + 1 ≤ (U + 1) * (M + 1) := by
    rw [add_mul, one_mul]
    exact Nat.add_le_add hu (Nat.le_add_left _ _)
  calc
    _ ≤ K * (repetitions B w + 1) ^ 2 := MotifEntry.run_le a b (baseDemand B z) w P (basePayload B)
      (lookup B z) (selectorTable B) (selectorCode B) v j d x (hD z) hS
    _ ≤ K * ((U + 1) * (M + 1)) ^ 2 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hu' _)
    _ = _ := by ring

/-- With sequential storage one can rescan a string from its beginning for
every indexed bit probe. The resulting allowance is cubic in the maximum
input width, with a coefficient fixed before seeing the input. -/
theorem sequential_entry_cost [DecidableEq J] (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) :
    ∃ K : ℕ, ∀ (M : ℕ) (w : D → ℕ), (∀ e, w e ≤ M) → ∀ v ∈ outerIndices B w, ∀ j d x,
      let z := demandGrid B hp w
      (MotifEntry.tapeRun (u := repetitions B w) a b (baseDemand B z) w P (basePayload B)
        (lookup B z) (selectorTable B) (selectorCode B) v j d x).2 ≤ K * (M + 1) ^ 3 := by
  obtain ⟨C, hC⟩ := linear_index_bound B hq
  obtain ⟨A, hA⟩ := runEntry_cost B hp
  let cap := Fintype.card D + Fintype.card S * (C + C * B.selectorBits)
  refine ⟨(3 * cap + 2) * A, fun M w hw v hv j d x => ?_⟩
  obtain ⟨hu, hvs⟩ := hC M w hw
  have hlen (e : S) : supplyWidths B w v e ≤ (C + C * B.selectorBits) * (M + 1) := by
    calc
      _ ≤ C * (M + 1) + (C * (M + 1)) * B.selectorBits :=
        Nat.add_le_add (hvs v hv e) (Nat.mul_le_mul_right _ hu)
      _ = _ := by ring
  let length := (∑ e, w e) + ∑ e, supplyWidths B w v e
  have hs : length ≤ cap * (M + 1) := by
    have hd := Finset.sum_le_sum (s := Finset.univ) (fun e _ => (hw e).trans (Nat.le_succ M))
    have hv' := Finset.sum_le_sum (s := Finset.univ) (fun e _ => hlen e)
    simpa [length, cap, Nat.add_mul, Nat.mul_assoc] using Nat.add_le_add hd hv'
  have allowance : 3 * length + 2 ≤ (3 * cap + 2) * (M + 1) := by
    calc
      _ ≤ 3 * (cap * (M + 1)) + 2 * (M + 1) := Nat.add_le_add (Nat.mul_le_mul_left _ hs)
        (Nat.le_mul_of_pos_right _ (Nat.succ_pos M))
      _ = _ := by ring
  have hrun := hA M w hw v j
    (fun e h => MotifEntry.Tape.readBits (d.1 e h), fun e h => MotifEntry.Tape.readBits (d.2 e h))
    (mapHalf P (fun _ => MotifEntry.Tape.readBits) x)
  exact (Nat.mul_le_mul allowance hrun).trans_eq (by ring)

/-- The spectral bound (6.1) yields fixed integral equations, a solution in
the given field, and the identities (6.2) over every ring satisfying those
equations. The block and its additive error are fixed before the input widths.
The entry descriptions and outer indices are shared across all assignments. -/
theorem exists_conversion [Nontrivial J] (a b : D → J) (P : Supply J S) (p : D → ℚ) (q : S → ℚ)
    (hp : ∀ i, 0 < p i) (hq : ∀ i, 0 < q i) {H H' : ℝ} (hH : 0 ≤ H) (hHH' : H < H')
    (hcomp : ∀ F : SpectralPoint k J,
      distanceEnergy (realWidths p) (fun i => F.wireDistance (a i) (b i)) ≤
        H * distanceEnergy (realWidths q) (fun i => F.wireDistance (P.src i) (P.dst i))) :
    ∃ B : FixedBlock k a b P (realWidths p) (realWidths q) H H',
      (∃ κ : (parameterData B).Entry → k, (parameterData B).IsSolution κ) ∧
      (∀ (w : D → ℕ) v, v ∈ outerIndices B w →
        widthNorm (realWidths q) (fun e => (supplyWidths B w v e : ℝ)) ^ 2 ≤
          H' * widthNorm (realWidths p) (fun e => (w e : ℝ)) ^ 2 + B.energyConstant) ∧
      ∀ (A : Type*) [CommRing A] (κ : (parameterData B).Entry → A), (parameterData B).IsSolution κ →
        ∀ w : D → ℕ, (wireNetwork (k := A) a b (fun e => Word (w e))).coeff =
          ∑ v ∈ outerIndices B w, applyLocal
            (B := (wireNetwork (k := A) P.src P.dst (fun e => Word (supplyWidths B w v e))).Basis)
            (fun j x y => evalEntry κ (entry B hp w v j x y))
            (wireNetwork P.src P.dst (fun e => Word (supplyWidths B w v e))).coeff := by
  obtain ⟨B⟩ := exists_fixed_block a b P (realWidths p) (realWidths q)
    (fun i => Rat.cast_pos.mpr (hp i)) (fun i => Rat.cast_pos.mpr (hq i)) hH hHH' hcomp
  exact ⟨B, exists_solution B, energy_le B hp hq, fun _ _ κ hκ => identity B κ hκ hp hq⟩

end MotifConversion

end VPVNP
end Computability
end OAI
