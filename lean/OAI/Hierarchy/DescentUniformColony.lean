import OAI.Hierarchy.DescentColonyScorePermutation
import OAI.Hierarchy.DescentColonyScoreCore
import OAI.Hierarchy.DescentColonySelection
import OAI.Hierarchy.DescentColonyFinScan
import OAI.Hierarchy.DescentIrreducibleSearch
import OAI.Hierarchy.DescentResidueMultiplication

namespace OAI
/-! # Uniform field preprocessing and the shared field multiplier colony scan -/

namespace Hierarchy.DescentColonies

open DescentGL DescentBinaryField
open scoped BigOperators
variable {k : ℕ}

theorem multiplierLoad_eq {V : Type*} (weight : V→Block k→ℕ) (a μ : Bits k) (L : Layout k)
    (acts : ∀b,multiply a μ b=L b) : multiplierLoad weight a μ = rearrangedLoad weight L := by
  funext v dest
  exact multiplierLoad_pullback weight a μ L acts v dest

/-- Run the forward-search address lookup with the charge from each actual
residue multiplication and a quadratic allowance for reading and comparing its address. -/
def preimageRun (a μ : Bits k) (dest : Block k) : Option (Bits k) × ℕ :=
  findWithCost (fun b => let m := multiplyRun a μ b
    (decide (blockAddress ((m.1.map Prod.snd).getD 0)=dest),m.2+(k+1)^2)) (words k)

theorem preimageRun_read (a μ : Bits k) (dest : Block k) : (preimageRun a μ dest).1=preimageWord a μ dest :=
  findWithCost_read _ _

private theorem preimageRun_bound (a μ : Bits k) (dest : Block k) :
    (preimageRun a μ dest).2≤2^k*((2^k)^2*((2*k+1)*(5*(2*k+1)+2))+(k+1)^2) := by
  unfold preimageRun
  apply (findWithCost_bound _ _ _ ?_).trans_eq (by rw [length_words])
  intro b _
  exact Nat.add_le_add_right (multiplyRun_work a μ b) _

/-- Materialize a single inverse-address table per multiplier and share it
across all groups and positions. -/
def inverseAddresses (a μ : Bits k) : Vector (Option (Block k) × ℕ) (2^k) :=
  Vector.ofFn fun d => let p := preimageRun a μ d
    (p.1.map blockAddress,p.2+(k+1)^2)

private theorem inverseAddresses_get (a μ : Bits k) (d : Block k) :
    (inverseAddresses a μ).get d =
      ((preimageRun a μ d).1.map blockAddress,(preimageRun a μ d).2+(k+1)^2) := by
  change (inverseAddresses a μ)[d.val] = _
  simp only [inverseAddresses,Vector.getElem_ofFn,Fin.eta]

def bufferedLoad {V : Type*} (weight : V→Block k→ℕ) (table : Vector (Option (Block k) × ℕ) (2^k))
    (v : V) (dest : Block k) : ℕ :=
  match (table.get dest).1 with
  | some old => weight v old
  | none => 0

theorem bufferedLoad_eq {V : Type*} (weight : V→Block k→ℕ) (a μ : Bits k) :
    bufferedLoad weight (inverseAddresses a μ)=multiplierLoad weight a μ := by
  funext v dest
  cases found : preimageWord a μ dest <;>
    simp [bufferedLoad,inverseAddresses_get,preimageRun_read,multiplierLoad,found]

/-- The time contributed by forward multiplications and address comparison
inside all populated entries of a single inverse address table. -/
def inverseTableWork (a μ : Bits k) := ∑ d : Block k, ((inverseAddresses a μ).get d).2

theorem inverseTableWork_bound (a μ : Bits k) :
    inverseTableWork a μ ≤ 2^k*(2^k*((2^k)^2*((2*k+1)*(5*(2*k+1)+2))+(k+1)^2)+(k+1)^2) := by
  let unit := (2^k)^2*((2*k+1)*(5*(2*k+1)+2))+(k+1)^2
  calc
    _ ≤ ∑ _d : Block k, (2^k*unit+(k+1)^2) := Finset.sum_le_sum fun d _=>by
      simpa only [inverseAddresses_get,unit] using Nat.add_le_add_right (preimageRun_bound a μ d) ((k+1)^2)
    _ = _ := by simp [Block,unit,pow_two,Nat.mul_assoc]

variable {V G : Type*} [Fintype V] [DecidableEq V] [Fintype G]

/-- The complete seed scan, starting from the first irreducible word found
by bounded deterministic preprocessing. -/
noncomputable def uniformColonyChoice (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (D cap : ℕ) : Option (Bits k × Nonzero k) := do
  let a ← (measuredLookup k).1
  let winner ← (scanMinimum (uniformColonyScore incoming weight D cap a) (nonzeroWords k)).1
  return (a,winner.1)

theorem uniformColonyChoice_correct (hk : 0<k) (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (adj : V → V → Prop) (spec : ∀u v,u∈incoming v ↔ adj u v) (a B Δ : ℕ)
    (limit : ∀g v i,weight g v i≤B) (degree : ∀v,(next adj v).card≤Δ) (branch : 2≤Δ)
    (scale_pos : 0<2^a*B) (two : 2≤2^a) :
    let D := 32*Nat.clog 2 (2*Δ)
    ∃ (w : Bits k) (μ : Nonzero k) (L : Layout k),
      uniformColonyChoice incoming weight D (2^a*B)=some (w,μ) ∧ Irreducible (candidate w) ∧
      (∀b,multiply w μ.val b=L b) ∧
      (∀ν,uniformColonyScore incoming weight D (2^a*B) w μ≤uniformColonyScore incoming weight D (2^a*B) w ν) ∧
      (colonyCount weight adj a B Δ limit L:ℝ)≤(Fintype.card G:ℝ)*Fintype.card V+
        240*(∑g,∑v,∑i,(weight g v i:ℝ))/(2^a*B:ℕ) := by
  classical
  let D := 32*Nat.clog 2 (2*Δ)
  obtain ⟨w,found,_,_,irreducible⟩ := lookupModulus_spec hk
  let : Fact (Irreducible (candidate w)) := ⟨irreducible⟩
  let e := residueCoordinates w
  let L := fieldMultiplier e
  let Q := uniformColonyScore incoming weight D (2^a*B) w
  have acts (μ : Nonzero k) (b) : multiply w μ.val b=L μ b :=
    (multiply_correct hk _ _ _).trans (fieldMultiplier_apply e μ b).symm
  have exactCost (μ : Nonzero k) : Q μ=colonyCount weight adj a B Δ limit (L μ) := by
    have sameGroup (g : G) : multiplierLoad (weight g) w μ.val=rearrangedLoad (weight g) (L μ) :=
      multiplierLoad_eq _ _ _ _ (acts μ)
    change (∑g,Scan.leafScore incoming (multiplierLoad (weight g) w μ.val) D (2^a*B))=_
    simp_rw [sameGroup]
    exact scannedColonyCount_eq incoming weight adj spec a B Δ branch limit (L μ)
  let : Nonempty (Nonzero k) := Fintype.card_pos_iff.mp (by
    rw [card_nonzero]; have := Nat.one_lt_pow hk.ne' (by decide : 1<2); omega)
  obtain ⟨good,paid⟩ := exists_shared_colonies_family L (fun hj=>fieldMultiplier_pairs e hj)
    weight adj a B Δ limit degree branch scale_pos two
  have upper : (Q good:ℝ)≤(Fintype.card G:ℝ)*Fintype.card V+
      240*(∑g,∑v,∑i,(weight g v i:ℝ))/(2^a*B:ℕ) := by
    rw [exactCost]
    simpa [colonyCount] using paid
  have total := (scanMinimum_spec Q (nonzeroWords k)).2
  cases selected : (scanMinimum Q (nonzeroWords k)).1 with
  | none =>
    simp only [selected] at total
    have mem := mem_nonzeroWords good
    simp [total] at mem
  | some pair =>
    simp only [selected] at total
    obtain ⟨μ,c⟩ := pair
    have least (ν) := total.2 ν (mem_nonzeroWords ν)
    have best (ν) : Q μ≤Q ν := total.1 ▸ least ν
    refine ⟨w,μ,L μ,?_,irreducible,acts μ,best,?_⟩
    · unfold uniformColonyChoice
      rw [(measuredLookup_spec k).1,found]
      change ((scanMinimum Q (nonzeroWords k)).1.bind (fun p => some (w,p.1))) = some (w,μ)
      rw [selected]; rfl
    · rw [←exactCost μ]
      exact (show (Q μ:ℝ)≤Q good by exact_mod_cast best good).trans upper

/-- The concrete finite-host program. Both groups and positions have their
ordinary integer addresses, and all row and score buffers use those addresses. -/
def finiteColonyChoice {groupCount siteCount : ℕ}
    (incoming : Fin siteCount → List (Fin siteCount))
    (weight : Fin groupCount → Fin siteCount → Block k → ℕ) (D cap : ℕ) : Option (Bits k × Nonzero k) := do
  let w ← (measuredLookup k).1
  let score := fun μ : Nonzero k =>
    let table := inverseAddresses w μ.val
    (List.ofFn fun g : Fin groupCount => Scan.FinRows.score incoming (bufferedLoad (weight g) table) D cap).sum
  let winner ← (scanMinimum score (nonzeroWords k)).1
  return (w,winner.1)

theorem finiteColonyChoice_eq {groupCount siteCount : ℕ}
    (incoming : Fin siteCount → List (Fin siteCount))
    (weight : Fin groupCount → Fin siteCount → Block k → ℕ) (D cap : ℕ) :
    finiteColonyChoice incoming weight D cap = uniformColonyChoice incoming weight D cap := by
  simp only [finiteColonyChoice,uniformColonyChoice,bufferedLoad_eq,Scan.FinRows.score_eq_leafScore,List.sum_ofFn]; rfl

/-- Charged work for the modulus search, every inverse-address table, and all
buffer evaluations in the explicitly enumerated multiplier sweep. -/
noncomputable def uniformSearchBudget (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (D cap : ℕ) (w : Bits k) :=
  (measuredLookup k).2 + ((nonzeroWords k).map fun μ => inverseTableWork w μ.val +
    ∑ g, (k+1)*(Scan.readBudget (k:=k) incoming k + Scan.leafVisits
      (Scan.build incoming (bufferedLoad (weight g) (inverseAddresses w μ.val)) D cap k))).sum

private theorem bound_map_sum {S : Type*} (s : List S) (f : S → ℕ) (N : ℕ) (bound : ∀ a,f a≤N) :
    (s.map f).sum≤ s.length*N := by
  induction s with
  | nil => simp
  | cons a s ih => simpa [Nat.succ_mul,Nat.add_comm] using Nat.add_le_add (bound a) ih

omit [DecidableEq V] in
/-- The uniform bound is polynomial in the group size `2^k` and depends
linearly on the number of group–position pairs. -/
theorem uniformSearchBudget_bound (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (D cap Δ : ℕ) (degree : ∀v,(incoming v).length≤Δ) (w : Bits k) :
    uniformSearchBudget incoming weight D cap w ≤
      (2^k)^3*(2*k+1)*(4*k+3) +
      2^k*(2^k*(2^k*((2^k)^2*((2*k+1)*(5*(2*k+1)+2))+(k+1)^2)+(k+1)^2) +
        Fintype.card G*Fintype.card V*(k+1)*(k*(2+Δ)*(2^k)^2+2^k*(k+2^k))) := by
  let depthRate := (k+1)*(Fintype.card V*k*(2+Δ)*(2^k)^2 + Fintype.card V*2^k*(k+2^k))
  let addressRate := 2^k*(2^k*((2^k)^2*((2*k+1)*(5*(2*k+1)+2))+(k+1)^2)+(k+1)^2)
  let one (μ : Nonzero k) := inverseTableWork w μ.val + ∑g,(k+1)*(Scan.readBudget (k:=k) incoming k +
    Scan.leafVisits (Scan.build incoming (bufferedLoad (weight g) (inverseAddresses w μ.val)) D cap k))
  have perSeed (μ) : one μ≤addressRate+Fintype.card G*depthRate := by
    apply Nat.add_le_add (inverseTableWork_bound _ _)
    calc
      _ ≤ ∑ _g : G,depthRate := Finset.sum_le_sum fun g _ => Nat.mul_le_mul_left _
        (Nat.add_le_add (Scan.scan_cost incoming Δ degree) (Scan.leafVisits_bound _))
      _ = _ := by simp
  apply Nat.add_le_add (measuredLookup_spec k).2
  exact ((bound_map_sum (nonzeroWords k) one _ perSeed).trans
    (Nat.mul_le_mul_right _ (nonzeroWords_length k))).trans_eq (by dsimp [depthRate,addressRate]; ring)

omit [DecidableEq V] in
/-- Number of trial visits and group score additions in the finite minimum
scan, in addition to the modulus, address and row table operations. -/
theorem selectionVisits_bound (incoming : V → List V) (weight : G → V → Block k → ℕ)
    (D cap : ℕ) (w : Bits k) :
    (scanMinimum (uniformColonyScore incoming weight D cap w) (nonzeroWords k)).2 +
      (nonzeroWords k).length*Fintype.card G ≤ 2^k*(1+Fintype.card G) := by
  rw [(scanMinimum_spec _ _).1]
  calc
    _ = (nonzeroWords k).length*(1+Fintype.card G) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (nonzeroWords_length k)

end Hierarchy.DescentColonies

end OAI
