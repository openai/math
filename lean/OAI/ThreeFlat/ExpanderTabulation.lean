import OAI.Computability.BinPacking.Expanders.ExpanderTableEnumeration

namespace OAI
/-! # Tabulating dyadic routing graphs from fixed-size seeds

Each square-zigzag step forms a table using a mixed-radix vertex index.
The `stepLookup` formula reads the preceding table twice and the fixed
cloud table twice for each new row. The sum of the row counts, including
the seed table, is linear in the number of rows in the final table.
-/

namespace ThreeFlat.RouteUnits

open BinPackingGames.Foundations.PCP ExpanderTables SpectralReturn

def seededOrder (v growth : ℕ) : ℕ → ℕ
  | 0 => v
  | n + 1 => seededOrder v growth n * growth

theorem seededOrder_eq (v growth n : ℕ) : seededOrder v growth n = v * growth ^ n := by
  induction n with
  | zero => simp [seededOrder]
  | succ n ih => simp [seededOrder, ih, pow_succ, Nat.mul_assoc]

/-- The only arbitrary tables in this recursion are its two fixed inputs. -/
def seededTable {v d : ℕ} (seed : Table v (d * d))
    (cloud : Table ((d * d) * (d * d)) d) :
    (n : ℕ) → Table (seededOrder v ((d * d) * (d * d)) n) (d * d)
  | 0 => seed
  | n + 1 => step (seededTable seed cloud n) cloud

theorem seededTable_certificate {v d : ℕ} [NeZero v] [NeZero d]
    (seed : Table v (d * d)) (cloud : Table ((d * d) * (d * d)) d)
    (hs : SpectralCertificate (graph seed) (1 / 2 : ℝ))
    (hc : SpectralCertificate (graph cloud) (1 / 100 : ℝ)) (n : ℕ) :
    SpectralCertificate (graph (seededTable seed cloud n)) (1 / 2 : ℝ) := by
  induction n with
  | zero => exact hs
  | succ n ih =>
    have hd := Nat.mul_ne_zero (NeZero.ne d) (NeZero.ne d)
    let : NeZero (seededOrder v ((d * d) * (d * d)) n) := ⟨by
      rw [seededOrder_eq]
      exact Nat.mul_ne_zero (NeZero.ne v) (pow_ne_zero _ (Nat.mul_ne_zero hd hd))⟩
    exact step_certificate _ _ ih hc

/-- The cumulative number of rotation rows enumerated up to level `n`. -/
def seededRowCount (v degree : ℕ) : ℕ → ℕ
  | 0 => v * degree
  | n + 1 => seededRowCount v degree n + seededOrder v (degree * degree) (n + 1) * degree

theorem seededRowCount_le {v degree : ℕ} (hdeg : 2 ≤ degree) (n : ℕ) :
    seededRowCount v degree n ≤ 2 * (seededOrder v (degree * degree) n * degree) := by
  have hgr : 2 ≤ degree * degree := hdeg.trans (Nat.le_mul_of_pos_right _ (by omega))
  induction n with
  | zero => simp only [seededRowCount, seededOrder]; omega
  | succ n ih =>
    let prev := seededOrder v (degree * degree) n * degree
    have hg : 2 * prev ≤ seededOrder v (degree * degree) (n + 1) * degree := by
      dsimp [prev, seededOrder]
      calc
        _ ≤ (degree * degree) * (seededOrder v (degree * degree) n * degree) :=
          Nat.mul_le_mul_right _ hgr
        _ = _ := by ring
    change seededRowCount v degree n ≤ 2 * prev at ih
    rw [seededRowCount]
    omega

abbrev dyadicPortDegree := Expanders.baseDegree * Expanders.baseDegree

private theorem dyadic_growth : dyadicPortDegree * dyadicPortDegree = 2 ^ 448 := by
  change (((2 : ℕ) ^ 16) ^ 7 * ((2 : ℕ) ^ 16) ^ 7) *
    (((2 : ℕ) ^ 16) ^ 7 * ((2 : ℕ) ^ 16) ^ 7) = _
  rw [← sq, ← sq, ← pow_mul, ← pow_mul, ← pow_mul]

def seedIndex (k : ℕ) : Fin 448 := ⟨k % 448, Nat.mod_lt _ (by decide)⟩

theorem dyadicTable_order (k : ℕ) :
    seededOrder (2 ^ (seedIndex k).val) (dyadicPortDegree * dyadicPortDegree) (k / 448) =
      2 ^ k := by
  rw [seededOrder_eq, dyadic_growth, ← pow_mul, ← pow_add]
  exact congrArg (fun n : ℕ => 2 ^ n) (Nat.mod_add_div k 448)

/-- The routing table is built bottom-up from one of 448 fixed seed tables
and a fixed cloud. `finCongr` reuses the numeric row labels at the final order. -/
def dyadicTable (seed : (i : Fin 448) → Table (2 ^ i.val) dyadicPortDegree)
    (cloud : Table (dyadicPortDegree * dyadicPortDegree) Expanders.baseDegree) (k : ℕ) :
    Table (2 ^ k) dyadicPortDegree :=
  ofGraph (GraphTransport.reindex (graph (seededTable (seed (seedIndex k)) cloud (k / 448)))
    (finCongr (dyadicTable_order k)) (Equiv.refl _))

theorem dyadicTable_certificate (seed : (i : Fin 448) → Table (2 ^ i.val) dyadicPortDegree)
    (cloud : Table (dyadicPortDegree * dyadicPortDegree) Expanders.baseDegree)
    (hs : ∀ i, SpectralCertificate (graph (seed i)) (1 / 2 : ℝ))
    (hc : SpectralCertificate (graph cloud) (1 / 100 : ℝ)) (k : ℕ) :
    SpectralCertificate (graph (dyadicTable seed cloud k)) (1 / 2 : ℝ) := by
  let : NeZero Expanders.baseDegree := ⟨by decide⟩
  rw [dyadicTable, graph_ofGraph]
  exact GraphTransport.reindex_spectralCertificate _ _ _ _
    (seededTable_certificate _ _ (hs _) hc _)

/-- All square-zigzag levels combined enumerate at most twice the final row count. -/
theorem dyadicTable_row_bound (k : ℕ) :
    seededRowCount (2 ^ (seedIndex k).val) dyadicPortDegree (k / 448) ≤
      2 * (2 ^ k * dyadicPortDegree) := by
  rw [← dyadicTable_order k]
  exact seededRowCount_le (by decide) _

/-- A finite choice of base tables suffices for the entire dyadic family. -/
theorem exists_dyadicTable_seeds :
    ∃ seed : (i : Fin 448) → Table (2 ^ i.val) dyadicPortDegree,
    ∃ cloud : Table (dyadicPortDegree * dyadicPortDegree) Expanders.baseDegree,
      (∀ i, SpectralCertificate (graph (seed i)) (1 / 2 : ℝ)) ∧
      SpectralCertificate (graph cloud) (1 / 100 : ℝ) := by
  classical
  have small (i : Fin 448) : ∃ T : Table (2 ^ i.val) dyadicPortDegree,
      SpectralCertificate (graph T) (1 / 2 : ℝ) := by
    obtain ⟨g, hg⟩ := Expanders.exists_generators i.val (2 ^ 14) (by have := i.isLt; omega)
    let G := CayleySpectral.cayleyGraph (CayleySpectral.powerGenerators g 14)
    have cert : SpectralCertificate G (1 / 2 : ℝ) := by
      apply CayleySpectral.cayley_spectralCertificate _ _ (by norm_num) (by norm_num)
      intro s hs
      exact (CayleySpectral.power_eigenvalue_bound g (1 / 2) (by norm_num) hg 14 s hs).trans
        (by norm_num)
    let ev := Fintype.equivFinOfCardEq (show
        Fintype.card (BinPackingGames.Foundations.Hastad.Cube (Fin i.val)) = 2 ^ i.val by
      simp [BinPackingGames.Foundations.Hastad.Cube])
    let ep := Fintype.equivFinOfCardEq (show
        Fintype.card (Fin 14 → Fin (4 * 2 ^ 14)) = dyadicPortDegree by
      simp only [Fintype.card_fun, Fintype.card_fin]
      norm_num [dyadicPortDegree, Expanders.baseDegree, Expanders.basePower, Expanders.initialDegree])
    refine ⟨ofGraph (GraphTransport.reindex G ev ep), ?_⟩
    rw [graph_ofGraph]
    exact GraphTransport.reindex_spectralCertificate _ _ _ _ cert
  choose seed cert using small
  obtain ⟨cloud, hc⟩ := exists_base_table
  exact ⟨seed, cloud, cert, hc⟩

end ThreeFlat.RouteUnits

end OAI
