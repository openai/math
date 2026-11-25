import OAI.Computability.NearSquareRoot.InterchangeROMRepairPR
import OAI.Computability.NearSquareRoot.InterchangeROMRepairApply
import OAI.Computability.NearSquareRoot.InterchangeROMRepairReindex
import OAI.Computability.NearSquareRoot.ScheduleGeneratorCharacteristic

/-! # Effective selection of all ground coefficients in a binary interchange -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Raw

open Sizes

def rowCount (m : ℕ) := rows m * basisCount m
def checkCount (m : ℕ) := checkRows m * basisCount m
def halfCode (p : ℕ) := (p+2)/2

theorem primrec_rowCount : Primrec rowCount := Primrec.nat_mul.comp primrec_rows primrec_basisCount

theorem primrec_checkCount : Primrec checkCount := Primrec.nat_mul.comp primrec_checkRows primrec_basisCount

theorem primrec_halfCode : Primrec halfCode :=
  Primrec.nat_div.comp (Primrec.nat_add.comp Primrec.id (.const 2)) (.const 2)

theorem halfCode_spec {p : ℕ} (prime : (p+1).Prime) (odd : 2 < p+1) :
    2 * (halfCode p : ZMod (p+1)) = 1 := by
  have hb := prime.eq_two_or_odd.resolve_left (by omega)
  have h : 2 * halfCode p = (p+1)+1 := by unfold halfCode; omega
  calc
    _ = ((2 * halfCode p : ℕ) : ZMod (p+1)) := by push_cast; rfl
    _ = (((p+1)+1 : ℕ) : ZMod (p+1)) := by rw [h]
    _ = 1 := by rw [Nat.cast_add_one, ZMod.natCast_self,zero_add]

/-- A finite ground tape of the prescribed computable size exists for every legal parameter. -/
theorem exists_valid {p m : ℕ} (prime : (p+1).Prime) (odd : 2 < p+1) (hm : 2 ≤ m) :
    ∃ t, Valid p (rowCount m) (checkCount m) m (pencilOrder m) (halfCode p) t := by
  let : Fact (p+1).Prime := ⟨prime⟩
  obtain ⟨t,ht⟩ := exists_fin_accepted hm (halfCode p : ZMod (p+1)) (halfCode_spec prime odd)
  exact ⟨encode t, (valid_iff ..).mpr (by simpa [rowCount,checkCount] using ht)⟩

/-- All-width action of any successful coded candidate, including a candidate found independently. -/
theorem valid_runs {p m : ℕ} {t : Tape} (prime : (p+1).Prime) (odd : 2 < p+1)
    (ht : Valid p (rowCount m) (checkCount m) m (pencilOrder m) (halfCode p) t)
    {C : Type} [LinearOrder C] (x : Fin (rowCount m) → Stream m C (ZMod (p+1)))
    (i : Fin (rowCount m)) (a : SwapSpectrum.Address (Fin m) C) :
    run (decode p (rowCount m) (checkCount m) m t) (pencilOrder m)
      (halfCode p : ZMod (p+1)) (halfCode_spec prime odd) x i a = x i (SwapRepair.swapAll a) :=
  run_correct _ _ _ _ ((valid_iff ..).mp ht) _ _ _

/-- Read the contiguous ground matrices in the product order used by the packed predictor. -/
def decodePacked (p m : ℕ) (t : Tape) :
    Spec (ZMod (p+1)) (Fin (rows m) × Fin (basisCount m))
      (Fin (checkRows m) × Fin (basisCount m)) m :=
  (decode p (rowCount m) (checkCount m) m t).reindex finProdFinEquiv finProdFinEquiv

/-- Verified coefficients remain valid in native clock-row and basis-coordinate order. -/
theorem packed_accepts {p m : ℕ} {t : Tape}
    (ht : Valid p (rowCount m) (checkCount m) m (pencilOrder m) (halfCode p) t) :
    accepts (decodePacked p m t) (pencilOrder m) (halfCode p : ZMod (p+1)) = true :=
  accepts_reindex _ finProdFinEquiv finProdFinEquiv _ _ ((valid_iff ..).mp ht)

/-- A single computable compiler for every pair of integer parameters. -/
theorem exists_compiler :
    ∃ tape : ℕ → ℕ → Tape, Computable₂ tape ∧ ∀ p m,
      (p+1).Prime → 2 < p+1 → 2 ≤ m →
      Valid p (rowCount m) (checkCount m) m (pencilOrder m) (halfCode p) (tape p m) := by
  let good (p : ℕ) := (p+1).Prime ∧ 2 < p+1
  have hg : PrimrecPred good := (Generator.primrecPrime.comp Primrec.succ).and
    (Primrec.nat_lt.comp (Primrec.const 2) Primrec.succ)
  let pp (n : ℕ) := if good n.unpair.1 then n.unpair.1 else 2
  let mm (n : ℕ) := if 2 ≤ n.unpair.2 then n.unpair.2 else 2
  have hp : Primrec pp := Primrec.ite (hg.comp (Primrec.fst.comp Primrec.unpair))
    (Primrec.fst.comp Primrec.unpair) (Primrec.const 2)
  have hm : Primrec mm := Primrec.ite
    (Primrec.nat_le.comp (Primrec.const 2) (Primrec.snd.comp Primrec.unpair))
    (Primrec.snd.comp Primrec.unpair) (Primrec.const 2)
  have hex (n : ℕ) := by
    have pg : good (pp n) := by
      unfold pp
      split
      · assumption
      · decide
    have mg : 2 ≤ mm n := by unfold mm; split <;> omega
    exact exists_valid pg.1 pg.2 mg
  obtain ⟨v,hv,hgood⟩ := exists_computable_tape pp (rowCount ∘ mm) (checkCount ∘ mm)
    mm (pencilOrder ∘ mm) (halfCode ∘ pp) hp.to_comp
    (primrec_rowCount.comp hm).to_comp (primrec_checkCount.comp hm).to_comp hm.to_comp
    (primrec_pencilOrder.comp hm).to_comp (primrec_halfCode.comp hp).to_comp hex
  refine ⟨fun p m => v (Nat.pair p m), hv.comp₂ Primrec₂.natPair.to_comp, ?_⟩
  intro p m prime odd big
  have hp2 : 2 ≤ p := by omega
  simpa [pp, mm, good, prime, hp2, big] using hgood (Nat.pair p m)

end InterchangeROMRepair.Raw

end NearSquareRoot
end Computability
end OAI
