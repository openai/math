import OAI.Computability.VPVNP.CompressorRecordsPhaseRecipe
import OAI.Computability.VPVNP.CompressorRefreshMapOperands
import OAI.Computability.VPVNP.CompressorRecordRefreshDemandScan

/-!
# Word coordinates of a refresh argument site

The promoted site has coordinates `(base, port, residual lane)`. The old lane stores the
same port as its high field, so promotion preserves the numerical site ordinal. The old
and new first slots multiply that ordinal by their respective degrees. The external
segment directory instead uses the old port as the segment index within the bundle.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.ArgumentSite

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh
open PhaseRecipe NewSlots
open scoped Fin.CommRing

/-- The port of a promoted site, above the residual-lane field. -/
def portIndex (D : ℕ) (z lanes : Expr) : Expr := (z.div lanes).mod (.lit D)

/-- Block ordinal for the term table. Consecutive divisions recover the base vertex. -/
def blockIndex (D : ℕ) (z lanes : Expr) : Expr :=
  (((z.div lanes).div (.lit D)).mul lanes).add (z.mod lanes)

/-- Compute the first old slot of the site by multiplying its ordinal by the old degree. -/
def oldFirst (D : ℕ) (z : Expr) : Expr := z.mul (.lit D)

/-- Compute the first refreshed slot of the same physical site using the restored degree. -/
def newFirst (d₀ : ℕ) (z : Expr) : Expr := z.mul (.lit d₀)

/-- External segment in the current bundle's source-port order. -/
def segment (D : ℕ) (z j : Expr) : Expr := (oldFirst D z).add j

/-- Address the diagonal segment by using the site's own promoted port as the segment number. -/
def diagonal (D : ℕ) (z lanes : Expr) : Expr := segment D z (portIndex D z lanes)

variable {a g a₀ dH bits : ℕ} (X : State a (a+g)) (p : (X.Base × BitWord g) × Fin (2^a))
  (pub : Fin 5 → W bits) (state : W bits) (m : Memory bits) (z lanes : Expr)

local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "S" => Fintype.card X.Base * 2^a * 2^g * 2^a

/-- Splitting the old binary word preserves the ordinal of the promoted physical site. -/
theorem oldSite_number :
    (X.baseIndex (RefreshMapOperands.oldSite X p).1).val * 2^(a+g) +
      (bitWordFinEquiv (a+g) (RefreshMapOperands.oldSite X p).2).val = (O p).val := by
  change (X.baseIndex p.1.1).val * 2^(a+g) +
    (bitWordFinEquiv (a+g) ((splitBitWord a g).symm ((bitWordFinEquiv a).symm p.2,p.1.2))).val = _
  rw [splitBitWord_number,AddEquiv.apply_symm_apply,Equiv.apply_symm_apply,pow_add,sites_val]
  ring

private theorem first_word (n : ℕ) (hz : (z.eval pub state m).val = (O p).val) :
    (z.mul (.lit n)).eval pub state m = word ((O p).val*n) := by
  apply Fin.ext
  change (z.eval pub state m * (n : W bits)).val = _ % _
  rw [Fin.val_mul,hz,Fin.val_natCast,Nat.mul_mod_mod]

/-- The old outgoing or incoming field list starts at the first slot of the old site. -/
theorem oldFirst_eval (hz : (z.eval pub state m).val = (O p).val) :
    (oldFirst (2^a) z).eval pub state m = IncidenceDirectory.actualPort X (RefreshMapOperands.oldSite X p,0) := by
  rw [oldFirst, first_word X p pub state m z _ hz]
  change word _ = word (((X.baseIndex (RefreshMapOperands.oldSite X p).1).val*2^(a+g)+
    (bitWordFinEquiv (a+g) (RefreshMapOperands.oldSite X p).2).val)*2^a+0)
  rw [oldSite_number,Nat.add_zero]

/-- The new field list starts at the first slot of the promoted site in the selected state. -/
theorem newFirst_eval (P : SlotGraph (Fin (2^a)) dH) (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀)
    (internal : X.Base × BitWord g → Fin (2^a) × Fin dH → ℕ)
    (hz : (z.eval pub state m).val = (O p).val) :
    (newFirst (2^a₀) z).eval pub state m =
      IncidenceDirectory.actualPort (RefreshMapOperands.newState X P hD hd internal) (promotedSites p,0) := by
  rw [newFirst,first_word X p pub state m z _ hz]
  change word _ = word (((p.2.val + 2^a*(X.baseIndex p.1.1).val)*2^g+
    (bitWordFinEquiv g p.1.2).val)*2^a₀+0)
  rw [sites_val,Nat.add_zero,Nat.mul_comm (2^a) _,Nat.add_comm p.2.val]

private theorem unpack {x d : W bits} {hi lo : ℕ} (h : x.val = hi*d.val+lo) (hl : lo < d.val) :
    (BinaryOp.div.eval x d).val = hi ∧ (BinaryOp.mod.eval x d).val = lo := by
  have hd : 0 < d.val := Nat.zero_lt_of_lt hl
  have hq : x.val / d.val = hi := by rw [h,Nat.mul_comm hi,Nat.mul_add_div hd,Nat.div_eq_of_lt hl,Nat.add_zero]
  exact ⟨(Nat.mod_eq_of_lt ((Nat.div_le_self ..).trans_lt x.isLt)).trans hq,
    (Nat.mod_eq_of_lt ((Nat.mod_le ..).trans_lt x.isLt)).trans (h ▸ Nat.mul_add_mod_of_lt hl)⟩

variable (hz : (z.eval pub state m).val = (sites (D := 2^a) X.baseIndex (bitWordFinEquiv g) p).val) (hr : (lanes.eval pub state m).val = 2^g)
  (hDfit : 2^a < 2^bits)

include hz hr in
private theorem read_site :
    ((z.div lanes).eval pub state m).val = (X.baseIndex p.1.1).val*2^a+p.2.val ∧
    ((z.mod lanes).eval pub state m).val = (bitWordFinEquiv g p.1.2).val := by
  apply unpack (d := lanes.eval pub state m) (x := z.eval pub state m)
  · rw [hz,sites_val,hr]
  · rw [hr]; exact (bitWordFinEquiv g p.1.2).isLt

include hz hr hDfit in
private theorem read_base :
    (((z.div lanes).div (.lit (2^a))).eval pub state m).val = (X.baseIndex p.1.1).val ∧
    ((portIndex (2^a) z lanes).eval pub state m).val = p.2.val := by
  have hword : ((2^a : ℕ) : W bits).val = 2^a := Nat.mod_eq_of_lt hDfit
  apply unpack (d := ((2^a : ℕ) : W bits)) (x := (z.div lanes).eval pub state m)
  · rw [hword]; exact (read_site X p pub state m z lanes hz hr).1
  · rw [hword]; exact p.2.isLt

include hz hr hDfit in
theorem portIndex_eval : (portIndex (2^a) z lanes).eval pub state m = word p.2.val := by
  apply Fin.ext
  exact (read_base X p pub state m z lanes hz hr hDfit).2.trans
    (Nat.mod_eq_of_lt (p.2.isLt.trans hDfit)).symm

include hz hr hDfit in
theorem blockIndex_eval : (blockIndex (2^a) z lanes).eval pub state m = word (DemandScan.blocks X p.1).val := by
  apply Fin.ext
  change ((((z.div lanes).div (.lit (2^a))).eval pub state m)*(lanes.eval pub state m) +
    (z.mod lanes).eval pub state m).val = _ % _
  rw [Fin.val_add,Fin.val_mul,(read_base X p pub state m z lanes hz hr hDfit).1,hr,
    (read_site X p pub state m z lanes hz hr).2,Nat.mod_add_mod,DemandScan.blocks_val]

include hz in
theorem segment_eval (jArg : Expr) (j : Fin (2^a)) (hj : (jArg.eval pub state m).val = j.val)
    (fit : S ≤ 2^bits) : (segment (2^a) z jArg).eval pub state m = idWord O fit (p,j) := by
  apply Fin.ext
  change ((z.mul (.lit (2^a))).eval pub state m + jArg.eval pub state m).val = (numbered O (p,j)).val
  rw [first_word X p pub state m z _ hz,Fin.val_add,Fin.val_ofNat,hj,Nat.mod_add_mod]
  rw [← numbered_val]
  exact Nat.mod_eq_of_lt ((numbered O (p,j)).isLt.trans_le fit)

include hz hr hDfit in
theorem diagonal_eval (fit : S ≤ 2^bits) :
    (diagonal (2^a) z lanes).eval pub state m = idWord O fit (p,p.2) :=
  segment_eval X p pub state m z hz _ _ (read_base X p pub state m z lanes hz hr hDfit).2 fit

end CompressorRecords.PortRefresh.ArgumentSite

end VPVNP
end Computability
end OAI
