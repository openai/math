import OAI.ThreeFlat.Diagonal.RefreshNodeOwners
import OAI.ThreeFlat.Diagonal.RefreshCursorFrame

namespace OAI
/-! # The two native refresh node-ownership streams -/

namespace ThreeFlat.Diagonal.RefreshNodeOwners

open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.Compression RAM RAM.HeaderScan RAM.PhysicalPinsExpr
open RefreshStageNav RefreshDemandRows CompressorPacking.Native
open scoped Fin.CommRing

def scan {W : ℕ} (cur : Word W) (m : ℕ) (child : Bool) : Scans W :=
  if child then .one ⟨42,43,HeaderScan.closed (expr cur.val m true)⟩
  else .one ⟨44,45,HeaderScan.closed (expr cur.val m false)⟩

def both {W : ℕ} (cur : Word W) (m : ℕ) := (scan cur m true).next (scan cur m false)

theorem both_program {W : ℕ} (cur : Word W) (m : ℕ) :
    ((both cur m).pipeline cur).program=procedure cur m := by
  simp only [both, scan, Bool.false_eq_true, eq_self, ite_true, ite_false,
    Scans.pipeline, Pipeline.thenDo, Pipeline.scan, RefreshNodeOwners.procedure]

variable {W : ℕ} (cur : Word W) (mem : Memory W) (reg : Word W)
local notation "D" => fun _ : Param=>0
local notation "N" => Function.comp Fin.val mem
local notation "U" => Function.const (Fin 1) (Fin.val reg)
local notation "V" => Formula.natural W D N U
local notation "Fit" => Formula.Fits W D N U

private theorem ofit (off : ℕ) (head : (mem cur.val).val+off<2^W) : Fit (field cur.val off) :=
  field_fit cur mem (fun _=>reg) _ head

private theorem addressed {idx lane : Formula 1} (m : ℕ) (fi : Fit idx) (fl : Fit lane)
    (bi : V idx<2^W) (bl : V lane<2^W) (bm : m<2^W) (full : m*V lane<2^W) :
    Fit (RefreshOwnership.childExpr m lane idx) ∧ Fit (RefreshOwnership.ownerExpr m lane idx) := by
  have fv : Fit (.op .div idx lane) := ⟨fi,fl,bi,bl⟩
  have bv : V (.op .div idx lane)<2^W := (Nat.div_le_self ..).trans_lt bi
  have ff : Fit (.op .mul (.lit m) lane) := ⟨trivial,fl,trivial⟩
  have fr : Fit (.op .mod idx (.op .mul (.lit m) lane)) := ⟨fi,ff,bi,full⟩
  have br : V (.op .mod idx (.op .mul (.lit m) lane))<2^W := (Nat.mod_le ..).trans_lt bi
  refine ⟨?_,?_⟩
  · exact ⟨⟨⟨fv,trivial,bv,bm⟩,ff,trivial⟩,
      ⟨⟨fv,trivial,bv,bm⟩,⟨trivial,⟨fi,fl,bi,bl⟩,trivial⟩,trivial⟩,trivial⟩
  · exact ⟨⟨⟨⟨⟨fi,ff,bi,full⟩,trivial,trivial⟩,⟨fr,trivial,br,bm⟩,trivial⟩,fl,trivial⟩,
      ⟨fr,trivial,br,bm⟩,trivial⟩

theorem native (m : ℕ) (b : Bool) (head : (mem cur.val).val+44<2^W) (ports : m<2^W)
    (full : m*N (N cur.val+8)<2^W) :
    (HeaderScan.closed (expr cur.val m b)).eval Fin.elim0 mem (fun _=>reg) =
      ((if b then N (N cur.val+6)+RefreshOwnership.child m (N (N cur.val+8)) (reg.val-N (N cur.val+42))
        else RefreshOwnership.owner m (N (N cur.val+8)) (reg.val-N (N cur.val+44)):ℕ):Word W) := by
  have f (off : ℕ) (h : off≤44) := ofit cur mem reg off (by omega)
  have ix (off : ℕ) (h : off≤44) : Fit (.cut (.reg 0) (field cur.val off)) := ⟨trivial,f off h,reg.isLt,(mem _).isLt⟩
  have ib (off : ℕ) : V (.cut (.reg 0) (field cur.val off))<2^W := (Nat.sub_le _ _).trans_lt reg.isLt
  have fs (off : ℕ) (h : off≤44) := addressed mem reg m (ix off h) (f 8 (by decide)) (ib off)
    (show V (field cur.val 8)<2^W from (mem _).isLt) ports full
  cases b with
  | false => exact closed_read mem (fun _=>reg) (expr cur.val m false) (fs 44 (by decide)).2 (expr_owner cur.val m N U)
  | true => exact closed_read mem (fun _=>reg) (expr cur.val m true) ⟨f 6 (by decide),(fs 42 (by decide)).1,trivial⟩ (expr_child cur.val m N U)


end ThreeFlat.Diagonal.RefreshNodeOwners

end OAI
