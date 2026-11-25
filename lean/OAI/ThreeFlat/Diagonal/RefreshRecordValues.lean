import OAI.ThreeFlat.Diagonal.RefreshKernelRecords
import OAI.ThreeFlat.Diagonal.RefreshStageDirectory

namespace OAI
/-! # Physical meanings of the retained local refresh records -/

namespace ThreeFlat.Diagonal.RefreshStageNav.Records

open Computability.VPVNP.BurstRAM Computability.VPVNP.Compression RAM.PhysicalPinsExpr RAM.MotifRows
open RefreshDemandRows CompressorPacking.Native

variable {W v m t : ℕ} (current : Word W) (data : Param → ℕ) (mem : ℕ → ℕ) (vs : Fin 1 → ℕ)
local notation "V" => Formula.natural W data mem vs

private theorem parts (i : ℕ) {n : ℕ} (j : Fin n) :
    (i*n+j.val)/n=i ∧ (i*n+j.val)%n=j.val := by
  constructor
  · rw [Nat.mul_comm i,Nat.mul_add_div (Nat.zero_lt_of_lt j.isLt),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  · rw [Nat.mul_comm i,Nat.mul_add_mod,Nat.mod_eq_of_lt j.isLt]

def siteId (z : Block v t) (p : Fin m) := (z.1.val*m+p.val)*2^t+(tagOrdinal t z.2).val

theorem siteOrdinal_read (site : Expr) (z : Block v t) (p : Fin m)
    (lanes : info mem current 8=2^t) (atSite : V site=siteId z p) :
    V (siteOrdinal m current site).1=blockId z ∧ V (siteOrdinal m current site).2=p.val := by
  let j := tagOrdinal t z.2
  have h := parts (z.1.val*m+p.val) j
  have f := parts z.1.val p
  change (V site/info mem current 8/m*info mem current 8+V site%info mem current 8=_) ∧
    V site/info mem current 8%m=p.val
  rw [lanes,atSite]
  simpa only [siteId,h.1,h.2,f.1,f.2,blockId,j] using And.intro
    (rfl : blockId z=blockId z) (rfl : p.val=p.val)

theorem splitIndex {d : ℕ} (off s : ℕ) (f : Fin d)
    (address : vs 0=info mem current off+s*d+f.val) :
    V (.op .div (index current off) (.lit d))=s ∧
    V (.op .mod (index current off) (.lit d))=f.val := by
  have h : V (index current off)=s*d+f.val := by
    change vs 0-info mem current off=_
    rw [address]; omega
  change V (index current off)/d=s ∧ V (index current off)%d=f.val
  rw [h]
  exact parts s f

theorem kernel_read (s : ℕ) (f : Fin 5) (a : vs 0=info mem current 34+s*5+f.val) :
    V (kernel current) = (![mem current.val,s,2,1,info mem current 36+s*6] : Fin 5 → ℕ) f := by
  let z := Formula.op .div (index current 34) (.lit 5)
  obtain ⟨site,field⟩ := splitIndex current data mem vs 34 s f a
  dsimp only [kernel]
  rw [rowAt_hit W data mem vs _ _ f field]
  fin_cases f <;> first | rfl | exact site | exact congrArg (fun j => info mem current 36+j*6) site

theorem motif_read (z : Block v t) (p : Fin m) (K : ℕ) (f : Fin 6)
    (lanes : info mem current 8=2^t) (a : vs 0=info mem current 36+siteId z p*6+f.val) :
    let b := blockId z
    let c := info mem current 2+b*3
    V (motif current m K) =
      (![b,info mem current 1+b*K,mem (c+1),mem c,0,2^p.val] : Fin 6 → ℕ) f := by
  let site := Formula.op .div (index current 36) (.lit 6)
  let b := (siteOrdinal m current site).1
  let party := (siteOrdinal m current site).2
  obtain ⟨siteEq,field⟩ := splitIndex current data mem vs 36 (siteId z p) f a
  obtain ⟨bEq,pEq⟩ := siteOrdinal_read current data mem vs site z p lanes siteEq
  have mask : V (rowAt m (fun j => .lit (2^j.val)) party)=2^p.val :=
    rowAt_hit W data mem vs _ _ p pEq
  dsimp only [motif]
  rw [rowAt_hit W data mem vs _ _ f field]
  fin_cases f <;> first
  | rfl
  | exact bEq
  | exact mask
  | exact congrArg (fun b => info mem current 1+b*K) bEq
  | exact congrArg (fun b => mem ((info mem current 2+b*3)+1)) bEq
  | exact congrArg (fun b => mem (info mem current 2+b*3)) bEq

theorem halfHeader_read (d s : ℕ) (f : Fin 2) (a : vs 0=info mem current 38+s*2+f.val) :
    V (halfHeader current d) = (![2*d,info mem current 40+s*(8*d)] : Fin 2 → ℕ) f := by
  obtain ⟨site,field⟩ := splitIndex current data mem vs 38 s f a
  change (if decide (V (.op .mod (index current 38) (.lit 2))=0) then 2*d
    else info mem current 40+V (.op .div (index current 38) (.lit 2))*(8*d))=_
  rw [site,field]
  fin_cases f <;> rfl

end ThreeFlat.Diagonal.RefreshStageNav.Records

end OAI
