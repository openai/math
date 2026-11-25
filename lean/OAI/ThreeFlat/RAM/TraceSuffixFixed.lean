import OAI.ThreeFlat.RAM.TraceSuffixFit

namespace OAI
/-! # Uniform eleven-parameter ROM with one physical external read -/

namespace ThreeFlat.RAM.TraceSuffixOracle
open Computability.VPVNP.BurstRAM PrivateRAM PhysicalPinsExpr DescriptorExpr
open scoped Fin.CommRing

def Layout.fields (s : Layout) : Fin 11 → ℕ :=
  ![s.paired,s.rawParams,s.rawTable,s.rawCount,s.hWidth,s.description,s.parameters,s.table,
    s.codeBase,s.textOffset,s.textSize]

def Layout.params (s : Layout) : Param → ℕ
  | .advice => s.paired | .teamBits => s.rawParams | .timeBits => s.rawTable
  | .parameterBits => s.rawCount | .chunkBits => s.hWidth | .ticks => s.description
  | .teams => s.parameters | .period => s.table | .finalBlock => s.codeBase
  | .parameterBase => s.textOffset | .templateBase => s.textSize

theorem Layout.fields_at (s : Layout) (p : Param) : s.fields p.index=s.params p := by cases p <;> rfl

def rawAddress (s : Layout) (t : ℕ) : ℕ :=
  if t<s.paired then 0 else if t<s.rawParams then s.description+(t-s.paired)
  else if t<s.rawTable then s.parameters+(t-s.rawParams) else if t<s.rawCount then s.table+(t-s.rawTable)
  else tailBit s.hWidth (t-s.rawTable)

def address (s : Layout) (t : ℕ) : ℕ :=
  if t<s.codeBase then rawAddress s t else if t<s.codeBase+s.textSize then
    s.description+s.textOffset+(t-s.codeBase) else rawAddress s t

theorem address_reads (s : Layout) (m : ℕ → ℕ) (t : ℕ) (zero : m 0=0) (one : m 1=1) :
    m (address s t)=read s m t := by
  have raw_ok : m (rawAddress s t)=raw s m t := by
    unfold rawAddress raw tailBit
    split_ifs <;> simp_all
  by_cases lo : t<s.codeBase <;> by_cases hi : t<s.codeBase+s.textSize <;>
    simp [address,read,lo,hi,raw_ok]

private abbrev E := Formula 1

def rawAddressForm : E :=
  let t : E := .reg 0
  let bit := sub t (A .timeBits)
  let width : E := A .chunkBits
  let tail := eqz (rem (div bit width) (L 11)) (L 3)
    (eqz (rem bit width) (sub width (L 1)) (L 1) (L 0)) (L 0)
  lt t (A .advice) (L 0) (lt t (A .teamBits) (add (A .ticks) (sub t (A .advice)))
    (lt t (A .timeBits) (add (A .teams) (sub t (A .teamBits)))
      (lt t (A .parameterBits) (add (A .period) bit) tail)))

def addressForm : E :=
  lt (.reg 0) (A .finalBlock) rawAddressForm
    (lt (.reg 0) (add (A .finalBlock) (A .templateBase))
      (add (add (A .ticks) (A .parameterBase)) (sub (.reg 0) (A .finalBlock))) rawAddressForm)

def fixedOracle (W K : ℕ) (slots : Fin 11 → Fin K) : Term W K 1 :=
  (Formula.load addressForm).compile (slots ∘ Param.index)

theorem fixedOracle_binds_eq (W K : ℕ) (slots : Fin 11 → Fin K) :
    (fixedOracle W K slots).binds=134 := by
  rw [fixedOracle,Formula.binds_compile]; rfl

theorem fixedOracle_binds (W K : ℕ) (slots : Fin 11 → Fin K) :
    (fixedOracle W K slots).binds≤200 := by rw [fixedOracle_binds_eq]; decide

theorem rawAddress_nat (s : Layout) (W t : ℕ) (m : ℕ → ℕ) :
    rawAddressForm.natural W s.params m (fun _ => t)=rawAddress s t := by
  by_cases a : t<s.paired
  · simp [rawAddressForm,rawAddress,Formula.natural,Layout.params,natTest,a]
  by_cases b : t<s.rawParams
  · simp [rawAddressForm,rawAddress,Formula.natural,Layout.params,natTest,natOp,a,b]
  by_cases c : t<s.rawTable
  · simp [rawAddressForm,rawAddress,Formula.natural,Layout.params,natTest,natOp,a,b,c]
  by_cases d : t<s.rawCount
  · simp [rawAddressForm,rawAddress,Formula.natural,Layout.params,natTest,natOp,a,b,c,d]
  by_cases e : (t-s.rawTable)/s.hWidth%11=3 <;> by_cases f : (t-s.rawTable)%s.hWidth=s.hWidth-1 <;>
    simp [rawAddressForm,rawAddress,tailBit,Formula.natural,Layout.params,natTest,natOp,a,b,c,d,e,f]

theorem address_nat (s : Layout) (W t : ℕ) (m : ℕ → ℕ) :
    addressForm.natural W s.params m (fun _ => t)=address s t := by
  by_cases a : t<s.codeBase <;> by_cases b : t<s.codeBase+s.textSize <;>
    simp [addressForm,address,Formula.natural,Layout.params,rawAddress_nat,natTest,natOp,a,b]

end ThreeFlat.RAM.TraceSuffixOracle

end OAI
