import OAI.Hierarchy.DescentSeedScalarSelectors
import OAI.Hierarchy.DescentSeedBoundaryPattern
import OAI.Hierarchy.DescentPrimitivePaletteLabels
import OAI.Hierarchy.DescentEpochTagKeys
import OAI.Hierarchy.DescentSeedTokenPlan
import OAI.Hierarchy.DescentPackedCensusRAM

namespace OAI
/-! # The physical dictionary, classes and validity mask for the seed census -/
namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot DescentInitialHost DescentSixParty DescentPrimitivePalette DescentKernelHistory DescentEpochTagKeys
open DescentPhysicalSplit DescentSIMDLookup Catalyst CorrectionBatch Computability.BorderVNP.Crossing
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat Diagonal
open scoped Classical BigOperators Fin.CommRing
noncomputable section
set_option quotPrecheck false

variable {F : Type} [Field F] {k p R s w : ℕ} (X : Approximation F k p)
local notation "N" => X.network.copyGraph
local notation "H" => Fintype.card (Old X)
local notation "d" => digitsNeeded s
local notation "B" => hubbed N

private theorem site_arity (v : Old X) : seedArity B (.inl v) ≤ 3 := by
  have e := Fintype.card_congr (seedPattern B (hub_unit N (physical_output X).1) (.inl v))
  simp only [Fintype.card_fun,Fintype.card_bool,Fintype.card_fin] at e
  have small : 2^(seedArity B (.inl v)) ≤ 2^3 :=
    e.ge.trans (hub_patterns_card N (physical_output X).1 v _)
  exact (Nat.pow_le_pow_iff_right (by decide : 1<2)).mp small

/-- The only site-dependent ROM selector records the ordering of the eight old pattern slots. -/
def plan (v : Old X) : Plan :=
  ⟨⟨seedArity B (.inl v),Nat.lt_succ_of_le (site_arity X v)⟩,
    fun pat=>DescentSeedRoot.code X (v:=v)
      ((seedPattern B (hub_unit N (physical_output X).1) (.inl v)).symm pat)⟩

def entry (s : ℕ) (a : Plan) (input : Cell (digitsNeeded s*8)) : Cell (roleBits s) :=
  let t : CensusTag s:=⟨a.1,fun pat=>Fin.ofNat (s+1) (((encode (digitsNeeded s) 8).symm input (a.2 pat)).val)⟩
  ⟨((census s).store (.inl t)).val,((census s).store (.inl t)).isLt.trans (Nat.lt_log2_self ..)⟩

end
end Hierarchy.DescentPackedSeed.Primitive

namespace Hierarchy.DescentPackedSeed.Primitive
open DescentSeedRoot DescentInitialHost DescentSixParty DescentPrimitivePalette DescentEpochTagKeys DescentSIMDLookup Catalyst
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {F : Type} [Field F] {k p w s R : ℕ} (X : Approximation F k p)

def plans := Fintype.equivFin Plan
def offset (s M : ℕ) (P : Plan) := (plans P).val*2^(digitsNeeded s*8*M)

def dictWord (s M : ℕ) (z : Fin (cols s M)) : ℕ :=
  let pp:Fin (Fintype.card Plan)×Cell (digitsNeeded s*8*M):=finProdFinEquiv.symm z
  (table (entry s (plans.symm pp.1)) pp.2).val

structure Tape where
  source : Bank
  dict : Bank
  classes : Bank
  mask : Bank

def spread (T : Tape) : Expr :=
  .op .mask (.lookup T.dict (.op .add (.lookup T.classes .row) (.lookup T.source .row))) (.lookup T.mask .row)

theorem work (T : Tape) : (spread T).work=28 := rfl

def tape (start H R M s src : ℕ) : Tape :=
  let n:=H*chunks R M;let size:=cols s M
  ⟨⟨src,Nat.clog 2 n⟩,⟨start,Nat.clog 2 size⟩,⟨start+size,Nat.clog 2 n⟩,⟨start+size+n,Nat.clog 2 n⟩⟩

def shelf (start n : ℕ) (f : Fin n→ℕ) (m : Memory w) : Memory w :=
  fun a=>if live : start≤a∧a<start+n then (f ⟨a-start,by omega⟩:Word w) else m a

def sitePlan (v : Fin (Fintype.card (Old X))) := plan X ((Fintype.equivFin _).symm v)

def endAddr (start H R M s : ℕ) := start+cols s M+2*(H*chunks R M)

structure Room (T : Tape) (out : ℕ) (a b M H R s w : ℕ) : Prop where
  fits : ∀B∈[T.source,T.mask,T.classes,T.dict],B.Fits w out
  rows : ∀B∈[T.source,T.mask,T.classes],H*chunks R M≤B.size
  dict : cols s M≤T.dict.size
  output : out+H*chunks R M<2^w
  result : b*M≤w

namespace Spaced
variable {laneCount : ℕ}
local notation "H" => Fintype.card (Old X)
local notation "b" => roleBits s
local notation "rows₀" => H*chunks R laneCount

def stamp (start : ℕ) (m : Memory w) :=
  let size:=cols s laneCount
  let first:=shelf start size (dictWord s laneCount) m
  let middle:=shelf (start+size) rows₀ (fun i=>offset s laneCount (sitePlan X ((row H R laneCount).symm i).1)) first
  shelf (start+size+rows₀) rows₀ (fun i=>maskWord b laneCount R ((row H R laneCount).symm i).2.val) middle

end Spaced

theorem role_bound (s : ℕ) : roleBits s≤16*digitsNeeded s := by
  have positive : 0<digitsNeeded s:=Nat.zero_lt_succ _
  have:=role_bound_short s
  omega

theorem result_fit (w s : ℕ) : roleBits s*pieces w s≤w := by
  let d:=digitsNeeded s
  have fit:=lanes_fit w (8*d)
  have h:=Nat.mul_le_mul_right (pieces w s) (role_bound s)
  change roleBits s*pieces w s≤w
  calc _ ≤16*d*pieces w s:=h
       _=(pieces w s*(8*d))*2:=by ring
       _≤w:=by change (lanes w (8*d)*(8*d))*2≤_;exact (Nat.le_div_iff_mul_le (by decide : 0<2)).mp fit

end
end Hierarchy.DescentPackedSeed.Primitive

end OAI
