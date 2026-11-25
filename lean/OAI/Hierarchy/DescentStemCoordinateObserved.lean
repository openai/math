import OAI.Hierarchy.DescentStemCoordinateBook
import OAI.Hierarchy.DescentResetStemObservedInputs

namespace OAI
/-! # The selected-matrix coordinate book supplies three literal numbered-stem registers -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentGL DescentIssuedFallbackPanel DescentResetStemCompactOrder DescentResetStemGroupPlane
open DescentSIMDLookup DescentPackedZip
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {ε q : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
local notation "m" => S.groupWidth k tail i+k
local notation "c" => B.terminals.commonDepth
local notation "r" => m-c
local notation "ng" => S.groupCount (i+1)
local notation "od" => S.resetInputDigits ctl.base ctl.radix i
local notation "nd" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "basis" => B.frame.basis
def coords (H M b : ℕ) : DescentStemCoordinateBook.Shape :=
  ⟨m,k,r,H,ng,M,b⟩

private theorem coords_address (u : Fin ng) (x : Block k) (lo : Block r) :
    (oldCell B x lo u).val=(u.val*2^k+x.val)*2^r+lo.val := by
  change ((nd).symm (u,x)).val*2^r+lo.val=_
  have hi : ((nd).symm (u,x)).val=u.val*2^k+x.val := by
    change x.val+2^k*u.val=u.val*2^k+x.val
    ac_rfl
  rw [hi]

theorem coords_original (H M b : ℕ) (u : Fin ng) (x : Block k) (lo : Block r) :
    (coords B H M b).original basis u x lo=(rearrange basis).symm (oldCell B x lo u) := by
  apply congrArg (rearrange basis).symm
  apply Fin.ext
  change ((u.val*2^k+x.val)*2^r+lo.val)%2^m=_
  rw [←coords_address B u x lo,Nat.mod_eq_of_lt (oldCell B x lo u).isLt]

theorem coords_group (H M b : ℕ) (u : Fin ng) (x : Block k) (lo : Block r) :
    (coords B H M b).value basis 0 x lo u=stemGroupDigit B x lo u := by
  let fit:=B.frame.enough.trans (Nat.sub_le ..)
  let v:=((nd).symm (u,x))
  have digit (j : Block r) : ((od) ((rearrange basis).symm (oldCell B x j u))).1.val=
      ((coords B H M b).original basis u x j).val/2^k :=by
    rw [coords_original];rfl
  have same : high fit (oldCell B x lo u)=v:=by
    apply Fin.ext
    change (v.val*2^r+lo.val)/2^r=v.val
    rw [Nat.mul_comm v.val,Nat.mul_add_div (Nat.two_pow_pos _),Nat.div_eq_of_lt lo.isLt,Nat.add_zero]
  let oldGroup:=fun j : Block r=>((od) ((rearrange basis).symm (oldCell B x j u))).1.val
  let got:=fun j : Block r=>((coords B H M b).original basis u x j).val/2^k
  have equal : oldGroup=got:=funext digit
  change compress (Finset.univ.image got) (got lo)=stemGroupDigit B x lo u
  refine (congrArg (fun f : Block r→ℕ=>compress (Finset.univ.image f) (f lo)) equal.symm).trans ?_
  exact (congrArg (fun hi=>compress (groupDomain od basis fit () hi) (oldGroup lo)) same).symm

theorem coords_fine (H M b : ℕ) (u : Fin ng) (x : Block k) (lo : Block r) :
    (coords B H M b).value basis 1 x lo u=stemFineDigit B x lo u := by
  change ((coords B H M b).original basis u x lo).val%2^k=_
  exact congrArg (fun v : Block m=>v.val%2^k) (coords_original B H M b u x lo)

theorem coords_zero (H M b : ℕ) (u : Fin ng) (x : Block k) (lo : Block r) :
    (coords B H M b).value basis 2 x lo u=stemZeroDigit (S:=S) (i:=i) x u := by
  simp [DescentStemCoordinateBook.Shape.value,DescentStemCoordinateBook.Shape.coarse,stemZeroDigit,coords]

theorem coords_read {H M b Wd : ℕ} (base : ℕ) (saved : Bank) (mem : Memory Wd)
    (chosen : mem saved.base=((DescentExterior.matrixCode basis).val:Word Wd)) (early : saved.Fits Wd base)
    (room : (coords B H M b).endAddress base<2^Wd) (x : Block k) (lo : Block r) :
    let A:=coords B H M b
    let dst:=A.image base mem
    Source (A.src base saved 0 x lo) (fun (_:Fin H) u=>(stemGroupDigit B x lo u:Cell b)) M dst ∧
    Source (A.src base saved 1 x lo) (fun (_:Fin H) u=>(stemFineDigit B x lo u:Cell b)) M dst ∧
    Source (A.src base saved 2 x lo) (fun (_:Fin H) u=>(stemZeroDigit (S:=S) (i:=i) x u:Cell b)) M dst := by
  intro A dst
  have out:=fun t=>(A.read base saved mem basis chosen early room t x lo).2
  have source (t : Fin 3) (value : Fin ng→ℕ) (eqn : ∀g,A.value basis t x lo g=value g) :
      Source (A.src base saved t x lo) (fun (_:Fin H) u=>(value u:Cell b)) M dst := by
    have same : (fun (_ : Fin H) (u : Fin ng)=>(A.value basis t x lo u:Cell b))=
        (fun (_ : Fin H) (u : Fin ng)=>(value u:Cell b)) := by
      funext h u
      exact congrArg (fun z : ℕ=>(z:Cell b)) (eqn u)
    rw [←same]
    exact out t
  exact ⟨source 0 _ (fun u=>coords_group B H M b u x lo),source 1 _ (fun u=>coords_fine B H M b u x lo),
    source 2 _ (fun u=>coords_zero B H M b u x lo)⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
