import OAI.Hierarchy.DescentExteriorService

namespace OAI
/-! # Exact coefficient and common price of the physical exterior verifier -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentExteriorFetch DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {w e j r t : ℕ} (origin : ℕ)
local notation "R" => 2^(j+r)
local notation "k" => j+(j+r)
local notation "first" => start j r t e origin

def guard {F : Type} [CommSemiring F] (n start : ℕ) (m : Memory w) : F :=
  ∏s : Fin 2,∏i : Fin n,(0:F)^(m (start+s.val*n+i.val)).val

theorem guard_value {F : Type} [CommSemiring F] (n start : ℕ) (m : Memory w) :
    guard (F:=F) n start m=
      if ∀s:Fin 2,∀i:Fin n,m (start+s.val*n+i.val)=0 then 1 else 0 := by
  by_cases ok : ∀s:Fin 2,∀i:Fin n,m (start+s.val*n+i.val)=0
  · simp [guard,ok]
  · rw [ite_eq_right ok]
    obtain ⟨s,failed⟩:=not_forall.mp ok
    obtain ⟨i,fail⟩:=not_forall.mp failed
    have nonzero : (m (start+s.val*n+i.val)).val≠0 := fun h=>fail (Fin.ext h)
    exact Finset.prod_eq_zero (Finset.mem_univ s)
      (Finset.prod_eq_zero (Finset.mem_univ i) (zero_pow nonzero))

local notation "n" => e*R
local notation "I" => Fin n

def observed (m : Memory w) (a : Fin e) (v : Plane j r) (b : Fin t) : Bool :=
  let i : I:=finProdFinEquiv (a,rowOrd j r v.2)
  (m (first+2*n+i.val)).val.testBit (pos j t (v.1,b)).val

theorem observed_read (room : 2^j*t≤w) (M : Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) (m : Memory w)
    (rc : Receipt origin M x z m) :
    observed origin m=(fun a=>output (M a) (projected z true a)) := by
  funext a v b
  let i : I:=finProdFinEquiv (a,rowOrd j r v.2)
  let data:=pack (fun l=>output (M a) (projected z true a) (l,v.2))
  have fetched : m (first+2*n+i.val)=(data.val:Word w) := by
    simpa [slab,dest,i,data] using rc.2 i
  change (m (first+2*n+i.val)).val.testBit (pos j t (v.1,b)).val=_
  rw [fetched,Fin.val_cast_of_lt (data.isLt.trans_le (Nat.pow_le_pow_right (by decide) room)),
    Computability.VPVNP.LiveHeader.testBit_wordBits]
  exact pack_bit ..

/-- The field coefficient is one evaluation at the correctly reindexed
literal exterior pins. Every incorrectly proposed native row has a zero
scalar, independently of the characteristic of the working field. -/
theorem contraction {F : Type} [CommSemiring F] (room : 2^j*t≤w) (M : Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (m : (Hidden e j r t→Bool)→Memory w)
    (rc : ∀z,Receipt origin M x z (m z)) (rest : (Fin e→Plane j r→Fin t→Bool)→F) :
    (∑z : Hidden e j r t→Bool,guard (F:=F) n first (m z)*rest (observed origin (m z)))=
      rest (fun a h=>x a (coords j r ((M a).symm ((coords j r).symm h)))) := by
  rw [←sum_headers M x rest]
  apply Finset.sum_congr rfl
  intro z _
  rw [guard_value,observed_read origin room M x z (m z) (rc z)]
  by_cases valid : z=canonical M x
  · simp [(rc z).1.mpr valid,(canonical_iff M x z).mpr valid]
  · rw [ite_eq_right (fun flags=>valid ((rc z).1.mp flags)),
      ite_eq_right (fun phases=>valid ((canonical_iff M x z).mp phases)),zero_mul]

end
end Hierarchy.DescentExteriorShelf

end OAI
