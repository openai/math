import OAI.Hierarchy.DescentPackedWalshAddresses
import OAI.Hierarchy.DescentPackedWalshRead
import OAI.Hierarchy.DescentPackedWalshWeights
import OAI.Hierarchy.DescentDyadicReductionGhosts

namespace OAI
/-! # The native gain/normalization pass supplies the actual first dyadic summation bank -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b c g w : ℕ}

def reduction (H u l c h : ℕ) (hc : 0<c) : Plan := ⟨H,u+l,h,c,hc⟩

def bill (j : ℕ) (lev : Fin H→ℕ) (gain : Fin H→Cell g) (x : Fin H→DescentGL.Bits (u+l)→ℕ)
    (v : Fin H) (d : Fin (2^(u+l))) := if lev v=j then
  (gain v).val*DescentIntegerScale.natCorrelation (x v) ((difference u l).symm d) else 0

theorem seed_of_installed (h base : ℕ) (hc : 0<c) (m : Memory w)
    (a : Fin H→Fin (2^(u+l))→ℕ)
    (lanes : laneBits (u+l) h c=l)
    (old : Installed base (fun v p q=>(a v (groupLane u l (ordinal u p,ordinal l q)):Cell c)) m) :
    (reduction H u l c h hc).Seed a base m := by
  let P := reduction H u l c h hc
  have low : P.laneBits 0 = l := by
    simpa only [P, reduction, Plan.laneBits, Nat.add_zero, laneBits] using lanes
  have count : P.chunks 0 = 2^u := by
    change 2 ^ ((u+l) - P.laneBits 0) = 2^u
    rw [low, Nat.add_sub_cancel]
  have width : P.lanes 0 = 2^l := by rw [Plan.lanes, low]
  change P.Seed a base m
  intro v i
  let group : Fin (2^u) := i.cast count
  let p := (ordinal u).symm group
  have address : (row (H:=H) v p).val = v.val*2^u+i.val := by
    change (ordinal u p).val+2^u*v.val = _
    rw [Equiv.apply_symm_apply]
    simp [group, Nat.mul_comm, Nat.add_comm]
  have location : base+v.val*P.chunks 0+i.val = base+(row (H:=H) v p).val := calc
    _ = base+(v.val*P.chunks 0+i.val) := Nat.add_assoc _ _ _
    _ = base+(v.val*2^u+i.val) := congrArg (fun n : ℕ => base+(v.val*n+i.val)) count
    _ = _ := congrArg (fun n : ℕ => base+n) address.symm
  change m (base+v.val*P.chunks 0+i.val) =
    ((packNat c (P.lanes 0) (fun z => a v ((i.val*P.lanes 0+z) : Fin (2^(u+l))))) : Word w)
  rw [width]
  refine (congrArg m location).trans ((old v p).trans ?_)
  apply congrArg (fun z : Cell (c*2^l) => (z.val : Word w))
  apply congrArg (encode c (2^l))
  funext s
  apply congrArg (fun d : Fin (2^(u+l)) => (a v d : Cell c))
  apply Fin.ext
  have within : i.val*2^l+s.val < 2^(u+l) := by
    simpa only [groupLane_val, group, Fin.val_cast] using (groupLane u l (group,s)).isLt
  simpa only [p, Equiv.apply_symm_apply, groupLane_val, group, Fin.val_cast,
    Nat.cast_add, Nat.cast_mul] using (Fin.val_cast_of_lt within).symm

/-- No multiplication by a truncated word is used in recovering the displayed mean. -/
theorem weighted_values (j : ℕ) (level : Fin H→ℕ) (gain : Fin H→Cell g)
    (rx : Fin H→Cube u→Cube l→Cell b) (x : Fin H→DescentGL.Bits (u+l)→ℕ)
    (returned : ∀v p q,(rx v p q).val=2^(u+l)*
      DescentIntegerScale.natCorrelation (x v) ((DescentWalshPhysical.coordinates (u+l)).symm (addr p q))) :
    (fun v p q=>if level v=j then (((gain v).val*((rx v p q).val/2^(u+l)):ℕ):Cell c) else 0)=
    (fun v p q=>(bill j level gain x v (groupLane u l (ordinal u p,ordinal l q)):Cell c)) := by
  funext v p q
  by_cases same : level v=j
  · simp only [bill,same,ite_true,returned,Nat.mul_div_cancel_left _ (Nat.two_pow_pos _),
      difference_back,Equiv.symm_apply_apply]
  · simp [bill,same]

end
end Hierarchy.DescentPackedWalsh

end OAI
