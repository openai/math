import OAI.Hierarchy.DescentPackedWalshNumerator
import OAI.Hierarchy.DescentIntegerScale

namespace OAI
/-! # Genuine measured correlation and traffic total in the true forward/square/inverse output -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b w : ℕ}
local notation "m" => u+l
local notation "Q" => DescentWalshPhysical.coordinates

def asCube (x : DescentGL.Bits m→ℕ) : Cube m→ℕ := fun a=>x ((Q m).symm a)

theorem corr (x : DescentGL.Bits m→ℕ) (d : Cube m) :
    (∑a : Cube m,asCube x a*asCube x (fun j=>(a j).xor (d j)))=
      DescentIntegerScale.natCorrelation x ((Q m).symm d) := by
  rw [←(Q m).sum_comp]
  apply Finset.sum_congr rfl
  intro i _
  change x ((Q m).symm (Q m i))*x ((Q m).symm (fun j=>(Q m i j).xor (d j)))=x i*x (i+(Q m).symm d)
  have add:=DescentWalshPhysical.coordinates_add i ((Q m).symm d)
  simp only [Equiv.apply_symm_apply] at add
  simp only [←add,Equiv.symm_apply_apply]

theorem read_measured (root first table : ℕ) (src start : Memory w)
    (x : Fin H→DescentGL.Bits m→ℕ) (B : ℕ) (bound : ∀v a,x v a≤B)
    (numRoom : 2^(3*m)*B^2<2^b) (payload : smallKey l b≤w)
    (tables : root+m*span H u l b≤table) (shelfEnds : table+2^(smallKey l b)≤first)
    (limit : sqOffset first H u l+(m+1)*page H u<2^w)
    (fixed : ∀j<first,start j=initial root table H u l b src j)
    (old : Installed first (fun v=>shaped (fun a=>(asCube (x v) a:Cell b))) start) :
    let dst:=numeratorMem root first table H u l b start
    (numeratorCode root first table H u l b w).Exec start dst (numeratorTicks H u l) ∧
      (∀v,
        digit b (ordinal l (fun _=>false)).val (dst (location first H u m+(row v (fun _ : Fin u=>false)).val)).val =
          ∑a,x v a) ∧
      (∀v p q,digit b (ordinal l q).val
        (dst (location (sqOffset first H u l) H u m+(row v p).val)).val=
          2^m*DescentIntegerScale.natCorrelation (x v) ((Q m).symm (addr p q))) ∧
      (∀i<first,dst i=start i) := by
  obtain ⟨run,firstRead,lastRead,saved⟩:=both root first table src start _ tables shelfEnds limit fixed old
  refine ⟨run,?_,?_,saved⟩
  · intro v
    rw [firstRead.bitValue payload]
    have zero : addr (fun _ : Fin u=>false) (fun _ : Fin l=>false)=(fun _=>false) := by
      funext i
      obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective i
      unfold addr
      rw [Equiv.symm_apply_apply]
      cases j <;> rfl
    simp only [shaped,zero,DescentWalshPhysical.transform_zero]
    rw [←Nat.cast_sum,Fin.val_cast_of_lt]
    · exact ((Q m).sum_comp (fun a=>asCube (x v) a)).symm.trans (by simp [asCube])
    · have ss : (∑a : Cube m,asCube (x v) a)≤2^m*B := by
        simpa [asCube,Cube,Fintype.card_fun] using Finset.sum_le_sum (s:=Finset.univ) (fun a _=>bound v ((Q m).symm a))
      by_cases hB : B=0
      · subst B
        rw [Nat.mul_zero] at ss
        exact ss.trans_lt (Nat.two_pow_pos b)
      · have power : 2^m≤2^(3*m):=Nat.pow_le_pow_right (by decide) (by omega)
        have b2 : B≤B^2:=by rw [pow_two];nlinarith only [Nat.mul_le_mul_left B (show 1≤B by omega)]
        exact ss.trans_lt ((Nat.mul_le_mul power b2).trans_lt numRoom)
  · intro v p q
    rw [lastRead.bitValue payload]
    exact (DescentWalshPhysical.correlation_word b (asCube (x v)) (addr p q) B (fun a=>bound v _) numRoom).trans
      (congrArg (2^m*·) (corr (x v) (addr p q)))

end
end Hierarchy.DescentPackedWalsh

end OAI
