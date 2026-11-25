import OAI.Hierarchy.DescentPackedWalshWeightedSeed
import OAI.Hierarchy.DescentPackedWalshWeightROM

namespace OAI
/-! # The two physical transforms supply weighted observations on every true original host -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup DescentPackedWalshReduction ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b c g w B : ℕ}
local notation "k" => u+l

def spectrum (x : Fin H→DescentGL.Bits k→ℕ) (v : Fin H) :=
  shaped (DescentWalshPhysical.numerator (fun a=>(asCube (x v) a:Cell b)))

theorem spectrum_val (x : Fin H→DescentGL.Bits k→ℕ) (bound : ∀v a,x v a≤B)
    (room : 2^(3*k)*B^2<2^b) (v : Fin H) (p : Cube u) (q : Cube l) :
    (spectrum (b:=b) x v p q).val=2^k*DescentIntegerScale.natCorrelation (x v)
      ((DescentWalshPhysical.coordinates k).symm (addr p q)) := by
  apply (DescentWalshPhysical.correlation_word b (asCube (x v)) (addr p q) B
    (fun a=>bound v _) room).trans
  exact congrArg (2^k*·) (corr (x v) (addr p q))

/-- All thresholds at different depths reuse this same spectrum. -/
theorem issued_spectrum (root first squareAt : ℕ) (src start : Memory w) (x : Fin H→DescentGL.Bits k→ℕ)
    (B : ℕ) (bound : ∀v a,x v a≤B) (room : 2^(3*k)*B^2<2^b) (width : smallKey l b≤w)
    (spaces : root+k*span H u l b≤ squareAt) (ends : squareAt+2^(smallKey l b)≤first)
    (limit : sqOffset first H u l+(k+1)*page H u<2^w)
    (fixed : ∀j<first,start j=initial root squareAt H u l b src j)
    (old : Installed first (fun v=>shaped (fun a=>(asCube (x v) a:Cell b))) start) :
    let dst:=numeratorMem root first squareAt H u l b start
    (numeratorCode root first squareAt H u l b w).Exec start dst (numeratorTicks H u l) ∧
    Installed (location (sqOffset first H u l) H u k) (spectrum (b:=b) x) dst ∧
    (∀v,digit b (ordinal l (fun _=>false)).val (dst (location first H u k+
      (row v (fun _ : Fin u => false)).val)).val=∑z,x v z) ∧ ∀i<first,dst i=start i := by
  obtain ⟨run, _, final, saved⟩ := both root first squareAt src start
    (fun v a => (asCube (x v) a : Cell b)) spaces ends limit fixed old
  obtain ⟨_,zero,_,_⟩:=read_measured root first squareAt src start x B bound room width spaces ends limit fixed old
  exact ⟨run,final,zero,saved⟩

theorem real_weight_seed (S : Weight.Header) (h first j : ℕ) (hc : 0<c)
    (mem : Memory w) (level : Fin H→ℕ) (gain : Fin H→Cell g) (x : Fin H→DescentGL.Bits k→ℕ)
    (B : ℕ) (bound : ∀v a,x v a≤B) (precision : 2^(3*k)*B^2<2^b) (lanes : laneBits k h c=l)
    (bnd : ∀v,level v<2^w) (jBound : j<2^w) (room : Weight.Room S first H u l b g w)
    (header : Weight.Fixed S u l b c g H mem)
    (levels : ∀v,mem (S.depth.base+v.val)=(level v:Word w))
    (gains : ∀v,mem (S.gain.base+v.val)=((gain v).val:Word w))
    (num : Installed S.numer.base (spectrum (b:=b) x) mem) :
    let dst:=image first (H*2^u) (Weight.expr S j) mem
    (scan w first (H*2^u) (Weight.expr S j)).Exec mem dst (4+94*(H*2^u)) ∧
      (reduction H u l c h hc).Seed (bill j level gain x) first dst ∧
      (∀z<first,dst z=mem z) ∧ ∀z,first+H*2^u≤z→dst z=mem z := by
  obtain ⟨executed,installed,lo,hi⟩:=Weight.run S first j mem level gain _ bnd jBound room header levels gains num
  rw [weighted_values j level gain _ x (spectrum_val x bound precision)] at installed
  refine ⟨?_,seed_of_installed h first hc _ _ lanes installed,lo,hi⟩
  rw [show 4+94*(H*2^u)=4+(H*2^u)*(2*(Weight.expr S j).work+4) by rw [Weight.tariff,Nat.mul_comm 94]]
  exact executed

end
end Hierarchy.DescentPackedWalsh

end OAI
