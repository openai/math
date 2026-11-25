import OAI.Hierarchy.DescentColonyLoads
import OAI.Hierarchy.DescentPackedColonyRun
import OAI.Hierarchy.DescentColonyScorePermutation
import OAI.Hierarchy.DescentResidueMultiplication
import OAI.Hierarchy.DescentResetSuffixSplit

namespace OAI
/-! # Computing reset flags physically on the remixed suffix with the identity multiplier -/
namespace Hierarchy.DescentPlainTerminal.Suffix
open DescentPackedColony DescentColonies DescentGL DescentBinaryField DescentIssuedFallbackPanel
open ThreeFlat.RAM PhysicalProcedure DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
noncomputable section

def identitySeed (k : ℕ) : Bits k := residueCoordinates (0 : Bits k) 1

theorem identityLoad {V : Type*} {k : ℕ} (wt : V→Block k→ℕ) :
    multiplierLoad wt (0 : Bits k) (identitySeed k)=wt := by
  have acts (x : Bits k) : multiply 0 (identitySeed k) x=(LinearEquiv.refl (ZMod 2) (Bits k)) x := by
    by_cases pos : 0<k
    · simp only [multiply_correct pos,identitySeed,LinearEquiv.symm_apply_apply,one_mul,LinearEquiv.apply_symm_apply,LinearEquiv.refl_apply]
    · obtain rfl : k=0:=by omega
      exact funext fun i=>Fin.elim0 i
  funext v x
  rw [multiplierLoad_pullback wt 0 (identitySeed k) (LinearEquiv.refl (ZMod 2) (Bits k)) acts]
  simp [rearrange]

theorem physical_splits {H Δ m c b M w : ℕ} (small : c≤ m) (A : DescentPackedColony.Layout Δ)
    (space : Hardware A H (2^c) (m-c) b M w) (lo : Low A H (2^c) (m-c) b M)
    (roster : Fin H→Fin Δ→Option (Fin H)) (weight : Fin H→Block m→ℕ) (L : DescentGL.Layout m)
    (D cap : ℕ) (fitWeight : ∀v x,weight v x<2^b) (mem : Memory w)
    (pre : Input A roster (fun high v low=>rearrangedLoad weight L v (join small high low)) D cap b M
      0 (identitySeed (m-c)) mem) :
    let rows:=fun high=>Scan.build (incoming (peers roster))
      (fun v low=>rearrangedLoad weight L v (join small high low)) D cap (m-c)
    let run:=passes A H (2^c) M (m-c)
    (ProtocolRAM.program w run).Exec mem (result run mem) (clock run) ∧
      Reads (A.source (m-c)) (fun v high=>cache (rows high) v) M (result run mem) ∧
      clock run≤4+(m-c)*(4+H*chunks (2^c) M*(2*(25+56*Δ)+4)) := by
  dsimp only
  refine ⟨(physical A space mem).1,?_,DescentPackedColony.clock_price A H (2^c) M (m-c)⟩
  have out:=produced A space lo roster (fun high v low=>rearrangedLoad weight L v (join small high low)) D cap
    0 (identitySeed (m-c)) (fun high v low=>fitWeight v ((rearrange L).symm (join small high low))) mem pre (m-c) le_rfl
  have rows_eq (W : Fin (2^c) → Fin H → Block (m-c) → ℕ) :
      DescentPackedColony.stateAt roster W D cap 0 (identitySeed (m-c)) (m-c) =
        fun v high => cache (Scan.build (incoming (peers roster)) (W high) D cap (m-c)) v := by
    funext v high
    exact congrArg (fun wt => cache (Scan.build (incoming (peers roster)) wt D cap (m-c)) v)
      (identityLoad (W high))
  rw [rows_eq] at out
  exact out

end
end Hierarchy.DescentPlainTerminal.Suffix

end OAI
