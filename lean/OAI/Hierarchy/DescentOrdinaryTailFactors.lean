import OAI.Hierarchy.DescentDatedNodeMetadataVolume
import OAI.Hierarchy.DescentOrdinaryFinalTariff

namespace OAI
/-! # Polynomial coefficients of the two ordinary successor publications -/
namespace Hierarchy.DescentDatedNodeMetadata.Chart
noncomputable section
variable (v : DescentDatedNodeMetadata.Chart)

/-- This is the full clock plus seven times the native metadata instruction
count, in units of the occupied host pages. -/
def ordinaryFactor (R K q : ℕ) :=
  let work:=tallyWork K (max q 16)
  ((4+10*v.nodes)+(v.inputClock+v.loopUnits R work))+
    7*(15*(v.nodes+1)+(v.inputNames+v.labelUnits work))

theorem ordinaryFactor_le (R K q : ℕ) :
    v.ordinaryFactor R K q ≤ 100000*(R+1)*(1+(v.blocks+v.nodes+K+q))^4 := by
  let n:=v.blocks+v.nodes+K+q
  let big : DescentDatedNodeMetadata.Chart:={v with blocks:=n,nodes:=n}
  have blocks : v.blocks ≤ n:=by dsimp only [n];omega
  have nodes : v.nodes ≤ n:=by dsimp only [n];omega
  have count : K ≤ n:=by dsimp only [n];omega
  have calls : q ≤ n+16:=by dsimp only [n];omega
  calc
    _ ≤ big.ordinaryFactor R n (n+16) := by
      simp only [ordinaryFactor,inputClock,inputNames,loopUnits,labelUnits,tallyWork,jobs,names,big]
      gcongr
    _ ≤ 100000*(R+1)*(1+n)^4 := by
      have capped : 16 ≤ n+16:=by omega
      simp only [ordinaryFactor,inputClock,inputNames,loopUnits,labelUnits,tallyWork,jobs,names,big,
        max_eq_left capped]
      ring_nf
      omega

end
end Hierarchy.DescentDatedNodeMetadata.Chart

namespace Hierarchy.DescentOrdinaryFinal.Chart
noncomputable section
variable (B : DescentOrdinaryFinal.Chart)

/-- Every operand contributes seven published fields on each block. -/
theorem finalFactor_le (R : ℕ) :
    B.tickUnits R+7*B.textUnits ≤
      100000*(R+1)*(1+(B.layout.blocks+B.layout.nodes+B.layout.operands))^4 := by
  let n:=B.layout.blocks+B.layout.nodes+B.layout.operands
  let big : DescentOrdinaryFinal.Chart:=
    {B with layout:={B.layout with blocks:=n,nodes:=n,operands:=n}}
  have blocks : B.layout.blocks ≤ n:=by dsimp only [n];omega
  have nodes : B.layout.nodes ≤ n:=by dsimp only [n];omega
  have args : B.layout.operands ≤ n:=by dsimp only [n];omega
  calc
    _ ≤ big.tickUnits R+7*big.textUnits := by
      simp only [tickUnits,textUnits,work,passes,outputs,inputs,keys,big]
      gcongr
    _ ≤ 100000*(R+1)*(1+n)^4 := by
      simp only [tickUnits,textUnits,work,passes,outputs,inputs,keys,big]
      ring_nf
      omega

end
end Hierarchy.DescentOrdinaryFinal.Chart

end OAI
