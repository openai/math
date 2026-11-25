import OAI.Hierarchy.DescentDatedMouthBounds
import OAI.Hierarchy.DescentOperandVectorArena

namespace OAI
/-! All native addresses in the three returned mouth fields, including the rounded
tail banks that can be empty on some ordinary dates. -/
namespace Hierarchy.DescentOrdinaryMouthReturn.Layout
open DescentOrdinaryBorn DescentSIMDLookup DescentVectorBookReshape ProtocolRAM
noncomputable section
variable (L : Layout)

private theorem round (n : ℕ) : 2^Nat.clog 2 n≤2*(n+2) :=by
  cases e:Nat.clog 2 n with
  | zero=>simp only [pow_zero]; omega
  | succ j=>
    have bound:=Nat.pow_lt_of_lt_clog (show j<Nat.clog 2 n by omega)
    rw [pow_succ];omega

theorem extent_any (floor h : ℕ) (hr : 0<L.radix) (pitch : L.B.lanes=L.lanes*L.radix)
    (same : L.B.groups=L.groups*L.radix) (chip : (L.B.chipBits*1+L.B.chipBits)*L.B.lanes≤h/2)
    (packed : (L.bits*L.radix)*L.lanes≤h/2) :
    L.endAddress floor≤floor+(16+4*L.B.fields)+(2*(1+L.B.fields)+3*L.radix)*2^(h/2)+
      (2*L.B.fields+2*L.pages*L.lows+5*L.pages*L.lows*L.radix+2*L.lows)*(L.B.hosts*chunks L.groups L.lanes) :=by
  let rows₀:=L.B.hosts*chunks L.groups L.lanes
  let src:=L.pages*DescentVectorBookReshape.sourceWords L.B.hosts L.lows L.groups L.lanes
  let dst:=L.pages*rows L.B.hosts L.lows L.groups L.radix L.lanes
  let dir:=dictionaryWords L.radix L.bits L.lanes
  have chipTable:=Nat.pow_le_pow_right (n:=2) (by decide) chip
  have dirTable : dir≤L.radix*2^(h/2):=Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) packed)
  have oldRows : L.B.rows=rows₀:=by
    unfold DescentOrdinaryBorn.Chart.rows rows₀
    rw [pitch,same]
    by_cases hm : 0 < L.lanes
    · rw [chunks_group _ _ _ hm hr]
    · have absent : L.lanes=0 := by omega
      change L.B.hosts*((L.groups*L.radix+L.lanes*L.radix-1)/(L.lanes*L.radix)) =
        L.B.hosts*((L.groups+L.lanes-1)/L.lanes)
      simp only [absent,Nat.zero_mul,Nat.div_zero]
  have role:RolePorts.endAddress L.B floor≤floor+(1+L.B.fields)*(2*2^(h/2))+L.B.fields*(2*(rows₀+2)):=by
    apply (RolePorts.resources L.B (⟨0,0⟩ : Bank) floor 0).2.2.trans
    unfold DescentOrdinaryBorn.Chart.endAddress DescentOrdinaryBorn.Chart.output DescentOrdinaryBorn.Chart.bookWords
      DescentOrdinaryBorn.Chart.pitch
    rw [oldRows]
    gcongr
    first | exact chipTable | exact round rows₀
  have disp : L.endAddress floor=RolePorts.endAddress L.B floor+2^Nat.clog 2 src+
      (dir+2*dst)+2^Nat.clog 2 (dir+1)+2^Nat.clog 2 (dst+1)+dst+2^Nat.clog 2 L.nextRows :=rfl
  have arr (x : ℕ) : 2^Nat.clog 2 (x+1)≤2*(x+2):=DescentOperandVectorArena.rounded_bound x
  have dshape : dst=L.pages*L.radix*L.lows*rows₀:=by dsimp only [dst,rows,rows₀];ring
  have sshape : src=L.pages*L.lows*rows₀:=by dsimp only [src,sourceWords,rows₀];ring
  have nshape : L.nextRows=L.lows*rows₀:=by dsimp only [nextRows,rows₀];ring
  rw [disp]
  calc
    _ ≤ (floor+(1+L.B.fields)*(2*2^(h/2))+L.B.fields*(2*(rows₀+2)))+2*(src+2)+
        (L.radix*2^(h/2)+2*dst)+2*(L.radix*2^(h/2)+2)+2*(dst+2)+dst+2*(L.nextRows+2) :=by
      have dpad:2^Nat.clog 2 (dir+1)≤2*(L.radix*2^(h/2)+2):=(arr dir).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_right dirTable _))
      gcongr <;> first | exact role | exact round src | exact dirTable | exact dpad | exact arr dst | exact round L.nextRows
    _ = _ :=by rw [sshape,dshape,nshape];dsimp only [rows₀];ring
theorem extent (floor h : ℕ) (_hm : 0<L.lanes) (hr : 0<L.radix) (pitch : L.B.lanes=L.lanes*L.radix)
    (same : L.B.groups=L.groups*L.radix) (chip : (L.B.chipBits*1+L.B.chipBits)*L.B.lanes≤h/2)
    (packed : (L.bits*L.radix)*L.lanes≤h/2) :
    L.endAddress floor≤floor+(16+4*L.B.fields)+(2*(1+L.B.fields)+3*L.radix)*2^(h/2)+
      (2*L.B.fields+2*L.pages*L.lows+5*L.pages*L.lows*L.radix+2*L.lows)*(L.B.hosts*chunks L.groups L.lanes) := L.extent_any floor h hr pitch same chip packed
end
end Hierarchy.DescentOrdinaryMouthReturn.Layout

end OAI
