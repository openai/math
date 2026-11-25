import OAI.Hierarchy.DescentPackedLayoutChoice

namespace OAI
/-! # Public buffer allocation and bill for the shared layout bit -/
namespace Hierarchy.DescentPacking.PackedMatch.LayoutSum
open DescentSixParty DescentSIMDLookup DescentPackedLayoutCPU DescentStaticWordColumn
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F] (s : Shape) (M : ℕ)
local notation "a" => SixBirths.width s M
local notation "Q" => 2^a

/-- Every table and scratch register follows the real packed birth output. -/
def plan (old : Bank) (base n : ℕ) : DescentBestLayoutRAM.Banks where
  pairs:=old
  tariff:=fun side=>⟨if side then base+Q else base,a⟩
  counts:=fun side=>if side then base+2*Q+2*n+1 else base+2*Q
  starts:=fun side=>if side then base+2*Q+3*n+1 else base+2*Q+n
  leftEnd:=⟨base+2*Q+2*n,0⟩
  rightEnd:=⟨base+2*Q+4*n+1,0⟩
  out:=base+2*Q+4*n+2

theorem space (old : Bank) (base n w : ℕ) (source : old.Fits w base) (rows : n≤old.size)
    (ends : base+2*Q+4*n+3 < 2^w) :
    Space (plan s M old base n) w n ∧ ROMSpace s M n w (plan s M old base n) := by
  have r:=source.2.2
  have qpos : 0 < Q:=by positivity
  have one : 1 < 2^w:=by omega
  constructor
  · refine ⟨?_,?_,rows,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
    · intro b
      exact ⟨source.1,source.2.1,by cases b <;> simp only [plan,Bool.false_eq_true,ite_false,ite_true] <;> omega⟩
    · intro b
      cases b <;> simp only [plan,Bool.false_eq_true,ite_false,ite_true,Bank.Fits,Bank.size]
        <;> exact ⟨qpos,by omega,by omega⟩
    · intro b;cases b <;> simp [plan]; omega
    · intro b;cases b <;> simp [plan] <;> omega
    · change base+2*Q+n+n < base+2*Q+2*n+1;omega
    · change base+Q+Q≤base+2*Q;omega
    · change base+2*Q+2*n=base+2*Q+n+n;omega
    · change base+2*Q+4*n+1=base+2*Q+3*n+1+n;omega
    · exact ⟨Nat.zero_lt_one,one,by change base+2*Q+2*n+1≤base+2*Q+4*n+2;omega⟩
    · exact ⟨Nat.zero_lt_one,one,by change base+2*Q+4*n+1+1≤base+2*Q+4*n+2;omega⟩
    · exact ends
  · refine ⟨?_,?_,?_,?_⟩
    · change old.base+n≤base;omega
    · rfl
    · change base+Q+Q < 2^w;omega
    · intro b;exact le_rfl

def clocks (n : ℕ) := 80+20*Q+80*n
theorem clock_eq (B : DescentBestLayoutRAM.Banks) (n : ℕ) :
    ((4+10*Q)+(4+10*Q)+DescentPackedLayoutCPU.ticks B n)=clocks s M n := by
  change _+ (2*((4+28*n)+(10+(3+12*n)))+(4+1*(2*15+4)))=_
  unfold clocks
  omega

theorem hardware (G : PoweredGadget F) (B : DescentBestLayoutRAM.Banks) (w n : ℕ) :
    names ((install s B M w G).seq (DescentPackedLayoutCPU.program B w n))=30*(Q+1)+265 := by
  have first : names (ProtocolRAMEndpointPrefix.exclusive w (B.counts false) (B.starts false) n)=38:=rfl
  have second : names (ProtocolRAMEndpointPrefix.exclusive w (B.counts true) (B.starts true) n)=38:=rfl
  simp only [install,DescentPackedLayoutCPU.program,DescentPackedLayoutCPU.side,
    names_seq,names_mount,names_scan,first,second]
  change (15*(Q+1)+15*(Q+1)) + (((11+4*12+38)+(11+4*12+38))+(11+4*15))=_
  omega

/-- The same clock also applies to rejected and malformed candidate histories. -/
theorem unconditional (old : Bank) (G : PoweredGadget F) (base n w : ℕ) (source : old.Fits w base)
    (rows : n≤old.size) (ends : base+2*Q+4*n+3 < 2^w) (m : Memory w) :
    let B:=plan s M old base n
    ∃fee : Bool→Fin n→ℕ,
      ((install s B M w G).seq (DescentPackedLayoutCPU.program B w n)).Exec m
        (DescentPackedLayoutCPU.after B (mounted s B M G m) fee) (clocks s M n) ∧
      ∀x,B.out < x→DescentPackedLayoutCPU.after B (mounted s B M G m) fee x=m x := by
  let B:=plan s M old base n
  obtain ⟨room,rom⟩:=space s M old base n w source rows ends
  obtain ⟨load,_,held⟩:=mount (G:=G) s B m rom
  obtain ⟨fee,finish⟩:=DescentPackedLayoutCPU.total_run B (mounted s B M G m) room
  refine ⟨fee,?_,?_⟩
  · rw [←clock_eq s M B n]
    exact load.then finish
  · intro x hi
    apply (DescentPackedLayoutCPU.above B _ _ room x hi).trans
    apply held x (.inr ?_)
    change base+Q+Q≤x
    change base+2*Q+4*n+2 < x at hi
    omega

/-- The data scans have the same packed rate as the already issued birth shelf. -/
theorem clock_price (H G w : ℕ) (pos : 0 < s.digit) (wide : 2*SixBirths.unit s≤w) :
    let batch:=lanes w (SixBirths.unit s)
    clocks s batch (H*chunks G batch)*w ≤
      (80+20*2^(w/2))*w+80*(H*w+4*H*G*SixBirths.unit s) := by
  let batch:=lanes w (SixBirths.unit s)
  have p:=SixBirths.price s w H G pos wide
  change _ ∧ SixBirths.width s batch≤w/2 ∧ _ at p
  have bound:=Nat.pow_le_pow_right (by decide : 0 < 2) p.2.1
  have cells:=p.2.2
  dsimp only
  unfold clocks
  nlinarith only [cells,Nat.mul_le_mul_right w bound]

end
end Hierarchy.DescentPacking.PackedMatch.LayoutSum

end OAI
