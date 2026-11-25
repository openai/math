import OAI.Hierarchy.DescentRecipeClosedReset
import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # The rotor layer word is a single integer from the actual preceding stage capacity -/
namespace Hierarchy.DescentRecordedRotorLayers
open DescentCompiler DescentSixParty DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def layers (n packet f cap : ℕ) := 2*((10*2^f*cap)/((2^n)*packet))+1
def width (f cap : ℕ) := ProtocolRAMPurchaseSampler.bits (21*2^f*(cap+1))

theorem layers_fit (n packet f cap : ℕ) : layers n packet f cap<2^width f cap := by
  have step:=Nat.div_le_self (10*2^f*cap) ((2^n)*packet)
  apply lt_of_le_of_lt _ (ProtocolRAMPurchaseSampler.lt_span _)
  unfold layers
  calc 2*((10*2^f*cap)/((2^n)*packet))+1≤2*(10*2^f*cap)+1 := Nat.add_le_add_right (Nat.mul_le_mul_left 2 step) _
       _≤21*2^f*(cap+1):=by nlinarith [Nat.two_pow_pos f]

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
  {q ε : ℝ} {S : AtomSchedule} {k i z w hist : ℕ}
  {W : MarkedWorld F d P bits} {D n h C f g cut tail : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (b : ClosedReset input ctl)

theorem recorded {p : ℕ} (r : b.Recorded p) (s : Bool) (host : b.reset.placement.Good) :
    (b.reset.circuit s host).layers=layers n ctl.bitsR f input.placement.cap := by
  let Z:=b.reset
  have wirePos : 0<w:=input.edges ▸ input.placement.wirePos
  have oldUnit : 0<z*G.b := Nat.mul_pos (input.grain ▸ input.placement.unitPos) G.base_pos
  have uPos : 0<(Z.unit:ℝ):=by
    rw [b.unit];exact_mod_cast oldUnit
  have room : 0<(w:ℝ):=by exact_mod_cast wirePos
  have pay : Z.pay=((2^f*Z.unit*input.placement.cap:ℕ):ℝ) := by
    apply mul_left_cancel₀ room.ne'
    calc (w:ℝ)*Z.pay=((2^f*(w*(z*G.b)*input.placement.cap):ℕ):ℝ):=r.reserve_exact
         _=_:=by rw [b.unit];push_cast;ring
  rw [(Z.circuit s host).canonicalLayers]
  unfold layers
  have computed : 10*Z.pay/(((2^Z.n:ℕ):ℝ)*Z.width*Z.unit)=
      ((10*2^f*input.placement.cap:ℕ):ℝ)/(((2^n)*ctl.bitsR:ℕ):ℝ) := by
    rw [pay,b.dimension,b.width]
    push_cast
    field_simp [uPos.ne',(by exact_mod_cast ctl.bits_positive.ne' : (ctl.bitsR:ℝ)≠0)]

  rw [computed,Nat.floor_div_natCast,Nat.floor_natCast]

theorem from_prior_cap {p : ℕ} (r : b.Recorded p) (s : Bool) (host : b.reset.placement.Good)
    (bound : ℕ) (seen : bound=input.placement.cap) :
    (b.reset.circuit s host).layers=layers b.reset.n b.reset.width f bound ∧
      (b.reset.circuit s host).layers<2^(width f bound) := by
  subst bound
  rw [recorded b r s host,b.dimension,b.width]
  exact ⟨rfl,layers_fit ..⟩

def capTable (base capBits n packet f : ℕ) (mem : Memory w) (i : ℕ) : Word w :=
  if base≤ i ∧ i<base+2^capBits then (layers n packet f (i-base):ℕ) else mem i

theorem cap_read {H : ℕ} (base capBits n packet f : ℕ) (capacity : Expr) (mem : Memory H) (tick : Word H) (bound : ℕ)
    (atCap : capacity.eval mem tick=(bound:Word H)) (fits : bound<2^capBits) (word : capBits≤H)
    (stored : ∀j<2^capBits,mem (base+j)=(layers n packet f j:Word H)) :
    (Expr.lookup (⟨base,capBits⟩:Bank) capacity).eval mem tick=(layers n packet f bound:Word H) := by
  have ok : bound<2^H:=fits.trans_le (Nat.pow_le_pow_right (by decide) word)
  simp only [Expr.eval,atCap,Bank.read,Bank.size,Fin.val_cast_of_lt ok,Nat.mod_eq_of_lt fits,stored _ fits]

theorem mount (base capBits n packet f : ℕ) (mem : Memory w) (j : ℕ) (live : j<2^capBits) :
    capTable base capBits n packet f mem (base+j)=(layers n packet f j:ℕ) := by simp [capTable,live]

theorem layers_all {p : ℕ} (r : b.Recorded p) (s s' : Bool) (g g' : b.reset.placement.Good) :
    (b.reset.circuit s g).layers=(b.reset.circuit s' g').layers := (recorded b r s g).trans (recorded b r s' g').symm

end
end Hierarchy.DescentRecordedRotorLayers

end OAI
