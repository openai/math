import OAI.Hierarchy.DescentPackedColonyStep
import OAI.Hierarchy.DescentPackedAffineContribution

namespace OAI
/-! # The actual packed outgoing amounts and winning split cache feed one affine scan -/
namespace Hierarchy.DescentPackedColony
open DescentSIMDLookup DescentColonies DescentColonies.PackedSplit DescentGL
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G Δ M k b w : ℕ}

/-- The final affine dictionary consumes the same winning split flags and
the measured outgoing amounts after the genuine multiplier permutation. -/
def affine (a μ : Bits k) (p : Panel k) (amount : Counts k b) :
    Cell (DescentAffineColors.PackedContribution.width k b) :=
  if p=0 then 0 else DescentAffineColors.PackedContribution.encode (decodeFlags (strip p))
    (fun x=>(paintIn a μ amount x:Cell b))

@[simp] theorem affine_zero (a μ : Bits k) : affine (b:=b) a μ (0:Panel k) 0=0 := by simp [affine]

theorem affine_read (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (a : Bits k) (μ : Nonzero k) (g : Fin G) (v : Fin H) (room : ∀x,amt g v x<2^b) :
    affine a μ.val (PackedSplit.state inc W D cap a μ v g) (counts b (amt g v))=
      DescentAffineColors.PackedContribution.actual b inc W amt D cap a μ g v := by
  simp only [affine,PackedSplit.state,present_ne_zero,ite_false,strip_present,decode_encodeFlags]
  unfold DescentAffineColors.PackedContribution.actual
  apply congrArg₂ DescentAffineColors.PackedContribution.encode rfl
  funext x
  apply Fin.ext
  change (paintIn a μ.val (counts b (amt g v)) x)%2^b=(multiplierLoad (amt g) a μ.val v x)%2^b
  rw [paintIn_read _ _ _ _ room]

/-- Every outgoing group and all terminal padding come directly from the old packed
count/flag banks in one two-operand native scan. -/
theorem affine_spec (T : DescentPackedZip.Tables) (flags amount : Bank) (out : ℕ)
    (L : WordRoom T (width k) (b*2^k) M w out) (rF : flags.Fits w out) (rA : amount.Fits w out)
    (capF : H*chunks G M≤flags.size) (capA : H*chunks G M≤amount.size) (good : out+H*chunks G M<2^w)
    (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) (a : Bits k)
    (μ : Nonzero k) (room : ∀g v x,amt g v x<2^b) :
    let u:=Expr.lookup flags .row
    let v:=Expr.lookup amount .row
    (DescentPackedZip.code T u v out H G M w).Spec
      (fun m=>DescentPackedZip.Static T (affine (b:=b) a μ.val) M m ∧
        Reads flags (PackedSplit.state inc W D cap a μ) M m ∧ Reads amount (fun n g=>counts b (amt g n)) M m)
      (fun before after=>after=image out (H*chunks G M) (T.read u v) before ∧
        ∀p : Row H G M,after (out+(row H G M p).val)=((data (fun v g=>
          DescentAffineColors.PackedContribution.actual b inc W amt D cap a μ g v) p).val:ℕ))
      (4+H*chunks G M*(2*(T.read u v).work+4)) ∧ CheapCode (DescentPackedZip.code T u v out H G M w) := by
  dsimp only
  let u:=Expr.lookup flags .row
  let v:=Expr.lookup amount .row
  obtain ⟨exec,cheap⟩ := DescentPackedZip.spec T u v out (L.issue u v ⟨rF,trivial⟩ ⟨rA,trivial⟩)
    good (affine (b:=b) a μ.val) (affine_zero ..) (PackedSplit.state inc W D cap a μ) (fun n g=>counts b (amt g n))
  refine ⟨?_,cheap⟩
  intro P N K mach pc reg pub exit rom regs cfg m start pre
  obtain ⟨time,ticks,done,after,run,ended,mem,fields⟩ := exec mach pc reg pub exit rom regs cfg m start
    ⟨pre.1,DescentPackedZip.source_column flags out rF m _ capF pre.2.1,
      DescentPackedZip.source_column amount out rA m _ capA pre.2.2⟩
  refine ⟨time,ticks,done,after,run,ended,mem,?_⟩
  intro p
  simpa only [affine_read _ _ _ _ _ _ _ _ _ (room _ _)] using fields p

end
end Hierarchy.DescentPackedColony

end OAI
