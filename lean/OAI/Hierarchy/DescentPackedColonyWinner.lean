import OAI.Hierarchy.DescentPackedColonyAffine
import OAI.Hierarchy.DescentGLPermutationRAM

namespace OAI
/-! # Feed the real winning multiplier word to the single packed affine input -/
namespace Hierarchy.DescentPackedColony
open DescentSIMDLookup DescentColonies DescentColonies.PackedSplit DescentGL
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {H G q k b M w : ℕ}

def ordinal (ptr : ℕ) : Expr := .lookup ⟨ptr,0⟩ (.lit 0)
def chosen (ptr : ℕ) (source : Fin q→Bank) (amount : Bank) (T : Fin q→DescentPackedZip.Tables) : Expr :=
  chooseField q 0 (fun i=>(T i).read (.lookup (source i) .row) (.lookup amount .row)) (ordinal ptr)

theorem chosen_read (ptr : ℕ) (source : Fin q→Bank) (amount : Bank) (T : Fin q→DescentPackedZip.Tables)
    (out : ℕ) (tables : ∀i,WordRoom (T i) (width k) (b*2^k) M w out)
    (fs : ∀i : Fin q,(source i).Fits w out ∧ H*chunks G M≤(source i).size)
    (fa : amount.Fits w out) (ar : H*chunks G M≤amount.size) (keyRoom : q≤2^w)
    (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (a : Bits k) (seed : Fin q→Nonzero k) (small : ∀g v x,amt g v x<2^b)
    (m : Memory w) (win : Fin q) (found : m ptr=(win.val:Word w))
    (input : Reads amount (fun v g=>counts b (amt g v)) M m)
    (rows : ∀i,Reads (source i) (PackedSplit.state inc W D cap a (seed i)) M m)
    (rom : ∀i,DescentPackedZip.Static (T i) (affine (b:=b) a (seed i).val) M m) :
    DescentPackedZip.Source (chosen ptr source amount T)
      (fun v g=>DescentAffineColors.PackedContribution.actual b inc W amt D cap a (seed win) g v) M m := by
  intro p
  have cur : ((ordinal ptr).eval m ((row H G M p).val:Word w)).val=0+win.val := by
    simp [ordinal,Expr.eval,Bank.read,Bank.size,found,Fin.val_cast_of_lt (win.isLt.trans_le keyRoom)]
  rw [chosen,eval_chooseField q 0 _ _ _ _ win (by simpa using keyRoom) cur]
  have data:=DescentPackedZip.read_data (T win) (.lookup (source win) .row) (.lookup amount .row) out
    ((tables win).issue _ _ ⟨(fs win).1,trivial⟩ ⟨fa,trivial⟩)
    (affine (b:=b) a (seed win).val) (affine_zero ..) m (rom win)
    (PackedSplit.state inc W D cap a (seed win)) (fun v g=>counts b (amt g v))
    (DescentPackedZip.source_column (source win) out (fs win).1 m _ (fs win).2 (rows win))
    (DescentPackedZip.source_column amount out fa m _ ar input) p
  simpa only [affine_read _ _ _ _ _ _ _ _ _ (small _ _)] using data

theorem chosen_fits (ptr out : ℕ) (source : Fin q→Bank) (amount : Bank) (T : Fin q→DescentPackedZip.Tables)
    (key : (⟨ptr,0⟩:Bank).Fits w out) (fs : ∀i,(source i).Fits w out) (fa : amount.Fits w out)
    (tables : ∀i,WordRoom (T i) (width k) (b*2^k) M w out) :
    (chosen ptr source amount T).Fits w out :=
  DescentGLPermutationRAM.fits_choose _ _ _ _ ⟨key,trivial⟩
    (fun i=>(tables i).safe _ _ ⟨fs i,trivial⟩ ⟨fa,trivial⟩)

theorem chosen_work (ptr : ℕ) (source : Fin q→Bank) (amount : Bank) (T : Fin q→DescentPackedZip.Tables) :
    (chosen ptr source amount T).work=1+33*q := by
  unfold chosen
  rw [DescentGLPermutationRAM.work_choose _ _ _ _ 25 (fun i=>by rw [DescentPackedZip.work];rfl)]
  simp only [ordinal,Expr.work]
  ring

theorem publish (ptr out : ℕ) (source : Fin q→Bank) (amount : Bank) (T : Fin q→DescentPackedZip.Tables)
    (key : (⟨ptr,0⟩:Bank).Fits w out) (fs : ∀i : Fin q,(source i).Fits w out ∧ H*chunks G M≤(source i).size)
    (fa : amount.Fits w out) (ar : H*chunks G M≤amount.size) (keyRoom : q≤2^w)
    (room : out+H*chunks G M<2^w) (tables : ∀i,WordRoom (T i) (width k) (b*2^k) M w out)
    (inc : Fin H→List (Fin H)) (W amt : Fin G→Fin H→Block k→ℕ) (D cap : ℕ)
    (a : Bits k) (seed : Fin q→Nonzero k) (small : ∀g v x,amt g v x<2^b) (win : Fin q) :
    let e:=chosen ptr source amount T
    (scan w out (H*chunks G M) e).Spec
      (fun m=>m ptr=(win.val:Word w) ∧ Reads amount (fun v g=>counts b (amt g v)) M m ∧
        (∀i,Reads (source i) (PackedSplit.state inc W D cap a (seed i)) M m) ∧
        ∀i,DescentPackedZip.Static (T i) (affine (b:=b) a (seed i).val) M m)
      (fun m after=>after=ProtocolRAM.image out (H*chunks G M) e m ∧ ∀p : Row H G M,
        after (out+(row H G M p).val)=((data (fun v g=>
          DescentAffineColors.PackedContribution.actual b inc W amt D cap a (seed win) g v) p).val:ℕ))
      (4+H*chunks G M*(2*(1+33*q)+4)) ∧ CheapCode (scan w out (H*chunks G M) e) := by
  dsimp only
  refine ⟨?_,scan_cheap w out (H*chunks G M) (chosen ptr source amount T)⟩
  intro P N K mach pc reg pub exit rom regs cfg m start pre
  obtain ⟨time,ticks,done,after,run,ended,mem⟩:=scan_exec out (H*chunks G M) (chosen ptr source amount T) m
    (chosen_fits ptr out source amount T key (fun i=>(fs i).1) fa tables) room mach pc reg pub exit rom regs cfg m start rfl
  refine ⟨time,by simpa only [chosen_work] using ticks,done,after,run,ended,mem,?_⟩
  intro p
  rw [mem]
  have ip:=(row H G M p).isLt
  simpa [ProtocolRAM.image,fillSegment,show out≤out+(row H G M p).val ∧ out+(row H G M p).val<out+H*chunks G M
    by omega,Nat.cast_add] using chosen_read ptr source amount T out tables fs fa ar keyRoom inc W amt D cap a seed
      small m win pre.1 pre.2.1 pre.2.2.1 pre.2.2.2 p

end
end Hierarchy.DescentPackedColony

end OAI
