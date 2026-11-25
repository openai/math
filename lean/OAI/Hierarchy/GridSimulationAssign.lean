import OAI.Hierarchy.GridSelfHeader
import OAI.Hierarchy.GridPinArenaSlices
import OAI.Hierarchy.FactorThresholdInput
import OAI.Hierarchy.FactorAssignmentCompiler

namespace OAI
/-! # Native allocation following the retained trace's resource scan -/

noncomputable section
namespace Hierarchy.GridSimulation
open ThreeFlat RAM Diagonal PhysicalProcedure
open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM FactorBucketRAM GridPinArena
open scoped Fin.CommRing Classical

def thresholdSource (w e B d : ℕ) := e*2+w^2+B*w^2+d*(64*w)

theorem threshold_read {F : Type} [Field F] [Fintype F] {w e B n k p start ell tp tr tk ep er ek : ℕ}
    (X : Catalyst.Approximation F k p) (enc : FieldCode F (64*w)) (params : Fin n→Word (64*w))
    (recv : Machine (64*w) tp tr tk) (eval : Machine (64*w) ep er ek)
    (pin : Fin (e*2)→Bool) (sel : Fin ell→Bool) (pos : 0<w)
    (sep : GridSelfHeader.rawSize w e B n≤ start) (i : ℕ) (hi : i<(64*w)*GridReceiverHeader.count w) :
    GridSelfHeader.captured (B:=B) X enc params recv eval pin start sel (thresholdSource w e B n+i)=
      ((thresholdBit (64*w) i).toNat:Word (64*w)) := by
  let W := 64*w
  have wp : 0<W := by dsimp [W]; omega
  let j : Fin (GridReceiverHeader.count w) := ⟨i/W,(Nat.div_lt_iff_lt_mul wp).mpr (by simpa [W,Nat.mul_comm] using hi)⟩
  let b : Fin W := ⟨i%W,Nat.mod_lt _ wp⟩
  let y := finProdFinEquiv (Fin.natAdd n j,b)
  have ix : y.val=n*W+i := by
    change i%W+W*(n+i/W)=n*W+i
    have := Nat.div_add_mod i W
    rw [Nat.mul_add,Nat.mul_comm W n]
    omega
  have rd := GridSelfHeader.operand_at (B:=B) X enc params recv eval pin sep sel y
  rw [GridReceiverHeader.word_at] at rd
  have hval := GridReceiverHeader.threshold_at pos j
  simp only [GridSelfHeader.words,Fin.addCases_right] at rd
  rw [hval] at rd
  simpa [thresholdSource,thresholdBit,ix,j,b,W,Nat.add_assoc] using rd

def assign (w src N d T : ℕ) : Procedure (64*w) :=
  (TraceAdmission.inputPacker (64*w) src (assignmentBanks w).thresholds (GridReceiverHeader.count w)).seq
    (FactorBucketRAM.compiler (64*w) w N d T (assignmentBanks w))

def assignTime (w N d : ℕ) :=
  GridReceiverHeader.count w*(5*(64*w)+6)+6 + FactorBucketRAM.ticks w N d

def protectedAddress (w N d a : ℕ) : Prop :=
  Outside a (assignmentBanks w).thresholds (GridReceiverHeader.count w) ∧
    untouched (assignmentBanks w) w N d a

structure Assigned {w N d T : ℕ} (ht : 0<T) (cost : Fin N → Fin d → ℕ)
    (m out : Memory (64*w)) : Prop where
  key : ∀ i, out ((assignmentBanks w).keys+i.val)=(classIndex (FactorAllocation.key w cost i):Word (64*w))
  owner : ∀ i, out ((assignmentBanks w).output+i.val)=((FactorAllocation.owner ht w cost i).val:Word (64*w))
  frame : ∀ a, protectedAddress w N d a→ out a=m a

theorem assign_spec {w src N d T : ℕ} (pos : 0<w) (ht : 0<T) (hd : 0<d)
    (cost : Fin N→Fin d→ℕ) (original : Memory (64*w))
    (rows : N*d≤ slab w) (width : GridReceiverHeader.count w≤ slab w) (items : N≤ slab w)
    (classes : (20*(w+1)+2)^d≤ slab w) (clock : N*d*(20*(w+1)+1)<2^(64*w))
    (dim : d<2^(64*w)) (ticksFit : T<2^(64*w))
    (low : src+(64*w)*GridReceiverHeader.count w≤GridDescription.sector w)
    (bits : ∀ i<(64*w)*GridReceiverHeader.count w,
      original (src+i)=((thresholdBit (64*w) i).toNat:Word (64*w)))
    (resources : ∀ (i : Fin N) (j : Fin d), (original ((assignmentBanks w).resources+(i.val*d+j.val))).val=cost i j) :
    (assign w src N d T).Spec (·=original) (fun _ out=>Assigned ht cost original out)
      (assignTime w N d) := by
  let b := assignmentBanks w
  let S := GridReceiverHeader.count w
  let J := GridDescription.sector w
  let g := slab w
  have sc := scales w pos
  have cuts : b.thresholds=14*J+g ∧ b.resources=14*J := ⟨rfl,rfl⟩
  change 32*g≤J ∧ 32*J<2^(64*w) at sc
  change S≤g at width
  change src+(64*w)*S≤J at low
  let mem := fun m : Memory (64*w) =>
    (∀ (i : Fin N) (j : Fin d), (m (b.resources+(i.val*d+j.val))).val=cost i j) ∧
    (∀ j≤20*(w+1),(m (b.thresholds+j)).val=FactorBucket.threshold j) ∧
    ∀ a,Outside a b.thresholds S → m a=original a
  have first : (TraceAdmission.inputPacker (64*w) src b.thresholds S).Spec (·=original)
      (fun _ o=>mem o) (S*(5*(64*w)+6)+6) := by
    intro pc regs slots M code reg pub exit install rom cfg m entry same
    subst m
    obtain ⟨t,ht,c,o,run,atExit,loaded⟩ := threshold_input w src b.thresholds pos
      (Or.inr (by change src+(64*w)*S≤b.thresholds; omega))
      (by change b.thresholds+S<2^(64*w); omega)
      (by change src+(64*w)*S<2^(64*w); omega)
      M code reg pub exit install rom cfg original entry bits
    refine ⟨t,ht,c,o,run,atExit,?_,loaded.1,loaded.2⟩
    intro i j
    have off : i.val*d+j.val<N*d := by
      have upper := Nat.mul_le_mul_right d i.isLt
      rw [Nat.succ_mul] at upper
      omega
    rw [loaded.2 _ (Or.inl (by omega)),resources]
  have both : (assign w src N d T).Spec (·=original)
      (fun _ out=> ∃ tmp, mem tmp ∧ (∀ a, untouched b w N d a → out a=tmp a) ∧
        ∀ i : Fin N, out (b.keys+i.val)=(classIndex (FactorAllocation.key w cost i):Word (64*w)) ∧
          out (b.output+i.val)=((FactorAllocation.owner ht w cost i).val:Word (64*w)))
      (assignTime w N d) :=
    Procedure.Spec.seq (A:=TraceAdmission.inputPacker (64*w) src b.thresholds S)
      (B:=FactorBucketRAM.compiler (64*w) w N d T b) first
      (assignment_compiler ht hd b (assignment_bounds pos rows width items classes) cost
        (by change S<_;omega) dim ticksFit clock (by omega) (by omega) (by omega))
      (fun _ _ h=>⟨h.1,h.2.1⟩)
  intro P R K machine pc reg pub exit install rom cfg m entry hm
  obtain ⟨t,ht,c,o,ran,ret,tmp,stored,done⟩ :=
    both machine pc reg pub exit install rom cfg m entry hm
  refine ⟨t,ht,c,o,ran,ret,fun i=>(done.2 i).1,fun i=>(done.2 i).2,?_⟩
  intro a free
  exact (done.1 a free.2).trans (stored.2.2 a free.1)

end Hierarchy.GridSimulation
end

end OAI
