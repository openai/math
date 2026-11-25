import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapPadded
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileElementaryRaw
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileGrade
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileRectSquare
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapPrefixCommand

/-! # An effective upper-field rectangle on a compact Walsh lane

The runtime header sets the reserved suffix to the smaller of the slot width
and the squared logarithm of the compact input size. Every native rectangle
degree can use this single program, including on the finite small-width range.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileSwapUpper

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode
open PhysicalWalshCompileXorRoute (Flat)
open PhysicalWalshCompileXorSwap (Params)
open PhysicalWalshCompileSwapPadded (Padded RectOn)
open PhysicalWalshCompileSwapRulers (Control)
open CommonRegisters GeneratorSyntax Filter
open KernelPass.ComputableSyntax (Op Packed)

def cut (A : ℕ) (s : Shape) := SlotSwap.reserve (Nat.clog 2 (Header.scale A s+1)) A s

theorem cut_eq (A : ℕ) (s : Shape) :
    cut A s = min (ElementarySchedule.slotWidth A s) ((Nat.clog 2 (Header.scale A s+1))^2) := by
  simp only [cut,SlotSwap.reserve,Controlled.payloadBits,pow_two]

private theorem rect_on {a W : ℕ} (i j : Fin (a+1)) (ne : i ≠ j) {ρ : ℝ} (nonneg : 0 ≤ ρ) {D : ℕ}
    {c : Cmd} (native : InterchangeROMBinary.RectPhysical c ρ D) :
    RectOn PhysicalWalshCompileGrade.live W 0 ρ i j (PhysicalWalshCompileRect.command c) := by
  intro x bank
  apply PhysicalWalshCompileRect.rectRunsScaled nonneg native bank (2^(D^2))
  · intro t
    change 0 < SlotSwap.stride i j t.shape _ * (2*(t.shape.w+1))
    exact Nat.mul_pos (Nat.mul_pos (Nat.two_pow_pos _) t.shape.suff_pos) (by omega)
  · exact fun t => PhysicalWalshCompileRect.square_fit_at D a W i j ne _ t.positive (x t)

private def AW (p : Control) := (p.1,p.2.1)

private noncomputable def route (body : Cmd) (k : Control) :=
  (SwapPrefixCmd.pre (AW k)).join (body.join (SwapPrefixCmd.post (AW k)))

private theorem whole {a W d e : ℕ} {ρ : ℝ} {i j : Fin (a+1)} (less : j.val < i.val) {body : Cmd}
    (run : Padded PhysicalWalshCompileGrade.live W 0 d ρ i j body) (large : max d SwapPrefixCmd.degree ≤ e) :
    Flat (a:=a) (W:=W) (nodeScan a W e (SlotSwap.wideExtra ρ (a+1))) (nodeArena a W e)
      (Route.upperSwap (cut (a+1)) i j) (route body (a+1,W,i.val,j.val,0)) := by
  let A := a+1
  let s := @XorInput.shape W
  let x (t : XorInput W) := SwapPrefix.extend A W (s t) t.row
  let E t := Nat.clog 2 (Header.scale A (s t)+1)
  let y (t : XorInput W) := x t ∘ SlotSwap.moved W (E t) i j (s t)
  let T t := nodeScan a W e (SlotSwap.wideExtra ρ A) (s t)
  let S t := nodeArena a W e (s t)
  have cap {b : ℕ} (he : b ≤ e) (t : XorInput W) : allowance A b (s t) ≤ S t :=
    (allowance_mono he _).trans (le_max_left ..)
  have cost (t : XorInput W) : S t ≤ T t := Nat.le_add_right ..
  have hpad := cap ((le_max_right ..).trans large)
  have hbody := cap ((le_max_left ..).trans large)
  have first := (SwapPrefixCmd.pre_runs A W s (fun t => t.row)).mono (fun t => (hpad t).trans (cost t)) hpad
  have last := (SwapPrefixCmd.post_runs A W s y).mono (fun t => (hpad t).trans (cost t)) hpad
  have middle := (run x).mono (time':=T) (space':=S) (fun t => Nat.add_le_add_right (hbody t) _) hbody
  have full := EffectiveBoundedTask.Runs.sequence first (EffectiveBoundedTask.Runs.sequence middle last)
  have eq (t : XorInput W) : laneFlat A W (s t) (y t) = laneFlat A W (s t) (Route.upperSwap (cut A) i j (s t) t.row) := by
    apply List.map_congr_left
    intro n mem
    have inside := SlotSwap.moved_lt W (E t) i j (s t) t.positive less n (List.mem_range.mp mem)
    change Dusk.mark (SwapPrefix.extend A W (s t) t.row (SlotSwap.moved W (E t) i j (s t) n)) = _
    rw [SwapPrefix.extend,ite_eq_left inside,SlotSwap.moved_eq W (E t) i j (s t) less n]
    rfl
  change ClosedRuns _ T S _ (fun t => send (laneFlat A W (s t) (y t))) at full
  simpa only [eq,Flat,route,AW,A,s,T,S] using full

/-- Source for every legal upper swap, jointly in the native rectangle source
index, raw template, and two axes. The native complexity degree serves only
in the correctness proof and can vary across candidates. -/
theorem compileSquare {J : Type} [Primcodable J] (c : J → Cmd) (eff : Effective ltr c)
    (B : ℕ) (regs : ∀ j, Within B (c j)) :
    ∃ (upper : J × Params → Cmd) (R d : ℕ), Effective ltr upper ∧ (∀ k, Within R (upper k)) ∧
      ∀ p a W (ops : List Op), (Packed.decode (a+1) ops).i = W → ∀ (e : ℕ), d ≤ e →
        ∀ (ρ : ℝ) (D : ℕ), 0 ≤ ρ → InterchangeROMBinary.RectPhysical (c p) ρ D →
        ∀ i j : Fin (a+1), j < i → Flat (a:=a) (W:=W) (nodeScan a W e (SlotSwap.wideExtra ρ (a+1)))
          (nodeArena a W e) (Route.upperSwap (cut (a+1)) i j) (upper (p,(a+1,ops),i.val,j.val)) := by
  obtain ⟨L,bL,rectReg⟩ := ((eventually_ge_atTop B).and PhysicalWalshCompileRect.registers).exists
  obtain ⟨cmd,F,d,emit,cmdReg,_,runs⟩ := PhysicalWalshCompileSwapPadded.compile PhysicalWalshCompileGrade.live
    (PhysicalWalshCompileGrade.mint PhysicalWalshCompileSwapRulers.packMint)
    (PhysicalWalshCompileGrade.mint PhysicalWalshCompileSwapRulers.rectMint)
    (PhysicalWalshCompileGrade.mint PhysicalWalshCompileSwapRulers.unpackMint)
    (fun p => PhysicalWalshCompileRect.command (c p)) (PhysicalWalshCompileRect.effective eff) L
    (fun p => rectReg _ (RegisterSelect.within_mono bL _ (regs p)))
  obtain ⟨H,_,hreg⟩ := SwapPrefixCmd.within
  let key (p : J × Params) := PhysicalWalshCompileElementaryRelease.rawKey (0,p.2)
  have hk : Computable key := PhysicalWalshCompileElementaryRelease.primrec_rawKey.to_comp.comp ((Computable.const 0).pair Computable.snd)
  have dims : Computable (fun p => AW (key p)) := (Computable.fst.comp hk).pair ((Computable.fst.comp Computable.snd).comp hk)
  let source (p : J × Params) := route (cmd (p.1,key p)) (key p)
  have e₁ : Effective ltr (fun p => SwapPrefixCmd.pre (AW (key p))) := SwapPrefixCmd.effective_pre.comp dims
  have e₂ : Effective ltr (fun p => cmd (p.1,key p)) := emit.comp (Computable.fst.pair hk)
  have e₃ : Effective ltr (fun p => SwapPrefixCmd.post (AW (key p))) := SwapPrefixCmd.effective_post.comp dims
  refine ⟨source,max H F,max d SwapPrefixCmd.degree,e₁.join (e₂.join e₃),?_,?_⟩
  · intro p
    exact ⟨RegisterSelect.within_mono (le_max_left ..) _ (hreg _).1,
      RegisterSelect.within_mono (le_max_right ..) _ (cmdReg _),RegisterSelect.within_mono (le_max_left ..) _ (hreg _).2⟩
  · intro p a W ops hW e he ρ D nonneg native i j lt
    have run := runs p a W 0 ρ nonneg i j lt (rect_on i j (ne_of_gt lt) nonneg native)
    dsimp only [source,key,PhysicalWalshCompileElementaryRelease.rawKey]
    rw [← Packed.decode_shape,show (Packed.decode (a+1) ops).shape.1.1 = W from hW]
    exact whole lt run he

end PhysicalWalshCompileSwapUpper

end NearSquareRoot
end Computability
end OAI
