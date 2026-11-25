import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapKeys
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapCodec
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapStage
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileRectSpec
import OAI.Computability.NearSquareRoot.PhysicalWalshSwapData

/-! # The generated high-field interchange on a padded Walsh row -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileSwapPadded

open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode
open PhysicalWalshNode.SlotSwap (Packet wideExtra)
open PhysicalWalshCompileSwapRulers (Control World)
open PhysicalWalshCompileSwapKeys (setGrade)
open CommonRegisters GeneratorSyntax Filter

/-- All three stages preserve the same compact descriptor. -/
def build (frame : PhysicalWalshCompileSwapStage.Frame) (pk rc up : Control → Cmd)
    (pack unpack rect : Cmd) (k : Control) := (frame.supply (pk k) pack).join
      ((frame.supply (rc k) rect).join (frame.supply (up k) unpack))

def atShape (g : World → ℕ) {a : ℕ} (W D : ℕ) (i j : Fin (a+1)) (s : Shape) := g ⟨a,W,i,j,D,s⟩

/-- The rectangle sees the actual high-field geometry chosen for each shape. -/
def RectOn (g : World → ℕ) {a : ℕ} (W D : ℕ) (ρ : ℝ) (i j : Fin (a+1)) (rect : Cmd) : Prop :=
  ∀ (x : (t : XorInput W) → Data t.shape),
    let bank (t : XorInput W) := SlotSwap.bank W (atShape g W D i j t.shape) i j t.shape (x t)
    ClosedRuns rect (fun t => ⌈((bank t).volume : ℝ)*(((bank t).geometry.wing+1:ℕ):ℝ)^ρ⌉₊)
      (Packet.volume ∘ bank) (Packet.input ∘ bank) (Packet.output ∘ bank)

def Padded (g : World → ℕ) {a : ℕ} (W D d : ℕ) (ρ : ℝ) (i j : Fin (a+1)) (cmd : Cmd) : Prop :=
  ∀ (x : (t : XorInput W) → Data t.shape),
    let S (t : XorInput W) := allowance (a+1) d t.shape
    let row (t : XorInput W) := SwapPrefix.stream (SwapPrefix.paddedSize (a+1) W t.shape)
    ClosedRuns cmd (fun t => S t + wideExtra ρ (a+1) t.shape) S
      (fun t => send (Header.wire (a+1) t.shape, row t (x t)))
      (fun t => send (Header.wire (a+1) t.shape, row t (x t ∘ SlotSwap.moved W (atShape g W D i j t.shape) i j t.shape)))

private theorem assemble (g : World → ℕ) {R a W D d : ℕ} {frame : PhysicalWalshCompileSwapStage.Frame}
    (hf : PhysicalWalshCompileSwapStage.Legal frame R) {pk rc up : Control → Cmd}
    (hpk : PhysicalWalshCompileSwapKeys.KeyRuns (PhysicalWalshCompileSwapRulers.packHeader ∘ setGrade g) d pk)
    (hrc : PhysicalWalshCompileSwapKeys.KeyRuns (PhysicalWalshCompileSwapRulers.rectHeader ∘ setGrade g) d rc)
    (hup : PhysicalWalshCompileSwapKeys.KeyRuns (PhysicalWalshCompileSwapRulers.unpackHeader ∘ setGrade g) d up)
    {pack unpack rect : Cmd} (hp : PhysicalWalshCompileSwapCodec.Packs pack) (hu : PhysicalWalshCompileSwapCodec.Unpacks unpack)
    {ρ : ℝ} (nonneg : 0 ≤ ρ) (i j : Fin (a+1)) (order : j.val < i.val)
    (hr : RectOn g W D ρ i j rect) :
    Padded g W D d ρ i j (build frame pk rc up pack unpack rect (a+1,W,i.val,j.val,D)) := by
  intro x S row
  let T (t : XorInput W) := S t + wideExtra ρ (a+1) t.shape
  have cost (t : XorInput W) : S t ≤ T t := Nat.le_add_right ..
  let k : Control := (a+1,W,i.val,j.val,D)
  let key (t : XorInput W) := Header.wire (a+1) t.shape
  let E (t : XorInput W) := atShape g W D i j t.shape
  let c (t : XorInput W) := SlotSwap.reserve (E t) (a+1) t.shape
  let z (t : XorInput W) := SlotSwap.geometry W i j t.shape (c t)
  let b (t : XorInput W) := SlotSwap.stride i j t.shape (c t)
  let n (t : XorInput W) := (z t).grid.count
  let y (t : XorInput W) := x t ∘ SlotSwap.moved W (atShape g W D i j t.shape) i j t.shape
  let bank (t : XorInput W) := SlotSwap.bank W (E t) i j t.shape (x t)
  have ne : i ≠ j := fun eq => (Nat.ne_of_lt order) (congrArg Fin.val eq.symm)
  have hn (t) : 0 < n t := by change 0 < (z t).grid.count; rw [SlotSwap.geometry_count]; positivity
  have hb (t) : 0 < b t := Nat.mul_pos (Nat.two_pow_pos _) t.shape.suff_pos
  let batch (f : (t : XorInput W) → Data t.shape) (t : XorInput W) : PhysicalWalshCompileSwapCodec.Batch :=
    ⟨t.shape.w,b t,n t,hb t,hn t,f t⟩
  have volume (t) : n t*b t = SwapPrefix.paddedSize (a+1) W t.shape :=
    SlotSwap.volume_eq (W:=W) i j ne t.shape t.positive (c t) (min_le_left ..)
  have size (t) : (n t*b t+1)*(t.shape.w+1) ≤ 2*S t := by
    rw [volume t]; exact SlotSwap.lane_volume_le _ _ d _
  have wrapCodec {cmd : Cmd} {q r : XorInput W → Tree}
      (h : ClosedRuns cmd (fun t : XorInput W => (n t*b t+1)*(t.shape.w+1))
        (fun t => (n t*b t+1)*(t.shape.w+1)) q r) : ClosedRuns cmd T S q r := by
    apply EffectiveBoundedTask.Runs.bound h 2 2 <;> intro t <;> have := size t <;> have := cost t <;> omega
  have packRun := hf.supply_runs cost (hpk a W i j ne D) (wrapCodec (hp.on (batch x)))
  have unpackRun := hf.supply_runs cost (hup a W i j ne D) (wrapCodec (hu.on (batch y)))
  have rectRun := hr x
  have actual : ClosedRuns rect T S (Packet.input ∘ bank) (Packet.output ∘ bank) := by
    apply EffectiveBoundedTask.Runs.bound rectRun 5 4 <;> intro t
    · have h := SlotSwap.bank_cost W (E t) i j nonneg t.shape (x t) ne t.positive
      exact h.trans (Nat.mul_le_mul_left 5 (Nat.succ_le_succ (Nat.le_add_left ..)))
    · have h := SlotSwap.lane_volume_le (a+1) W d t.shape
      change (SlotSwap.bank W (E t) i j t.shape (x t)).volume+1 ≤ 4*(S t+1)
      rw [SlotSwap.bank_volume W (E t) i j _ _ ne t.positive]
      change (SwapPrefix.paddedSize (a+1) W t.shape+1)*(t.shape.w+1) ≤ 2*S t at h
      ring_nf at h ⊢
      omega
  have perm (t) : (bank t).output = send (batch y t).packed := by
    apply congrArg send
    apply List.map_congr_left
    intro l _
    exact (PhysicalWalshSwapCodec.payload_map (hb t) (x t) (SlotSwap.wingSource (z t)) l).symm
  have pass : ClosedRuns rect T S
      (fun t => .fork (send (z t).header) (send (batch x t).packed)) (fun t => send (batch y t).packed) := by
    rw [← show (Packet.output ∘ bank) = fun t => send (batch y t).packed from funext perm]
    exact actual
  have rectStage := hf.supply_runs cost (hrc a W i j ne D) pass
  have combine := EffectiveBoundedTask.Runs.sequence packRun (EffectiveBoundedTask.Runs.sequence rectStage unpackRun)
  have batches (f : (t : XorInput W) → Data t.shape) (t : XorInput W) : (batch f t).stream = row t (f t) := by
    change (List.range (n t*b t)).map _ = _
    rw [volume t]; rfl
  change ClosedRuns _ T S (fun t => send (key t,(batch x t).stream)) (fun t => send (key t,(batch y t).stream)) at combine
  simpa only [batches,build,T,key,y] using combine

/-- Insert a rectangular routine in the two fixed record codecs. The family
of source files is computable jointly in that routine and the five literals. -/
theorem compile (g : World → ℕ)
    (pm : Mint PhysicalWalshCompileSwapRulers.regime (PhysicalWalshCompileSwapRulers.packHeader ∘ setGrade g))
    (rm : Mint PhysicalWalshCompileSwapRulers.regime (PhysicalWalshCompileSwapRulers.rectHeader ∘ setGrade g))
    (um : Mint PhysicalWalshCompileSwapRulers.regime (PhysicalWalshCompileSwapRulers.unpackHeader ∘ setGrade g))
    {J : Type} [Primcodable J] (rect : J → Cmd) (eff : Effective ltr rect)
    (B : ℕ) (regs : ∀ j, Within B (rect j)) :
    ∃ (emit : J × Control → Cmd) (R d : ℕ), Effective ltr emit ∧ (∀ p, Within R (emit p)) ∧ 1 ≤ d ∧
      ∀ (p : J) (a W D : ℕ) (ρ : ℝ), 0 ≤ ρ →
        ∀ i j : Fin (a+1), j.val < i.val → RectOn g W D ρ i j (rect p) → Padded g W D d ρ i j (emit (p,a+1,W,i.val,j.val,D)) := by
  obtain ⟨F,L,hF⟩ := PhysicalWalshCompileSwapStage.exists_frame
  obtain ⟨pk,rc,up,d,H,ep,ec,eu,hs,hd,hp,hr,hu⟩ := PhysicalWalshCompileSwapKeys.compileAt g pm rm um
  obtain ⟨⟨pack,hPack⟩,⟨unpack,hUnpack⟩⟩ := PhysicalWalshCompileSwapCodec.fixed
  obtain ⟨R,lR,hR,bR,pr,ur⟩ := ((eventually_ge_atTop L).and ((eventually_ge_atTop H).and
    ((eventually_ge_atTop B).and ((RegisterSelect.within_eventually pack).and
    (RegisterSelect.within_eventually unpack))))).exists
  refine ⟨fun p => build F pk rc up pack unpack (rect p.1) p.2,R,d,
    (F.effective_supply (ep.comp Computable.snd) (effective_const _ pack)).join
      ((F.effective_supply (ec.comp Computable.snd) (eff.comp Computable.fst)).join
       (F.effective_supply (eu.comp Computable.snd) (effective_const _ unpack))),?_,hd,?_⟩
  · intro p
    obtain ⟨p₁,p₂,p₃⟩ := hs p.2
    exact ⟨hF.within_supply lR (RegisterSelect.within_mono hR _ p₁) pr,
      hF.within_supply lR (RegisterSelect.within_mono hR _ p₂) (RegisterSelect.within_mono bR _ (regs p.1)),
      hF.within_supply lR (RegisterSelect.within_mono hR _ p₃) ur⟩
  · intro p a W D ρ nonneg i j order engine
    exact assemble g hF hp hr hu hPack hUnpack nonneg i j order engine

end PhysicalWalshCompileSwapPadded

end NearSquareRoot
end Computability
end OAI
