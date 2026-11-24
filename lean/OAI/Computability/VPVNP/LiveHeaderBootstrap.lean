import OAI.Computability.VPVNP.LiveHeaderAdviceStages
import OAI.Computability.VPVNP.LiveHeaderScalarStages

/-!
# Native recovery of the distributed index and advice

The first two stages start on the actual processor memory. Their two tag
writes are carried into the next dispatch. The resulting memory contains
the original packed headers, the index summaries and copied bits, and all
advice words. Every address outside the written regions keeps its value.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveHeaderProgram

open BurstRAM BurstRAM.PrivateRAM PrimedStackRAM ChainAssignments LiveHeaderSchedule LiveHeader
open scoped Fin.CommRing

variable {w d : ℕ}

/-- The bootstrap's recovered group index, summary, advice words, and packed headers, with a
frame for memory outside its writes. -/
structure BootstrapState (s : Sizes) (base : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (out : Memory w) : Prop where
  headers : SiteHeaders d hw advice cuts g out
  summary : Summary s base (g.val+1) out
  index : ∀ j < s.h+2, out (indexBase base+j) = PrimedInputRAM.encodeBit w ((g.val+1).testBit j)
  adviceWords : ∀ j : Fin s.advice, out (adviceBase s base + j.val) = PrimedInputRAM.encodeBit w (advice j)
  frame : ∀ k, k ≠ base → (k < indexBase base ∨ populationAddr s base < k) →
    (k < adviceBase s base ∨ adviceBase s base+s.advice ≤ k) →
    out k = physicalMemory (d := d) hw advice cuts g k

private theorem transfer_other {base : ℕ} {addr : Word w} {i : StageId} {m : Memory w}
    {k : ℕ} (haddr : addr.val = base) (hk : k ≠ base) :
    LiveStageLink.transferMemory addr (some i) m k = m k := by simp [LiveStageLink.transferMemory,writeMemory,haddr,hk]

theorem index_advice_prefix (s : Sizes) (base : ℕ) (hw : 4 ≤ w) (advice : CutSchedule.Bits s.advice)
    (cuts : AllCuts s.h s.delta) (g : Fin (2^(s.h+1))) (indices : s.h+2 ≤ 2^d) (adv : s.advice ≤ 2^d)
    (scratch : 2^d ≤ base) (fit : limit s base ≤ 2^w) :
    ∃ xs out, StagePrefix s base (some (⟨0, by decide⟩ : StageId)) (physicalMemory (d := d) hw advice cuts g)
      xs (some (⟨2, by decide⟩ : StageId)) out ∧ (∀ x ∈ xs, x.Good s) ∧
      BootstrapState (d := d) s base hw advice cuts g out := by
  let addr : Word w := Fin.ofNat _ base
  let id₀ : StageId := ⟨0,by decide⟩
  let id₁ : StageId := ⟨1,by decide⟩
  let id₂ : StageId := ⟨2,by decide⟩
  let m := physicalMemory (d := d) hw advice cuts g
  obtain ⟨r₀, hr₀, he₀, hl₀, hp₀, hf₀, data₀⟩ := index_stage_native s base hw advice cuts g indices scratch fit
  let x₀ : StageTrace w := ⟨id₀,25,List.replicate (calls s .index) [],r₀⟩
  let before := after m (eventLog r₀)
  let m₁ := x₀.finalMem addr m
  have run₀ : x₀.Exec s base m := ⟨hr₀,he₀,hf₀⟩
  have good₀ : x₀.Good s := ⟨(by decide : 25 ≤ 40),rfl,hl₀,hp₀⟩
  have tagFit : addr.val = base := by
    apply Nat.mod_eq_of_lt
    rw [limit_eq] at fit
    omega
  have pass₀ (k : ℕ) (hk : k ≠ base) : m₁ k = before k :=
    transfer_other (i := id₁) tagFit hk
  have hdr₁ : SiteHeaders d hw advice cuts g m₁ := fun v =>
    (pass₀ v.val (Nat.ne_of_lt (v.isLt.trans_le scratch))).trans (data₀.headers v)
  obtain ⟨r₁, hr₁, he₁, hl₁, hp₁, hf₁, data₁⟩ := advice_stage_native s base hw advice cuts g m₁ hdr₁ adv scratch fit
  let x₁ : StageTrace w := ⟨id₁,16,List.replicate (calls s .advice) [],r₁⟩
  let copied := after m₁ (eventLog r₁)
  let out := x₁.finalMem addr m₁
  have run₁ : x₁.Exec s base m₁ := ⟨hr₁,he₁,hf₁⟩
  have good₁ : x₁.Good s := ⟨(by decide : 16 ≤ 40),rfl,hl₁,hp₁⟩
  have pass₁ (k : ℕ) (hk : k ≠ base) : out k = copied k :=
    transfer_other (i := id₂) tagFit hk
  have keep (k : ℕ) (hk : k ≠ base) (ha : k < adviceBase s base ∨ adviceBase s base + s.advice ≤ k) :
      out k = before k := (pass₁ k hk).trans ((data₁.frame k ha).trans (pass₀ k hk))
  let pub := indexWords w s base
  have fit' := fit
  rw [limit_eq] at fit'
  have va : (pub 0).val = indexBase base := Nat.mod_eq_of_lt (by dsimp [indexBase]; omega)
  have vh : (pub 1).val = highAddr s base := Nat.mod_eq_of_lt (by dsimp [highAddr,indexBase]; omega)
  have vc : (pub 2).val = populationAddr s base := Nat.mod_eq_of_lt (by dsimp [populationAddr,highAddr,indexBase]; omega)
  have horder : base < indexBase base ∧ indexBase base ≤ highAddr s base ∧
      highAddr s base < populationAddr s base ∧ populationAddr s base < adviceBase s base := by
    dsimp [adviceBase,rightIndexBase,leftIndexBase,populationAddr,highAddr,indexBase]
    omega
  have hidx (j : ℕ) (hj : j < s.h+2) : out (indexBase base+j) = PrimedInputRAM.encodeBit w ((g.val+1).testBit j) := by
    have hbound : indexBase base+j < highAddr s base := by dsimp [highAddr]; omega
    rw [keep _ (by omega) (Or.inl (by omega)), ←va]
    exact data₀.copied j hj
  refine ⟨[x₀,x₁],out,StagePrefix.cons x₀ run₀ (StagePrefix.cons x₁ run₁ (.nil _ _)), ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact good₀
    · obtain rfl := List.mem_singleton.mp hx
      exact good₁
  · constructor
    · intro v
      rw [pass₁ v.val (Nat.ne_of_lt (v.isLt.trans_le scratch))]
      exact data₁.headers v
    · constructor
      · rw [keep _ (by omega) (Or.inl (by omega)), ←vh]; exact data₀.high
      · rw [keep _ (by omega) (Or.inl (by omega)), ←vc]; exact data₀.count
      · rw [← data₀.count]; exact data₀.singleton
      · simpa using hidx 0 (by omega)
    · exact hidx
    · intro j
      rw [pass₁ _ (by omega)]
      exact data₁.copied j
    · intro k hb hi ha
      rw [keep k hb ha]
      apply data₀.frame
      · change k < (pub 0).val ∨ (pub 0).val+(s.h+2) ≤ k
        rw [va]
        change k < indexBase base ∨ highAddr s base ≤ k
        omega
      · change k ≠ (pub 1).val
        rw [vh]; omega
      · change k ≠ (pub 2).val
        rw [vc]; omega

end LiveHeaderProgram

end VPVNP
end Computability
end OAI
