import OAI.Computability.IntegerMultiplication.Binary

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip.Series
variable {A B : Type}
theorem nth (s : Series A) (j : Fin s.count) :
    (natural s.count).follow ⟨j.val,by simp⟩=j := get_natural ..
noncomputable def native (s : Series A) :
    Adopt s (natural s.count) :=
  ⟨s.index,fun {_} f => by
    apply List.ext_getElem
    · rw [Series.card,Series.card,Series.count_natural]
    intro i h v
    let j : Fin s.count := ⟨i,by simpa using h⟩
    rw [s.get _ j, (natural s.count).get _ ⟨i,by simpa using h⟩]
    simp only [Function.comp_apply,index_symm]
    rw [get_natural _ j,index_follow]⟩
end Strip.Series
namespace Spindle
open Strip Loom Net.Shuttle Code Adic Dims

variable {I : Type} {r : Regime I} (P G B : I→Tape) (n : I→ℕ)
theorem rectBead
    (has : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hb : Told r B)
    (bound : ∀ i n0,n0∈P i ++ G i ++ B i → n0≤base)
    (L : I→ℕ) {T:I→Type} (t : (i:I)→Series (T i)) (h : ∀ i,(t i).count≤L i)
    (v : (i:I)→SpanKey (P i) (G i) (B i) (Block 2 (n i)) → T i → Bead) :
    let s i := stock 2 (P i) (G i) (B i) (n i)
    Breeze (modes n (τ:=Net.Motif.sigma)) r (fun i=>(s i).count) L
      (together r.header (cloth s t v))
      (cloth s t fun i x => v i (swapper _ _ _ x)) := by
  have solid i : Dims.solid (P i++G i++B i) := by simp [(hp.solid _),(hg.solid _),(hb.solid _)]
  let A i := stock 2 (P i) (G i) (B i) (n i)
  have v0 :=
    letI : NeZero base := ⟨by have := base_large; omega⟩
    starFlow (Series.arbitrary FPbit) Design.laced P G B Net.Motif.sigma_range.1
      Net.Motif.sigma_range.2.le (fun i n h => ⟨solid i n h,bound i n h⟩) hp.shape hg.shape hb.shape has L (fun i => (t i).count) h
        (fun i a => v i a ∘ (t i).index.symm)
  have u (v : (i:I)→SpanKey (P i) (G i) (B i) (Block 2 (n i))→T i→Bead) :
      cloth A (fun i => Series.natural (t i).count) (fun i a => v i a ∘ (t i).index.symm) =
        cloth A t v := by
    funext i; apply congrArg (stripe (A i)); funext a
    dsimp only
    rw [(t i).native.packet]
    apply congrArg (stripe (t i)); funext x
    simp [Series.native] -- congr issue
  have w := u v
  change Breeze _ _ _ _ (together _ (cloth A _ _)) (cloth A _ (fun i a => v i (swapper _ _ _ a) ∘ (t i).index.symm)) at v0
  rw [u (fun i x => v i (swapper _ _ _ x)),w] at v0
  exact v0

theorem bitstring_swap
    (u : r.Has (tally ∘ n)) (hp : Told r P) (hg : Told r G) (hb : Told r B)
    (bound : ∀ i n0,n0∈P i ++ G i ++ B i → n0≤base)
    (L t : I→ℕ) (h : ∀i,t i ≤ L i)
    (v : (i:I)→SpanKey (P i) (G i) (B i) (Block 2 (n i))→List Bool)
    (sizes : ∀ i a,(v i a).length=t i) :
    let s i := stock 2 (P i) (G i) (B i) (n i)
    Breeze (modes n (τ:=Net.Motif.sigma)) r (fun i=>(s i).count) L
      (together r.header (stackRun s (fun i a => Code.send (v i a))))
      (stackRun s (fun i a => Code.send (v i (swapper _ _ _ a)))) := by
  let m (i:I) := Series.natural (t i)
  let V i a := notify.symm ∘ (m i).untab (v i a) (by simp [m,sizes])
  have e := rectBead P G B n u hp hg hb bound L m (fun i => by simpa [m] using h i) V
  have eq i a : stripe (m i) (fun b => Code.send (V i a b)) = Code.send (v i a) := by
    have f : (fun b => Code.send (V i a b))=fun b => Code.send ((m i).untab (v i a) (by simp [m,sizes]) b) := by
      funext b
      change Code.Tree.atom (notify (notify.symm _))=Code.Tree.atom _
      rw [Equiv.apply_symm_apply]
    rw [f,stripe_eq',Series.recover]
  unfold cloth at e; simp_rw [eq] at e
  exact e
end Spindle

end IntegerMultiplication
end Computability
end OAI
