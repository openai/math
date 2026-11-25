import OAI.Computability.NearSquareRoot.FixedCandidateArenaLiteral
import OAI.Computability.NearSquareRoot.FixedLayerEffectivePlans
import OAI.Computability.NearSquareRoot.FixedLayerClock

/-! # Compiling the physical permutation and Walsh rows on every parameter tuple -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveBoundedTask.Family

open IntegerMultiplication Code GeneratorSyntax

/-- Reindex emitted programs through a computable enumeration. The input sets,
logical data and resource bounds are allowed to depend on the original index. -/
theorem reindex {P Q : Type} [Primcodable P] [Primcodable Q] {I : P → Type}
    {t s : ∀ p, I p → ℕ} {u v : ∀ p, I p → Tree} (h : EffectiveBoundedTask.Family t s u v)
    (e : Q → P) (he : Computable e) :
    EffectiveBoundedTask.Family (fun q => t (e q)) (fun q => s (e q))
      (fun q => u (e q)) (fun q => v (e q)) := by
  obtain ⟨c,R,hc,hR,runs⟩ := h
  exact ⟨c ∘ e,R,hc.comp he,hR,fun q => runs (e q)⟩

end EffectiveBoundedTask.Family

namespace FixedCandidate

open IntegerMultiplication Code DigitPacking FixedPoint FixedLayer EffectiveBoundedTask Filter

abbrev Tuple := ℕ × ℕ × ℕ

def decodeTuple (p : ℕ) : Tuple := (p.unpair.1,p.unpair.2.unpair)
def encodeTuple (j a b : ℕ) : ℕ := Nat.pair j (Nat.pair a b)

theorem decodeTuple_primrec : Primrec decodeTuple :=
  (Primrec.fst.comp Primrec.unpair).pair (Primrec.unpair.comp (Primrec.snd.comp Primrec.unpair))

@[simp] theorem decode_encodeTuple (j a b : ℕ) : decodeTuple (encodeTuple j a b) = (j,a,b) := by
  simp [decodeTuple,encodeTuple]

def rowClocks (route row : ℕ → ℕ) : Clocks := ⟨route,wordClock row,wordClock row⟩

/-- Two running CRT commands plus directional permutation and Walsh row
commands supply the actual generated arithmetic files. Any computable
enumeration can be used, including triples of arbitrary reserve guesses. -/
theorem arenaFiles_of_rows {P : Type} [Primcodable P] (enum : ℕ → P) (he : Computable enum)
    (K : P → ℕ) (hK : Computable K) (hN : ∀ p, 2 ≤ K p)
    (hv : ∀ p (i : LargeInput (K p)), Directory i.val.width)
    (hd : ∀ p (i : LargeInput (K p)), 4 ≤ (box i.val.width).length)
    (hk : ∀ p (i : LargeInput (K p)), 1024 ≤ addressBits i.val.width)
    (A routeTick rowTick : P → ℕ → ℕ) (ha : ∀ p n, n ≤ A p n)
    (lin : ∀ p (i : LargeInput (K p)), A p i.val.width ≤ rowTick p i.val.width)
    (hl : ∀ p (i : LargeInput (K p)), phaseClock i.val.width ≤ rowTick p i.val.width)
    (crt : EffectiveCRTAt K A routeTick (fun p i => route (hv p i)))
    (undo : EffectiveCRTAt K A routeTick (fun p i => afterInverseCRT (hv p i)))
    (perm : ∀ dir : Bool, EffectiveImplementsAt (fun p (i : LargeInput (K p)) => i.val.width) hv
      (fun _ _ => dir) hd A rowTick .permutation)
    (walsh : ∀ dir : Bool, EffectiveImplementsAt (fun p (i : LargeInput (K p)) => i.val.width) hv
      (fun _ _ => dir) hd A rowTick .walsh) :
    Nonempty (ArenaFiles
      (fun j => clockAt (rowClocks (routeTick (enum j)) (rowTick (enum j))) (A (enum j)))
      (fun j => arenaAt (A (enum j)))) := by
  obtain ⟨plans,F,J⟩ := effectivePlansAt K hN hv hd hk A rowTick (fun p i => ha p i.val.width)
    lin hl perm walsh
  let c p := rowClocks (routeTick p) (rowTick p)
  let T p n := (c p).total n+A p n
  have ops : EffectiveTransportsAt K hv plans c A := ⟨crt,undo,F,J⟩
  have large := effective_largeTask_atArena K hv plans c A T hN ha (fun _ _ => Nat.le_add_left ..)
    (fun _ _ => Nat.le_add_right ..) ops
  have full := (effective_all_widths_atArena K hK T A ha large).reindex enum he
  obtain ⟨cmd,R,ce,hR,ok⟩ := full
  choose coeff body using fun p => (ok p).2
  exact ⟨⟨R,hR,cmd,ce,fun p => (ok p).1,coeff,body⟩⟩

/-- Time and workspace of one good tuple with a logarithmic row slack. -/
theorem rowClocks_good {route row A : ℕ → ℕ} {ρ γ : ℝ} (hr : 0 ≤ ρ) (hg : ρ < γ)
    (ha : ∃ L : ℕ, ∀ᶠ n in atTop, A n ≤ L*(n+1))
    (hroute : ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (route n : ℝ) ≤ C*n*logScale n^γ)
    (hrow : RowClock ρ row) :
    (∃ L : ℕ, ∀ᶠ n in atTop, arenaAt A n ≤ L*(n+1)) ∧
      ∃ C : ℝ, 0 < C ∧ ∀ᶠ n in atTop, (clockAt (rowClocks route row) A n : ℝ) ≤ C*n*logScale n^γ := by
  apply good_arena_clock _ _ (hr.trans_lt hg) ha
  intro op hm
  have ft := (hrow.transform hr).eventually_le hr hg
  simp only [rowClocks,List.mem_cons,List.not_mem_nil,or_false,or_self] at hm
  rcases hm with rfl | rfl
  · exact hroute
  · exact ft

end FixedCandidate

end NearSquareRoot
end Computability
end OAI
