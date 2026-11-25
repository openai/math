import OAI.Computability.NearSquareRoot.InterchangeROMAddressStep
import OAI.Computability.NearSquareRoot.InterchangeROMLegalWord

/-! # One effective physical program for a finite word of movements -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OpcodeProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Port
  IntegerMultiplication.Loom IntegerMultiplication.Adic IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims InterchangeROMAddress InterchangeAddress
  InterchangeSpace GeneratorSyntax

noncomputable def word (b n : ℕ) (ops : Opcode.Word) : Cmd :=
  InterchangeROMSequence.command (dispatch b n) ops

theorem word_effective {X : Type} [Primcodable X] {b n : X → ℕ} {ops : X → Opcode.Word}
    (hb : Computable b) (hn : Computable n) (ho : Computable ops) :
    Effective ltr fun x => word (b x) (n x) (ops x) :=
  InterchangeROMSequence.effective_family (fun x => dispatch (b x) (n x))
    (effective (hb.comp Computable.fst) (hn.comp Computable.fst) Computable.snd) ho

theorem word_within : ∃ R, ∀ b n o, CommonRegisters.Within R (word b n o) := by
  obtain ⟨R,hr⟩ := within
  exact ⟨max 3 R, fun b n ops => InterchangeROMSequence.within (le_max_left ..)
    (dispatch b n) (fun m => RegisterSelect.within_mono (le_max_right ..) _ (hr b n m)) ops⟩

theorem cost_congr (c : Clocks) (b n : ℕ) (op : Opcode.Op) (h : Header) (N : ℕ)
    {x y a z : Tree} (hx : x.count = a.count) (hy : y.count = z.count) :
    cost c b n op h N x y = cost c b n op h N a z := by simp only [cost,scan,Affine.scanPrice,pivotPrice,hx,hy]

/-- The complete dispatcher realizes the pullback by the P192 address
permutation. Its sum of local prices, maximum stack prices, and the
number and type of child requests refer to the actual serialized program. -/
theorem run_word : ∃ c : Clocks, ∀ {n b f : ℕ} [NeZero b] (P G S : Tape)
    (_ : solid P) (_ : solid G) (_ : solid S) (_ : 2 ≤ b) (l : ℕ)
    (ops : List (Lag (Fin n) b)) (leg : ∀ m∈ops, m.legal (ranking (Equiv.refl (Fin n))))
    (v : Keys P G S (Fin n) (Block b f) → Tree) (good : Tree → Prop) (_ : ∀ k, good (v k)),
    let ord := Equiv.refl (Fin n)
    let s := arrays ord (line b f) P G S
    let h := header f P G S
    let src := stripe s v
    let dst := stripe s (v ∘ (recreation ord P G S f ops leg).symm)
    let tick := fun o => cost c b n (Opcode.encode o) h s.count src src
    ∃ qs, qs.length = (ops.map Lag.prices).sum ∧
      (∀ q∈qs, Valid (b:=b) f s.count l P G S good q) ∧
      InterchangeROMSequence.Step (Request.job b) (word b n (ops.map Opcode.encode)) (send h) src dst qs
        ((ops.map tick).sum+(ops.length+1)*(110*((send h).count+1)))
        (InterchangeBatch.dataSpace src.count (send h).count (childPeak tick ops))
        (InterchangeBatch.returnSpace (send h).count (childPeak tick ops)) := by
  obtain ⟨c,atomic⟩ := run_step
  refine ⟨c,?_⟩
  intro n b f nz P G S p g s hb l ops leg v good mem
  let ord := Equiv.refl (Fin n)
  let rows := arrays ord (line b f) P G S
  let src := stripe rows v
  let h := header f P G S
  let tick (op : Lag (Fin n) b) := cost c b n (Opcode.encode op) h rows.count src src
  apply InterchangeROMSequence.run_legal ord P G S f (dispatch b n) (send h) ops leg v _ tick tick tick
  intro op hop e
  obtain ⟨qs,card,val,run⟩ := atomic P G S p g s hb l op hop (v ∘ e.symm) good (fun k => mem _)
  let next := e.trans (reflect ord op hop P G S f)
  have same (q : Equiv.Perm _) : (stripe rows (v ∘ q.symm)).count = src.count := by
    simpa only [src,stripe_eq,size] using AffineAddress.tab_volume_eq rows q.symm v
  have eq := cost_congr c b n (Opcode.encode op) h rows.count (same e) (same next)
  refine ⟨qs,card,val,?_⟩
  let t := cost c b n (Opcode.encode op) h rows.count (stripe rows (v ∘ e.symm)) (stripe rows (v ∘ next.symm))
  change InterchangeROMSequence.Step _ _ _ _ _ _ t t t at run
  change t = tick op at eq
  rw [eq] at run
  exact run

end OpcodeProgram

end NearSquareRoot
end Computability
end OAI
