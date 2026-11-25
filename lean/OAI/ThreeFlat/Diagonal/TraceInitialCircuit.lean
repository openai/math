import OAI.ThreeFlat.Diagonal.TraceCanonical
import OAI.ThreeFlat.Diagonal.TraceAdjacent

namespace OAI
/-! # The initial CPU register constraint -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM TraceBanks TraceWords
open Computability.VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r : ℕ} {σ : Type*}

private def literals {b : ℕ} (x : Word b) : Fin b → Expr σ := fun k => .const (bits x k)

/-- Compare the canonical row's active tag, public entry counter, persistent
input word, and zero-initialized registers. -/
def initialCheck (hp : p ≤ 2^(w+1)) (entry : Fin p) (state : Fin (w+1) → Expr σ)
    (raw : CodePin w r → Expr σ) : Expr σ :=
  let word (j : Fin (5+r)) := fun k => raw (j,k)
  (Expr.not (sameWord (word ((0 : Fin 5).castAdd r)) (literals 0))).and
    ((sameWord (word ((1 : Fin 5).castAdd r)) (literals (entry.castLE hp))).and
      ((sameWord (word ((2 : Fin 5).castAdd r)) state).and
        (allBits fun i => sameWord (word (Fin.natAdd 5 i)) (literals 0))))

theorem initialCheck_at (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (entry : Fin p) (st : Word w)
    (state : Fin (w+1) → Expr σ) (raw : CodePin w r → Expr σ) (x : σ → Bool)
    (row : Row (w+1) (Snapshot w p r)) (hstate : ∀ k, (state k).eval x = bits (wide st) k)
    (hraw : ∀ j k, (raw (j,k)).eval x = bits ((rowFormat hw hp).words row j) k) :
    (initialCheck hp entry state raw).eval x = true ↔ before row = some ⟨entry,st,fun _ => 0⟩ := by
  have test (j : Fin 5) (v : Word (w+1)) :
      (sameWord (fun k => raw (j.castAdd r,k)) (literals v)).eval x = true ↔ header hw hp row j = v := by
    apply sameWord_at
    · intro k; simpa using hraw (j.castAdd r) k
    · intro k; rfl
  have hs : (sameWord (fun k => raw ((2 : Fin 5).castAdd r,k)) state).eval x = true ↔
      header hw hp row 2 = wide st := by
    apply sameWord_at _ _ _ _ hstate
    intro k; simpa using hraw ((2 : Fin 5).castAdd r) k
  have hr (j : Fin r) :
      (sameWord (fun k => raw (Fin.natAdd 5 j,k)) (literals 0)).eval x = true ↔ regs row j = 0 := by
    apply sameWord_at
    · intro k; simpa using hraw (Fin.natAdd 5 j) k
    · intro k; rfl
  have tag : (sameWord (fun k => raw ((0 : Fin 5).castAdd r,k)) (literals 0)).eval x =
      decide (header hw hp row 0 = 0) := by
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using test 0 0
  simp only [initialCheck, Expr.eval, Bool.and_eq_true, tag, Bool.not_eq_true', decide_eq_false_iff_not,
    test, hs, allBits_true, hr]
  have wide_inj : Function.Injective (wide (w:=w)) := fun a b h => by
    simpa only [narrow_wide] using congrArg narrow h
  have hwz (z : Word w) : wide z = 0 ↔ z = 0 := by
    change wide z = wide (0 : Word w) ↔ _
    exact wide_inj.eq_iff
  have hpc (a : Fin p) : pcWord hp a = entry.castLE hp ↔ a = entry := by
    constructor
    · intro h
      exact Fin.ext (congrArg (fun z : Word (w+1) => z.val) h)
    · rintro rfl; rfl
  have hv (a : Snapshot w p r) : a.pc = entry ∧ a.persistent = st ∧ (∀ i, a.reg i = 0) ↔
      some a = some (⟨entry, st, fun _ => 0⟩ : Snapshot w p r) := by
    cases a with
    | mk pc st' reg =>
      constructor
      · rintro ⟨rfl,rfl,hr⟩
        have he : reg = fun _ => 0 := funext hr
        rw [he]
      · intro e
        have he := Option.some.inj e
        exact ⟨congrArg Snapshot.pc he,congrArg Snapshot.persistent he,
          fun i => congrFun (congrArg Snapshot.reg he) i⟩
  have hn (t : Fin 8) (h : t.val ≠ 0) : tagWord hw t ≠ 0 := fun he =>
    h (congrArg (fun z : Word (w+1) => z.val) he)
  cases row with
  | pad => simp [header, before]
  | halt a out =>
    cases out <;> simpa [header,before,regs,hpc,hwz,wide_inj.eq_iff,hn,Function.comp_def] using hv a
  | move a e =>
    cases e with
    | choice b =>
      cases b <;> simpa [header,before,regs,hpc,hwz,wide_inj.eq_iff,hn,Function.comp_def] using hv a
    | tick | read | write =>
      simpa [header,before,regs,hpc,hwz,wide_inj.eq_iff,hn,Function.comp_def] using hv a

/-- A canonical row's initial-state predicate needs one word equality per
register and three fixed control fields. -/
theorem initialCheck_size (hp : p ≤ 2^(w+1)) (entry : Fin p) (state : Fin (w+1) → Expr σ)
    (raw : CodePin w r → Expr σ) (hs : ∀ i, (state i).size ≤ 1) (hr : ∀ j, (raw j).size ≤ 1) :
    (initialCheck hp entry state raw).size ≤ (r+4)*((w+1)*10+2)+6 := by
  let words := fun j : Fin (5+r) => fun b => raw (j,b)
  have ctl (j : Fin (5+r)) (x : Word (w+1)) :
      (sameWord (words j) (literals x)).size ≤ (w+1)*10+1 :=
    sameWord_size_le _ _ (s:=1) (t:=1) (fun b => hr (j,b)) (fun _ => le_rfl)
  have st := sameWord_size_le (words ((2 : Fin 5).castAdd r)) state
    (s:=1) (t:=1) (fun b => hr _) hs
  have regs := allBits_size_le (fun j : Fin r => sameWord (words (Fin.natAdd 5 j)) (literals 0))
    (fun j => ctl (Fin.natAdd 5 j) 0)
  have tag := ctl ((0 : Fin 5).castAdd r) 0
  have pc := ctl ((1 : Fin 5).castAdd r) (entry.castLE hp)
  simp only [initialCheck,Expr.size]
  dsimp only [words] at st regs tag pc
  ring_nf at st regs tag pc ⊢
  omega

end ThreeFlat.Diagonal.TraceRows

end OAI
