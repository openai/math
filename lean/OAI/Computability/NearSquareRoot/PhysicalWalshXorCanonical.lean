import OAI.Computability.NearSquareRoot.PhysicalWalshXorRowData
import OAI.Computability.NearSquareRoot.CRTPositionOpcodeCall
import OAI.Computability.NearSquareRoot.CRTPositionProgramRowTransport
import OAI.Computability.NearSquareRoot.CRTControlledPrefixClock

/-! # Canonical opcode commands on the actual XOR payload series

The fixed prefix computes a unary width and an opcode from the caller's
descriptor. The canonical command then sees the same serialized record
bits in the order of the actual payload series.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication Code Adic Strip Staff Loom Packed Controlled Controlled.PositionProgram NamedPacked

private theorem timesAt {I : Type} {c : Cmd} {a b : I → ℝ} {u v : I → Tree}
    (h : CarriesAt c a u v) (hb : ∀ i,1≤b i) (C : ℕ) (scale : ∀ i,a i≤(C:ℝ)*b i) :
    CarriesAt c b u v := by
  obtain ⟨t,run,D,cost⟩ := h.work
  refine ⟨hb,⟨t,run,D*C,fun i => ?_⟩,(h.forget.times hb C scale).small⟩
  exact (cost i).trans (by rw [Nat.cast_mul,mul_assoc]; exact mul_le_mul_of_nonneg_left (scale i) (Nat.cast_nonneg D))

/-- A single header preparation works for all eligible canonical opcode
programs and all their exponents on the specified joint input domain. -/
theorem opcodeFromCanonical {I : Type} {r : Regime I} (k : I → ℕ) (op : I → Op)
    (hk : Realizes r k) (hop : r.Has op) (legal : ∀ i, WellFormed (k i) (guardWidth (k i)) (op i))
    {U : I → Type} (u : (i : I) → Series (U i)) (f : (i : I) → Block 2 (k i) → U i → Bead) :
    ∃ prep : Cmd, (∀ c ρ, OpAt c ρ id →
      BreezeAt (prep.join c) (Spindle.modes k (τ:=ρ)) r (fun i => (line 2 (k i)).count) (fun i => (u i).count)
        (fun i => Tree.fork (r.header i) (stripe (line 2 (k i)) (fun a => strip (u i) (f i a))))
        (fun i => stripe (line 2 (k i)) (fun a => strip (u i) (f i (nativeOp (k i) (guardWidth (k i)) (op i) a))))) ∧
    ∀ c (time : Call id → ℕ), EffectiveTask.Runs c time Call.input Call.output →
      ∃ t, EffectiveTask.Runs (prep.join c) t
        (fun i => Tree.fork (r.header i) (stripe (line 2 (k i)) (fun a => strip (u i) (f i a))))
        (fun i => stripe (line 2 (k i)) (fun a => strip (u i) (f i (nativeOp (k i) (guardWidth (k i)) (op i) a)))) := by
  let n (i : I) := (line 2 (k i)).count
  let w (i : I) := (u i).count
  let data (i : I) := stripe (line 2 (k i)) (fun a => strip (u i) (f i a))
  let key (i : I) := send (tally (k i),op i)
  have hn (i : I) : 1 ≤ n i := by simp only [n,lineSize]; exact Nat.two_pow_pos _
  have alive : Alive r n w data := by
    refine ⟨0,Carries.idles (unit_mass hn 0) ⟨3,?_⟩⟩
    intro i
    have size := position_row_count (k i) (u i) (f i)
    simp only [mass,n,w,lineSize,pow_zero]
    change ((data i).count:ℝ) ≤ _
    dsimp only [data]
    exact_mod_cast (show (cloth (fun i => line 2 (k i)) u f i).count ≤ 3*(2^(k i)*((u i).count+1)) by
      rw [←Nat.mul_assoc]; exact size)
  have head : Rip r n w r.header key := Rip.header hn (Regime.Has.pair hk hop)
  obtain ⟨d,launch⟩ := head.left alive
  obtain ⟨prep,start⟩ := CarriesAt.exists_of_carries launch
  let pick (i : I) : Call id := ⟨k i,op i,legal i,w i,fun a j => f i a ((u i).follow j)⟩
  have cell (i : I) (a : Block 2 (k i)) :
      strip (Series.natural (w i)) ((pick i).data a) = strip (u i) (f i a) :=
    stripe_natural_follow (u i) (fun j => send (f i a j))
  have entry : Call.input ∘ pick = together key data := by
    funext i
    exact congrArg (Tree.fork _) (congrArg (stripe _) (funext (cell i)))
  have exit : Call.output ∘ pick = fun i => stripe (line 2 (k i))
      (fun a => strip (u i) (f i (nativeOp (k i) (guardWidth (k i)) (op i) a))) := by
    funext i
    exact congrArg (stripe _) (funext (fun a => cell i (nativeOp (k i) (guardWidth (k i)) (op i) a)))
  refine ⟨prep,?_,?_⟩
  · intro c ρ canonical
    let rate := Spindle.modes k (τ:=ρ)
    have hrate i : 1 ≤ rate i := canonical.1 (pick i)
    have pre : BreezeAt prep rate r n w (together r.header data) (together key data) :=
      ⟨hrate,d,start.larger (fun i => le_mul_of_one_le_right (zero_le_one.trans (unit_mass hn d i)) (hrate i))⟩
    obtain ⟨_,b,body⟩ := canonical
    have call := body.on pick
    have small : Dom r.scale k := (Regime.Small.extent hk).mono (fun x => by
      change k x ≤ size (tally (k x)); simp only [size_tally,tally_length]; omega)
    obtain ⟨e,C,space⟩ := PrefixCommand.rebase (n:=n) (w:=w) k small b
    have carry := timesAt call (fun i => one_le_mul_of_one_le_of_one_le (unit_mass (r:=r) (l:=w) hn e i) (hrate i))
      C (fun i => by
        change mass (Call.regime id) _ _ b (pick i) * rate i ≤ (C:ℝ)*(mass r n w e i*rate i)
        rw [←mul_assoc]
        exact mul_le_mul_of_nonneg_right (space i) (zero_le_one.trans (hrate i)))
    rw [entry,exit] at carry
    exact pre.next ⟨hrate,e,carry⟩
  · intro c time h
    obtain ⟨t,beginRun,_,_⟩ := start.work
    have core := h.on pick
    rw [entry,exit] at core
    exact ⟨_,beginRun.comp core⟩

/-- Fixed preparation of the canonical opcode packet on each high-spectator row. -/
theorem nativeRowsFromCanonical {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P)
    (hk : Realizes r k) (op : X → Op) (hop : r.Has op)
    (ok : ∀ x, WellFormed (k x) (guardWidth (k x)) (op x))
    {U : X → Type} (u : (x:X) → Series (U x)) (f : (x:X) → Input (P x) (k x) (U x)) :
    ∃ prep : Cmd, (∀ c ρ, OpAt c ρ id → NativeRowAt r P k hP u (prep.join c) ρ op f) ∧
      ∀ c (time : Call id → ℕ), EffectiveTask.Runs c time Call.input Call.output →
      let rr := fixedRowRegime r P hP
      let layout (z : (x:X) × Block 2 (P x)) := line 2 (k z.1)
      let payload (z : (x:X) × Block 2 (P x)) := u z.1
      let read (z : (x:X) × Block 2 (P x)) (b : Block 2 (k z.1)) := f z.1 (prefixBit b) z.2
      ∃ t, EffectiveTask.Runs (prep.join c) t (together rr.header (cloth layout payload read))
        (cloth layout payload (fun z b => read z (nativeOp (k z.1) (guardWidth (k z.1)) (op z.1) b))) :=
  opcodeFromCanonical (fun j : (x:X) × Block 2 (P x) => k j.1) (fun j => op j.1)
    (fixedRowGlobal P hP hk) (fixedRowGlobal P hP hop) (fun j => ok j.1) (fun j => u j.1)
    (fun j a => f j.1 (prefixBit a) j.2)

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
