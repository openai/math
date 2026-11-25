import OAI.Computability.BorderVNP.CubeScatterDigits
import OAI.Computability.BorderVNP.RoutingISANativeTags

/-! # Finite native dispatch of the owned packet layout

Register 43 names the selector, 44 carries the one-hot coordinate and 45 the
owner bit. Register 59 contains one. The generated code scans consecutive
selector numbers by increment and coordinate masks by doubling. It writes only
register 58 before the selected layout begins. Exhaustion or a nonbinary owner
reaches the rejecting opcode.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter

open RoutingISA VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM DiagonalResidueRAM

private def scan (key : Reg) (advance : Code) : {k : ℕ} → (Fin k → Code) → Code
  | 0, _ => .reject
  | _+1, branches => .ifEq key 58 (branches 0) (.seq advance (scan key advance (branches ∘ Fin.succ)))

private inductive Indexing where
  | selector | coordinate

private def Indexing.key : Indexing → Reg | .selector => 43 | .coordinate => 44

private def Indexing.value : Indexing → ℕ → ℕ | .selector, i => i | .coordinate, i => 2^i

private def Indexing.advance : Indexing → Code
  | .selector => .binary .add 58 58 59
  | .coordinate => .binary .add 58 58 58

private def Indexing.initial : Indexing → Word 8 | .selector => 0 | .coordinate => 1

private def Indexing.lookup {k : ℕ} (idx : Indexing) (branches : Fin k → Code) : Code :=
  .seq (.constant 58 idx.initial) (scan idx.key idx.advance branches)

private def ownerCode (branches : Bool → Code) : Code :=
  .seq (.constant 58 0) (.ifEq 45 58 (branches false) (.ifEq 45 59 (branches true) .reject))

/-- Finite length-independent layout selection on selector, coordinate, and owner. -/
def dispatch {count a : ℕ} (branch : Fin count → Fin a → Bool → Code) : Code :=
  Indexing.selector.lookup fun k => Indexing.coordinate.lookup fun i => ownerCode (branch k i)

private abbrev mark {w : ℕ} (s : Bank w) (x : Word w) := Function.update s (58 : Reg) x

private abbrev ticks {w : ℕ} (k : ℕ) (fs : List (TeamRAM.Event w)) := List.replicate k (tick w) ++ fs

private theorem ticks_add {w : ℕ} (j k : ℕ) (fs : List (TeamRAM.Event w)) :
    ticks j (ticks k fs) = ticks (j+k) fs := by simp only [ticks, List.replicate_add, List.append_assoc]

private theorem ticks_two {w : ℕ} (i : ℕ) (fs : List (TeamRAM.Event w)) :
    ticks (2*(i+1)+1) fs = tick w :: tick w :: ticks (2*i+1) fs := by
  rw [show 2*(i+1)+1 = (2*i+1)+1+1 by omega]
  simp only [ticks, List.replicate_succ, List.cons_append]

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}

private theorem reject_false {s m es t mt} (r : Runs pub mac .reject s m es t mt) : False := by
  cases r with | atom h _ _ => cases h

private theorem ifEq_iff {x y : Reg} {a b : Code} {s m es t mt} :
    Runs pub mac (.ifEq x y a b) s m es t mt ↔ ∃ gs, es = tick w :: gs ∧
      Runs pub mac (if s x = s y then a else b) s m gs t mt := by
  constructor
  · intro h
    cases h with
    | atom h _ _ => cases h
    | ifEq h => exact ⟨_, rfl, h⟩
  · rintro ⟨_,rfl,h⟩
    exact .ifEq h

private theorem seq_tick_iff {a b : Code} {s m u es t mt} (det : a.deterministic = true)
    (head : Runs pub mac a s m [tick w] u m) :
    Runs pub mac (.seq a b) s m es t mt ↔ ∃ gs, es = tick w :: gs ∧ Runs pub mac b u m gs t mt := by
  constructor
  · intro h
    obtain ⟨v,mv,fs,gs,he,hf,hg⟩ := Runs.seq_iff.mp h
    obtain ⟨rfl,rfl,rfl⟩ := hf.unique_of_deterministic det head
    exact ⟨gs, he, hg⟩
  · rintro ⟨_,rfl,h⟩
    exact head.seq h

private theorem Indexing.advance_run (idx : Indexing) (s : Bank w) (m : Memory w)
    (one : s 59 = 1) (i : ℕ) :
    Runs pub mac idx.advance (mark s (word w (idx.value i))) m [tick w]
      (mark s (word w (idx.value (i+1)))) m := by
  apply Runs.localStep m (by cases idx <;> rfl)
  cases idx with
  | selector =>
    simp (config := {decide := true}) [Indexing.advance, Indexing.value, Code.atom, BinaryOp.eval,
      mark, Function.update_of_ne, one, Function.update_idem]
  | coordinate =>
    have h : 2^(i+1) = 2^i+2^i := by rw [pow_succ]; omega
    simp [Indexing.advance, Indexing.value, Code.atom, BinaryOp.eval, mark, Function.update_idem, h]

private theorem Indexing.guard_eq (idx : Indexing) (s : Bank w) (i : ℕ) :
    mark s (word w (idx.value i)) idx.key = mark s (word w (idx.value i)) 58 ↔
    s idx.key = word w (idx.value i) := by
  cases idx <;> simp (config := {decide := true}) [mark, Indexing.key, Function.update_of_ne]

private theorem Indexing.value_inj (idx : Indexing) {i j : ℕ}
    (hi : idx.value i < 2^w) (hj : idx.value j < 2^w)
    (h : word w (idx.value i) = word w (idx.value j)) : i = j := by
  have he := congrArg Fin.val h
  rw [word_val _ _ hi, word_val _ _ hj] at he
  cases idx with
  | selector => exact he
  | coordinate => exact (Nat.pow_right_injective (by decide : 2 ≤ 2)) he

private theorem Indexing.scan_iff (idx : Indexing) (s : Bank w) (m : Memory w) (one : s 59 = 1)
    (off k : ℕ) (branch : Fin k → Code) (fit : ∀ j : Fin k, idx.value (off+j.val) < 2^w)
    {es t mt} : Runs pub mac (scan idx.key idx.advance branch) (mark s (word w (idx.value off))) m es t mt ↔
      ∃ j : Fin k, s idx.key = word w (idx.value (off+j.val)) ∧ ∃ fs,
        es = ticks (2*j.val+1) fs ∧ Runs pub mac (branch j) (mark s (word w (idx.value (off+j.val)))) m fs t mt := by
  induction k generalizing off es with
  | zero =>
    exact ⟨fun h => (reject_false h).elim, fun ⟨j,_⟩ => j.elim0⟩
  | succ k ih =>
    have add_succ (j : Fin k) : (off+1)+j.val = off+j.succ.val := by simp only [Fin.val_succ]; omega
    have fit' (j : Fin k) : idx.value ((off+1)+j.val) < 2^w := by
      rw [add_succ]; exact fit j.succ
    have tail (gs : List (TeamRAM.Event w)) := ih (off+1) (branch ∘ Fin.succ) fit' (es := gs)
    have heq := idx.guard_eq s off
    rw [scan, ifEq_iff]
    constructor
    · rintro ⟨gs,rfl,run⟩
      by_cases he : s idx.key = word w (idx.value off)
      · rw [ite_eq_left (heq.mpr he)] at run
        exact ⟨0, by simpa using he, gs, rfl, by simpa using run⟩
      · rw [ite_eq_right (fun h => he (heq.mp h))] at run
        obtain ⟨hs,rfl,hr⟩ := (seq_tick_iff (by cases idx <;> rfl) (idx.advance_run s m one off)).mp run
        obtain ⟨j,hj,fs,hes,hf⟩ := (tail _).mp hr
        refine ⟨j.succ, by simpa only [add_succ] using hj, fs, ?_, ?_⟩
        · rw [Fin.val_succ, ticks_two, hes]
        · simpa only [Function.comp_apply, add_succ] using hf
    · rintro ⟨j,hj,fs,rfl,hf⟩
      cases j using Fin.cases with
      | zero =>
        have he : s idx.key = word w (idx.value off) := by simpa using hj
        refine ⟨fs, rfl, ?_⟩
        rw [ite_eq_left (heq.mpr he)]
        simpa using hf
      | succ j =>
        have he : s idx.key ≠ word w (idx.value off) := by
          intro h0
          have hv := idx.value_inj (i := off+0) (j := off+j.succ.val) (fit 0) (fit j.succ) (h0.symm.trans hj)
          simp at hv
        refine ⟨tick w :: ticks (2*j.val+1) fs, ticks_two j.val fs, ?_⟩
        rw [ite_eq_right (fun h => he (heq.mp h))]
        apply (seq_tick_iff (by cases idx <;> rfl) (idx.advance_run s m one off)).mpr
        refine ⟨_,rfl,(tail _).mpr ⟨j, ?_, fs, rfl, ?_⟩⟩
        · simpa only [add_succ] using hj
        · simpa only [Function.comp_apply, add_succ] using hf

private theorem Indexing.lookup_iff (idx : Indexing) {k : ℕ} (branch : Fin k → Code)
    (s : Bank w) (m : Memory w) (one : s 59 = 1) (fit : ∀ j : Fin k, idx.value j.val < 2^w)
    {es t mt} : Runs pub mac (idx.lookup branch) s m es t mt ↔
      ∃ j : Fin k, s idx.key = word w (idx.value j.val) ∧ ∃ fs,
        es = ticks (2*j.val+2) fs ∧ Runs pub mac (branch j) (mark s (word w (idx.value j.val))) m fs t mt := by
  have init : Runs pub mac (.constant 58 idx.initial) s m [tick w] (mark s (word w (idx.value 0))) m :=
    Runs.localStep m rfl (by cases idx <;> rfl)
  have tail (gs : List (TeamRAM.Event w)) :=
    idx.scan_iff (pub := pub) (mac := mac) s m one 0 k branch (by simpa using fit) (es := gs) (t := t) (mt := mt)
  simp only [Nat.zero_add] at tail
  rw [lookup, seq_tick_iff rfl init]
  constructor
  · rintro ⟨gs,rfl,h⟩
    obtain ⟨j,hj,fs,rfl,hf⟩ := (tail gs).mp h
    exact ⟨j,hj,fs,rfl,hf⟩
  · rintro ⟨j,hj,fs,rfl,hf⟩
    exact ⟨_, rfl, (tail _).mpr ⟨j,hj,fs,rfl,hf⟩⟩

private theorem owner_iff (branch : Bool → Code) (s : Bank w) (m : Memory w)
    (one : s 59 = 1) (hne : (1 : Word w) ≠ 0) {es t mt} :
    Runs pub mac (ownerCode branch) s m es t mt ↔ ∃ b : Bool, s 45 = wordBit w b ∧ ∃ fs,
      es = ticks (2+b.toNat) fs ∧ Runs pub mac (branch b) (mark s 0) m fs t mt := by
  have init : Runs pub mac (.constant 58 0) s m [tick w] (mark s 0) m := Runs.localStep m rfl rfl
  have h0 : mark s 0 45 = mark s 0 58 ↔ s 45 = 0 := by simp (config := {decide := true}) [mark,Function.update]
  have h1 : mark s 0 45 = mark s 0 59 ↔ s 45 = 1 := by simp (config := {decide := true}) [mark,Function.update,one]
  rw [ownerCode, seq_tick_iff rfl init]
  constructor
  · rintro ⟨gs,rfl,r⟩
    obtain ⟨hs,rfl,guard⟩ := ifEq_iff.mp r
    by_cases hz : s 45 = 0
    · rw [ite_eq_left (h0.mpr hz)] at guard
      exact ⟨false,hz,hs,rfl,guard⟩
    · rw [ite_eq_right (fun h => hz (h0.mp h))] at guard
      obtain ⟨fs,rfl,test⟩ := ifEq_iff.mp guard
      by_cases hu : s 45 = 1
      · rw [ite_eq_left (h1.mpr hu)] at test
        exact ⟨true,hu,fs,rfl,test⟩
      · rw [ite_eq_right (fun h => hu (h1.mp h))] at test
        exact (reject_false test).elim
  · rintro ⟨b,hb,fs,rfl,hf⟩
    cases b with
    | false =>
      refine ⟨_, rfl, ifEq_iff.mpr ⟨fs,rfl,?_⟩⟩
      rwa [ite_eq_left (h0.mpr hb)]
    | true =>
      have hu : s 45 = 1 := hb
      have hz : s 45 ≠ 0 := hu.symm ▸ hne
      refine ⟨_,rfl,ifEq_iff.mpr ⟨_,rfl,?_⟩⟩
      rw [ite_eq_right (fun h => hz (h0.mp h))]
      refine ifEq_iff.mpr ⟨fs,rfl,?_⟩
      rwa [ite_eq_left (h1.mpr hu)]

/-- Exact number of ordinary positive ticks before the branch, including all
failed candidates and the valid owner test. -/
def dispatchTicks {count a : ℕ} (k : Fin count) (i : Fin a) (owner : Bool) : ℕ :=
  2*k.val + 2*i.val + 6 + owner.toNat

/-- Linear dispatch cost in the two finite table dimensions. -/
theorem dispatchTicks_le {count a : ℕ} (k : Fin count) (i : Fin a) (owner : Bool) :
    dispatchTicks k i owner ≤ 2*(count+a)+3 := by
  have hk := k.isLt
  have hi := i.isLt
  have hb := owner.toNat_le
  unfold dispatchTicks
  omega

/-- Complete forward and inverse execution of the dispatcher. The prefix is
probe-free and contains no choices. At the branch entry register 58 contains
zero, all other registers retain their values, and the memory is unchanged. -/
theorem dispatch_iff {count a : ℕ} (branch : Fin count → Fin a → Bool → Code) (s : Bank w) (m : Memory w)
    (one : s 59 = 1) (fit : max count (2^a) < 2^w) {es t mt} :
    Runs pub mac (dispatch branch) s m es t mt ↔ ∃ k : Fin count, ∃ i : Fin a, ∃ owner : Bool,
      s 43 = word w k.val ∧ s 44 = word w (2^i.val) ∧ s 45 = wordBit w owner ∧
      ∃ fs, es = List.replicate (dispatchTicks k i owner) (tick w) ++ fs ∧
        Runs pub mac (branch k i owner) (Function.update s (58 : Reg) 0) m fs t mt := by
  let byCoord (k : Fin count) := Indexing.coordinate.lookup fun i => ownerCode (branch k i)
  let bankK (k : Fin count) := mark s (word w k.val)
  let bankI (i : Fin a) := mark s (word w (2^i.val))
  have fitsK (k : Fin count) : Indexing.selector.value k.val < 2^w :=
    k.isLt.trans ((le_max_left ..).trans_lt fit)
  have fitsI (i : Fin a) : Indexing.coordinate.value i.val < 2^w :=
    (Nat.pow_le_pow_right (by decide : 1 ≤ 2) i.isLt.le).trans_lt ((le_max_right ..).trans_lt fit)
  have keyLookup := Indexing.selector.lookup_iff (pub := pub) (mac := mac) byCoord s m one fitsK (es := es) (t := t) (mt := mt)
  change Runs pub mac (Indexing.selector.lookup byCoord) s m es t mt ↔ _
  rw [keyLookup]
  have coords (k : Fin count) (gs : List (TeamRAM.Event w)) :
      Runs pub mac (byCoord k) (bankK k) m gs t mt ↔
      ∃ i : Fin a, s 44 = word w (2^i.val) ∧ ∃ hs, gs = ticks (2*i.val+2) hs ∧
        Runs pub mac (ownerCode (branch k i)) (bankI i) m hs t mt := by
    simpa (config := {decide := true}) only [Indexing.key, Indexing.value, byCoord, bankK, bankI,
      mark, Function.update_of_ne (show (44 : Reg) ≠ 58 by decide), Function.update_idem] using
      (Indexing.coordinate.lookup_iff (fun i => ownerCode (branch k i)) (bankK k) m
        (by simpa (config := {decide := true}) [bankK, mark, Function.update] using one) fitsI (es := gs) (t := t) (mt := mt) (pub := pub) (mac := mac))
  have hne : (1 : Word w) ≠ 0 := by
    have hfit : 1 < 2^w := (Nat.one_le_pow a 2 (by decide)).trans_lt ((le_max_right ..).trans_lt fit)
    intro he
    have hz : (word w 1).val = (word w 0).val := congrArg Fin.val he
    rw [word_val _ _ hfit, word_val _ _ (by omega)] at hz
    contradiction
  have owns (k : Fin count) (i : Fin a) (hs : List (TeamRAM.Event w)) :
      Runs pub mac (ownerCode (branch k i)) (bankI i) m hs t mt ↔ ∃ b : Bool, s 45 = wordBit w b ∧
      ∃ fs, hs = ticks (2+b.toNat) fs ∧ Runs pub mac (branch k i b) (mark s 0) m fs t mt := by
    simpa only [bankI, mark, Function.update_of_ne (show (45 : Reg) ≠ 58 by decide), Function.update_idem] using
      (owner_iff (branch k i) (bankI i) m (by simpa (config := {decide := true}) [bankI, mark, Function.update] using one)
        hne (es := hs) (t := t) (mt := mt) (pub := pub) (mac := mac))
  have clock (k : Fin count) (i : Fin a) (b : Bool) (fs : List (TeamRAM.Event w)) :
      ticks (2*k.val+2) (ticks (2*i.val+2) (ticks (2+b.toNat) fs)) = ticks (dispatchTicks k i b) fs := by
    rw [ticks_add, ticks_add, dispatchTicks]
    congr 1
    omega
  constructor
  · rintro ⟨k,hk,gs,rfl,hr⟩
    obtain ⟨i,hi,hs,rfl,hc⟩ := (coords k gs).mp hr
    obtain ⟨b,hb,fs,rfl,hf⟩ := (owns k i hs).mp hc
    exact ⟨k,i,b,hk,hi,hb,fs,clock k i b fs,hf⟩
  · rintro ⟨k,i,b,hk,hi,hb,fs,rfl,hf⟩
    refine ⟨k,hk,_,(clock k i b fs).symm,(coords k _).mpr ⟨i,hi,_,rfl,(owns k i _).mpr ⟨b,hb,fs,rfl,hf⟩⟩⟩

/-- Native layout branches give a fully native dispatch table, even when the number of
selectors and coordinates is a symbolic parameter. -/
theorem dispatch_nativeOnly {count a : ℕ} (branch : Fin count → Fin a → Bool → Code)
    (native : ∀ k i owner, (branch k i owner).nativeOnly = true) : (dispatch branch).nativeOnly = true := by
  have scanNative (key : Reg) (step : Code) (hs : step.nativeOnly = true) (l : ℕ) (f : Fin l → Code)
      (hf : ∀ i, (f i).nativeOnly = true) : (scan key step f).nativeOnly = true := by
    induction l with
    | zero => rfl
    | succ l ih =>
      simp only [scan,Code.nativeOnly,hf,hs,Bool.true_and]
      exact ih _ (fun j => hf j.succ)
  have lookup (idx : Indexing) {l : ℕ} (f : Fin l → Code) (hf : ∀ i, (f i).nativeOnly = true) :
      (idx.lookup f).nativeOnly = true := by
    simp only [Indexing.lookup,Code.nativeOnly,Bool.true_and]
    exact scanNative _ _ (by cases idx <;> rfl) _ f hf
  apply lookup
  intro k
  apply lookup
  intro i
  simp [ownerCode,Code.nativeOnly,native]

end Cube.Scatter

end BorderVNP
end Computability
end OAI
