import OAI.Computability.BorderVNP.RoutingISABroadcastRead
import OAI.Computability.BorderVNP.RoutingISAPartnerLoop

/-! # Comparing one incident prefix word with the copied reference

A failed word comparison rejects in the native instruction table. A successful comparison
changes just the scratch registers and position cursor and never writes shared memory.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM

variable {w : ℕ} {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}

private theorem headerStable_of_low {f : BroadcastFrame} {s t : Bank w}
    (hs : f.Stable (readings s)) (low : ∀ i : Reg, i.val ≤ 9 ∨ i = 14 → t i = s i) :
    f.Stable (readings t) := by
  have h (i : Reg) (hi : i.val ≤ 9 ∨ i = 14) : readings t i = readings s i :=
    congrArg Fin.val (low i hi)
  simp only [BroadcastFrame.Stable, h 0 (by decide), h 1 (by decide), h 2 (by decide),
    h 3 (by decide), h 4 (by decide), h 5 (by decide), h 6 (by decide), h 7 (by decide),
    h 8 (by decide), h 9 (by decide), h 14 (by decide)]
  exact hs

private theorem eq_from_return {x y : Reg} {s m es t mt}
    (r : Runs pub macros (requireEq x y) s m es t mt) : s x = s y := by
  obtain ⟨_,_,h⟩ := r.splitEq
  by_contra hn
  rw [ite_eq_right hn] at h
  cases h with | atom ha _ _ => cases ha

/-- One returning comparison checks the actual physical word against the word at the
copied-header address. Conversely, equal words cause a return within the slot bound. -/
theorem compareHeaderBit_paths {m : Memory w} (f : BroadcastFrame)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    {s : Bank w} (stable : f.Stable (readings s)) (partner : (s 11).val < f.teams)
    (other : (s 11).val ≠ f.team) (more : (s 10).val < f.header) :
    ∃ t, f.Stable (readings t) ∧ t 11 = s 11 ∧ (t 10).val = (s 10).val+1 ∧
      ((m (f.addr (s 11).val (s 10).val) = m (f.dst + (s 10).val)) →
        ∃ es, Runs pub macros compareHeaderBit s m es t m ∧ traceCost es ≤ compareHeaderBit.slots) ∧
      ∀ {es u mu}, Runs pub macros compareHeaderBit s m es u mu → u = t ∧ mu = m ∧
        m (f.addr (s 11).val (s 10).val) = m (f.dst + (s 10).val) := by
  obtain ⟨gs,a,read,cost,low⟩ := readPhysical_run f pub macros s m 11 10 12 (by decide)
    image fit partner other (more.trans_le fit.cap)
  have a12 : a 12 = m (f.addr (s 11).val (s 10).val) := by simpa using low 12 (by decide)
  have keep (i : Reg) (hi : i.val < 30) (hd : i ≠ 12) : a i = s i := by simpa [hd] using low i hi
  let b := Function.update a (13 : Reg) (BinaryOp.add.eval (a 9) (a 10))
  have add : Runs pub macros (.binary .add 13 9 10) a m [tick w] b m := .localStep m rfl rfl
  have dest : (s 9).val = f.dst := stable.2.2.2.2.2.2.2.2.2.1
  have ptr : (b 13).val = f.dst + (s 10).val := by
    simp only [b, Function.update_self, BinaryOp.eval, Fin.val_add, keep 9 (by decide) (by decide),
      keep 10 (by decide) (by decide), dest]
    exact Nat.mod_eq_of_lt (by have := fit.out; omega)
  let c := Function.update b (15 : Reg) (m (b 13).val)
  have load : Runs pub macros (.load 15 13) b m
      [⟨.ordinary (some ((b 13).val, none)),[m (b 13).val],[],.plus⟩] c m :=
    Runs.load pub macros 15 13 b m
  have eqv : c 12 = c 15 ↔ m (f.addr (s 11).val (s 10).val) = m (f.dst + (s 10).val) := by
    rw [show c 12 = a 12 from by simp (config := {decide := true}) [c,b],
      show c 15 = m (b 13).val from Function.update_self .., a12, ptr]
  let t := Function.update c (10 : Reg) (BinaryOp.add.eval (c 10) (c 1))
  have inc : Runs pub macros (.binary .add 10 10 1) c m [tick w] t m := .localStep m rfl rfl
  have lowT (i : Reg) (hi : i.val < 30) (h10 : i ≠ 10) (h12 : i ≠ 12) (h13 : i ≠ 13) (h15 : i ≠ 15) :
      t i = s i := by simp [t,c,b,h10,h13,h15,keep i hi h12]
  have st : f.Stable (readings t) := by
    apply headerStable_of_low stable
    intro i hi
    have bound (x : Reg) (hx : 9 < x.val) (hx' : x ≠ 14) : i ≠ x := by
      rintro rfl
      rcases hi with h | h
      · omega
      · exact hx' h
    have small : i.val < 30 := by rcases hi with h | rfl <;> omega
    exact lowT i small (bound 10 (by decide) (by decide)) (bound 12 (by decide) (by decide))
      (bound 13 (by decide) (by decide)) (bound 15 (by decide) (by decide))
  have one : (s 1).val = 1 := stable.2.1
  have next : (t 10).val = (s 10).val + 1 := by
    simp (config := {decide := true}) only [t,c,b, Function.update_self,
      Function.update_of_ne (by decide : (10:Reg) ≠ 15), Function.update_of_ne (by decide : (10:Reg) ≠ 13),
      Function.update_of_ne (by decide : (1:Reg) ≠ 15), Function.update_of_ne (by decide : (1:Reg) ≠ 13),
      BinaryOp.eval, Fin.val_add, keep 10 (by decide) (by decide), keep 1 (by decide) (by decide), one]
    exact Nat.mod_eq_of_lt (by have := fit.out; omega)
  have forward (ok : m (f.addr (s 11).val (s 10).val) = m (f.dst + (s 10).val)) :
      ∃ es, Runs pub macros compareHeaderBit s m es t m ∧ traceCost es ≤ compareHeaderBit.slots := by
    have nop : Runs pub macros .nop c m [tick w] c m := .localStep m rfl rfl
    have ck : Runs pub macros (requireEq 12 15) c m [tick w,tick w] c m :=
      .ifEq (by simpa only [eqv.mpr ok, ite_true] using nop)
    refine ⟨_,read.seq (add.seq (load.seq (ck.seq inc))),?_⟩
    change traceCost (gs ++ _) ≤ (readPhysical 11 10 12).slots + _
    simp only [traceCost, VPVNP.RAMBuckets.cost_append]
    change traceCost gs + 5 ≤ (readPhysical 11 10 12).slots + 6
    omega
  refine ⟨t,st,lowT 11 (by decide) (by decide) (by decide) (by decide) (by decide),next,forward,?_⟩
  intro es u mu run
  obtain ⟨_,_,_,_,_,r₀,remaining⟩ := Runs.seq_iff.mp run
  obtain ⟨_,rfl,rfl⟩ := read.unique_of_deterministic (by decide) r₀
  obtain ⟨_,_,_,_,_,r₁,remaining⟩ := Runs.seq_iff.mp remaining
  obtain ⟨_,rfl,rfl⟩ := add.unique_of_deterministic rfl r₁
  obtain ⟨_,_,_,_,_,r₂,remaining⟩ := Runs.seq_iff.mp remaining
  obtain ⟨_,rfl,rfl⟩ := load.unique_of_deterministic rfl r₂
  obtain ⟨_,_,_,_,_,guard,_⟩ := Runs.seq_iff.mp remaining
  have ok := eqv.mp (eq_from_return guard)
  obtain ⟨_,normal,_⟩ := forward ok
  obtain ⟨_,hu,hm⟩ := run.unique_of_deterministic (by decide) normal
  exact ⟨hu,hm,ok⟩

end RoutingISA

end BorderVNP
end Computability
end OAI
