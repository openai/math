import OAI.Computability.BorderVNP.RoutingISABroadcastRead
import OAI.Computability.BorderVNP.RoutingISATableState

/-!
# Exact memory image after copying the reference prefix

The evaluator copies one bit at a time from an actual physical block, checks
that its word encoding is zero or one, and uses at most a constant number of
word instructions per copied bit. Every other address retains its previous
contents.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

/-- The reference block after the first `count` positions have been copied. -/
def BroadcastFrame.copied (f : BroadcastFrame) (m : ℕ → ℕ) (count addr : ℕ) : ℕ :=
  if f.dst ≤ addr ∧ addr-f.dst < count then m (f.addr f.partner (addr-f.dst)) else m addr

private theorem copied_zero (f : BroadcastFrame) (m : ℕ → ℕ) : f.copied m 0 = m := by
  funext a
  simp [BroadcastFrame.copied]

private theorem copied_next (f : BroadcastFrame) (m : ℕ → ℕ) (i : ℕ) :
    Function.update (f.copied m i) (f.dst+i) (m (f.addr f.partner i)) = f.copied m (i+1) := by
  funext a
  by_cases h : a = f.dst+i
  · subst a; simp [BroadcastFrame.copied]
  · rw [Function.update_of_ne h]
    unfold BroadcastFrame.copied
    split_ifs with h₁ h₂ <;> first | rfl | omega

/-- Original physical words and frame fields precede the output copy. -/
theorem BroadcastFrame.copied_before (f : BroadcastFrame) (m : ℕ → ℕ) (count addr : ℕ)
    (h : addr < f.dst) : f.copied m count addr = m addr := by
  simp [copied,not_le.mpr h]

/-- Every copied bit equals the reference physical bit at the same offset. -/
theorem BroadcastFrame.copied_at (f : BroadcastFrame) (m : ℕ → ℕ) {i count : ℕ}
    (hi : i < count) : f.copied m count (f.dst+i) = m (f.addr f.partner i) := by
  simp [copied, hi]

/-- Writing the header copy never changes any of the seven header-control fields. -/
theorem BroadcastFrame.copied_image (f : BroadcastFrame) {w : ℕ} {pub : Arg → ℕ} {m : ℕ → ℕ}
    (fit : f.Fits w (pub 0)) (image : f.At pub m) (count : ℕ) : f.At pub (f.copied m count) := by
  have before (j : ℕ) (hj : j ≤ 25) :
      frameField pub (f.copied m count) j = frameField pub m j :=
    f.copied_before m count (pub 0+j) (by have := fit.frame; omega)
  simp only [At, before 0 (by decide), before 1 (by decide), before 2 (by decide), before 3 (by decide), before 4 (by decide), before 5 (by decide), before 25 (by decide)]
  exact image

/-- A team has a valid zero-or-one word at every reference prefix position. -/
def BroadcastFrame.ReferenceBits (f : BroadcastFrame) (m : ℕ → ℕ) : Prop :=
  ∀ i < f.header, m (f.addr f.partner i) < 2

private def CopyAt (f : BroadcastFrame) (original : ℕ → ℕ) (i : ℕ) (z : NatState) : Prop :=
  f.Stable z.reg ∧ z.reg 10 = i ∧ z.mem = f.copied original i

private theorem copyHeaderBit_run {w : ℕ} (f : BroadcastFrame) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (original : ℕ → ℕ) (bits : f.ReferenceBits original)
    (image : f.At (readings pub) original) (fit : f.Fits w (pub 0).val)
    (i : ℕ) (hi : i < f.header) (s : Bank w) (m : Memory w)
    (inv : CopyAt f original i (.ofWords s m)) :
    BoundedRun pub macros copyHeaderBit s m copyHeaderBit.slots (CopyAt f original (i+1)) := by
  obtain ⟨stable, cursor, memEq⟩ := inv
  change f.Stable (readings s) at stable
  change (s 10).val = i at cursor
  change readings m = f.copied original i at memEq
  have fm : f.At (readings pub) (readings m) := memEq ▸ f.copied_image fit image i
  have partner : (s 8).val = f.partner := stable.2.2.2.2.2.2.2.2.1
  obtain ⟨other,good⟩ := f.partner_spec fit.three
  obtain ⟨es,t,read,cost,hr⟩ := readPhysical_run f pub macros s m 8 10 12 (by decide) fm fit
    (partner ▸ good) (partner ▸ other) (cursor ▸ hi.trans_le fit.cap)
  have before : f.addr f.partner i < f.dst :=
    (f.addr_lt_input fit good other (hi.trans_le fit.cap)).trans_le
      (fit.input.trans (by have := fit.frame; omega))
  have h12 : (t 12).val = original (f.addr f.partner i) := by
    have e := congrArg Fin.val (hr 12 (by decide))
    simpa [readings,partner,cursor,← show readings m (f.addr f.partner i) =
      original (f.addr f.partner i) by rw [memEq, f.copied_before original i _ before]] using e
  have low (k : Reg) (hk : k.val < 30) (hne : k ≠ 12) : readings t k = readings s k :=
    congrArg Fin.val (by simpa [hne] using hr k hk)
  have st : f.Stable (readings t) := by
    simp only [BroadcastFrame.Stable, low 0 (by decide) (by decide), low 1 (by decide) (by decide), low 2 (by decide) (by decide), low 3 (by decide) (by decide), low 4 (by decide) (by decide), low 5 (by decide) (by decide), low 6 (by decide) (by decide), low 7 (by decide) (by decide), low 8 (by decide) (by decide), low 9 (by decide) (by decide), low 14 (by decide) (by decide)]
    exact stable
  have t10 : readings t 10 = i := (low 10 (by decide) (by decide)).trans cursor
  have t12 : readings t 12 = original (f.addr f.partner i) := h12
  have ⟨_,one,_,_,_,_,_,_,_,dest,two⟩ := st
  have inRange := bits i hi
  have hsafe : saveHeaderBit.fixedSafe w (readings pub) (.ofWords t m) := by
    simp (config := {decide:=true}) [saveHeaderBit,requireLt,Code.block,Code.fixedSafe,
      Code.fixedEval,Code.safeReadOnly,Code.evalNat,addressOpFits,addressOp,NatState.ofWords,
      one,dest,two,t10,t12,inRange]
    have := fit.out; omega
  obtain ⟨fs,u,mu,save,ct,post⟩ := saveHeaderBit.runFixed pub macros t m hsafe
  refine ⟨_,u,mu,read.seq save,(VPVNP.RAMBuckets.cost_append ..).trans_le (Nat.add_le_add cost ct),?_⟩
  rw [post]
  constructor
  · simpa (config := {decide:=true}) [saveHeaderBit, requireLt, Code.block, Code.fixedEval, Code.evalNat,
      addressOp,NatState.ofWords,BroadcastFrame.Stable,two,t12,inRange] using st
  · constructor
    · simp (config := {decide:=true}) [saveHeaderBit,requireLt,Code.block,Code.fixedEval,Code.evalNat,
        addressOp,NatState.ofWords,two,t12,inRange,t10,one]
    · simpa (config := {decide:=true}) [saveHeaderBit,requireLt,Code.block,Code.fixedEval,Code.evalNat,
        addressOp,NatState.ofWords,two,t12,inRange,t10,dest,memEq] using copied_next f original i

/-- The complete prefix copy has the exact memory image and preserves the
stable control registers at a cost linear in its declared width. -/
theorem copyHeader_run {w : ℕ} (f : BroadcastFrame) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (image : f.At (readings pub) (readings m)) (fit : f.Fits w (pub 0).val)
    (bits : f.ReferenceBits (readings m)) (stable : f.Stable (readings s)) :
    BoundedRun pub macros copyHeader s m (2+f.header*(copyHeaderBit.slots+1))
      (fun z ↦ f.Stable z.reg ∧ z.mem = f.copied (readings m) f.header) := by
  let t := Function.update s 10 (s 0)
  have reset : Runs pub macros (.copy 10 0) s m [tick w] t m := Runs.localStep m rfl rfl
  have start : CopyAt f (readings m) 0 (.ofWords t m) := by
    refine ⟨?_,?_,(copied_zero ..).symm⟩
    · simpa (config := {decide:=true}) [t,NatState.ofWords,readings,BroadcastFrame.Stable,Function.update]
        using stable
    · simpa [t,NatState.ofWords,readings] using stable.1
  obtain ⟨es,u,mu,run,cost,hpost⟩ := run_counted_loop pub macros 10 6 copyHeaderBit
    f.header copyHeaderBit.slots (CopyAt f (readings m))
    (fun _ _ h ↦ ⟨h.2.1,h.1.2.2.2.2.2.2.1⟩)
    (fun i hi s' m' inv ↦ copyHeaderBit_run f pub macros (readings m) bits image fit i hi s' m' inv)
    0 (Nat.zero_le _) t m start
  refine ⟨_,u,mu,reset.seq run,?_,hpost.1,hpost.2.2⟩
  change 1+traceCost es ≤ _
  simp only [Nat.sub_zero] at cost
  omega

end RoutingISA

end BorderVNP
end Computability
end OAI
