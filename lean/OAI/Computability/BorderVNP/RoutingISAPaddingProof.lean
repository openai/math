import OAI.Computability.BorderVNP.RoutingISAPaddingPartner
import OAI.Computability.BorderVNP.RoutingISAUnitPartner
import OAI.Computability.BorderVNP.RoutingISAPaddingTicks

/-! # Execution of the physical unit-link and padding checks

The complete physical input of each incident block is checked on the unit branch. On the
evaluation branch the loop starts after the prefix and both oriented scheduled leg loads.
Every returning execution reads zero at each required address, leaves memory unchanged, and
fits the native tick allowance. -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA

open VPVNP.BurstRAM

variable {w : ℕ}

/-- Native completeness and soundness of a read-only physical link check. -/
structure NativeLinkCheck (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (c : Code) (s : Bank w) (m : Memory w) (budget : ℕ) (condition : Prop) : Prop where
  /-- A valid physical image returns with unchanged memory within the tick bound. -/
  complete : condition → ∃ es t, Runs pub macros c s m es t m ∧ traceCost es ≤ budget
  /-- Every returning trace validates the image and preserves memory. -/
  sound : ∀ {es t mt}, Runs pub macros c s m es t mt → mt = m ∧ condition

/-- At the assembled program's actual accepting continuation, a physical check
accepts precisely the images satisfying the declared condition. -/
theorem NativeLinkCheck.execute_iff {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m budget condition} (h : NativeLinkCheck pub macros c s m budget condition)
    (fallThrough : c.withoutAccept = true) :
    (∃ bits es, TeamRAM.execute (c.program.fetch pub macros) ⟨0,s⟩ m bits = some es) ↔ condition := by
  constructor
  · rintro ⟨bits,es,he⟩
    obtain ⟨⟨t,mt,hr⟩,_⟩ := (Code.execute_iff_runs fallThrough).mp he
    exact (h.sound hr).2
  · intro hc
    obtain ⟨es,t,r,_⟩ := h.complete hc
    exact ⟨_,es,r.execute⟩

/-- All returning traces of the deterministic physical check obey the computed time bound. -/
theorem NativeLinkCheck.cost {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    {c : Code} {s m budget condition} (h : NativeLinkCheck pub macros c s m budget condition)
    (det : c.deterministic = true) {es t mt} (run : Runs pub macros c s m es t mt) :
    traceCost es ≤ budget := by
  obtain ⟨fs,u,r,hr⟩ := h.complete (h.sound run).2
  rw [(run.unique_of_deterministic det r).1]
  exact hr

private theorem checkAll {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8} {m : Memory w}
    (f : BroadcastFrame) (start : List Code) (hne : start ≠ []) (s : Bank w) (base extra : ℕ)
    (c : Code) (ok : ℕ → Prop) (det : (Code.block start).deterministic = true)
    (setup : ∃ es t, Runs pub macros (.block start) s m es t m ∧
      traceCost es ≤ (Code.block start).slots ∧ partnerInv f base t ∧ (t 11).val = 0)
    (check : PartnerCheck pub macros m f.teams f.team (extra+f.capacity*(zeroScanBody.slots+1)+1)
      c (partnerInv f base) ok) :
    NativeLinkCheck pub macros (.block (start ++ [partnerLoop c])) s m
      (f.linkCheckTicks (Code.block start).slots extra) (∀ i < f.teams, i ≠ f.team → ok i) := by
  obtain ⟨hs,t,init,hc,hinv,hzero⟩ := setup
  have split {es z mz} :
      Runs pub macros (.block (start ++ [partnerLoop c])) s m es z mz ↔
      Runs pub macros (.seq (.block start) (partnerLoop c)) s m es z mz :=
    Runs.block_append_iff hne (by simp)
  constructor
  · intro good
    obtain ⟨fs,z,rl,hl,_,_⟩ := partnerLoop_complete (partnerRegs f base) check good t hinv
      (by rw [hzero]; exact Nat.zero_le _)
    rw [hzero, Nat.sub_zero] at hl
    refine ⟨_,z,split.mpr (init.seq rl),?_⟩
    rw [show traceCost (hs ++ fs) = traceCost hs + traceCost fs from VPVNP.RAMBuckets.cost_append ..]
    unfold BroadcastFrame.linkCheckTicks
    change traceCost fs ≤ f.teams * (extra + f.capacity * (zeroScanBody.slots+1) + 5) + 1 at hl
    omega
  · intro es z mz r
    obtain ⟨v,mv,gs,fs,_,head,tail⟩ := Runs.seq_iff.mp (split.mp r)
    obtain ⟨_,ht,hm⟩ := head.unique_of_deterministic det init
    subst v
    subst mv
    obtain ⟨hm,_,_,ha⟩ := partnerLoop_sound (partnerRegs f base) check hinv hzero tail
    exact ⟨hm,ha⟩

private theorem initCounter {pub : Arg → Word w} {macros : TeamOpcode.Macros w 8}
    (f : BroadcastFrame) (m : Memory w) (base : ℕ) (s : Bank w) (h : partnerInv f base s) :
    ∃ t, Runs pub macros (.copy 11 0) s m [tick w] t m ∧ partnerInv f base t ∧ (t 11).val = 0 := by
  refine ⟨_,Runs.localStep m rfl rfl,(partnerRegs f base).counter s h (s 0),?_⟩
  simp only [Function.update_self]
  exact h.1.1

/-- On the unit branch, the exact instruction fragment checks every word in every incident
block, with a common time bound linear in the physical exterior and number of partners. -/
theorem unitLinks_check (f : BroadcastFrame) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (image : f.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) :
    NativeLinkCheck pub macros unitLinks s m (f.linkCheckTicks (headerSetup.slots+1) 1)
      (∀ i < f.teams, i ≠ f.team → f.ZeroFrom (readings m) 0 i) := by
  obtain ⟨es,t,init,hi,st⟩ := headerSetup_run f pub macros s m image fit
  let base := (t 19).val
  obtain ⟨z,rc,hv,h0⟩ := initCounter (pub := pub) (macros := macros) f m base t ⟨st,rfl⟩
  apply checkAll f [headerSetup,.copy 11 0] (by decide) s base 1 unitPartner
    (f.ZeroFrom (readings m) 0) (by decide) _ (unitPartner_check f pub macros m base image fit)
  refine ⟨_,z,init.seq rc,?_,hv,h0⟩
  rw [show traceCost (es ++ [tick w]) = traceCost es + 1 from VPVNP.RAMBuckets.cost_append ..]
  exact Nat.add_le_add_right hi 1

/-- At the evaluation branch's padding pass, register 19 contains the base of the two-way
load table, as read from field 18. All low header registers survive that read. -/
private theorem loadPaddingBase (f : BroadcastFrame) (pub : Arg → Word w)
    (macros : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (hs : f.Stable (readings s)) (fit : f.Fits w (pub 0).val) :
    ∃ es t, Runs pub macros (readFrame 19 62 63 18) s m es t m ∧
      traceCost es ≤ (readFrame 19 62 63 18).slots ∧
      partnerInv f (frameField (readings pub) (readings m) 18) t := by
  have haddr : readings pub 0+18 < 2^w := by
    change (pub 0).val+18 < _
    have := fit.frame
    have := fit.out
    omega
  have safe : (readFrame 19 62 63 18).safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [readFrame,Code.block,Code.safeReadOnly,Code.evalNat,addressOpFits]
    omega
  obtain ⟨es,t,r,hc,he⟩ := Code.runReadOnly _ pub macros m s safe
  rw [readFrameFixed] at he
  refine ⟨es,t,r,hc,?_,?_⟩
  · rcases hs with ⟨h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h14⟩
    simp (config := {decide := true}) [BroadcastFrame.Stable,he,h0,h1,h2,h3,h4,h5,h6,h7,h8,h9,h14]
  · change readings t 19 = _
    simp [he]

/-- The physical padding checker accepts exactly the zero suffixes after the common
header and the two actual table loads at every incident partner. -/
theorem checkPadding_check (f : BroadcastFrame) (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (image : f.At (readings pub) (readings m))
    (fit : f.Fits w (pub 0).val) (base : ℕ) (field : frameField (readings pub) (readings m) 18 = base)
    (room : ∀ i < f.teams, i ≠ f.team →
      pairIndex base f.teams f.team i < 2^w ∧ pairIndex base f.teams i f.team < 2^w)
    (widths : ∀ i < f.teams, i ≠ f.team → f.paddingFrom (readings m) base i ≤ f.capacity) :
    NativeLinkCheck pub macros checkPadding s m
      (f.linkCheckTicks (headerSetup.slots+(readFrame 19 62 63 18).slots+1) paddingStartBlock.slots)
      (∀ i < f.teams, i ≠ f.team → f.ZeroFrom (readings m) (f.paddingFrom (readings m) base i) i) := by
  obtain ⟨es,t,init,hi,st⟩ := headerSetup_run f pub macros s m image fit
  obtain ⟨fs,v,read,hr,hv⟩ := loadPaddingBase f pub macros t m st fit
  rw [field] at hv
  obtain ⟨z,rc,hz,h0⟩ := initCounter (pub := pub) (macros := macros) f m base v hv
  have h := checkAll f [headerSetup, readFrame 19 62 63 18, .copy 11 0] (by decide) s base
    paddingStartBlock.slots paddingPartner
    (fun i => f.ZeroFrom (readings m) (f.paddingFrom (readings m) base i) i) (by decide) ?_
    (paddingPartner_check f base pub macros m image fit room widths)
  · exact h
  · refine ⟨_,z,init.seq (read.seq rc),?_,hz,h0⟩
    simp only [traceCost,VPVNP.RAMBuckets.cost_append]
    change traceCost es + (traceCost fs + 1) ≤ headerSetup.slots + ((readFrame 19 62 63 18).slots+1)
    omega

end RoutingISA

end BorderVNP
end Computability
end OAI
