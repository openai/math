import OAI.Computability.BorderVNP.DiagonalTallyMaterialize

/-! # Execution of the complete native sparse record producer -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyMaterialize

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM

variable {w : ℕ}

/-- All physical source words referred to by this operand lie before a fresh output bank. -/
def Operand.before (o : Operand) (limit : ℕ) : Prop :=
  o.offsetAddr < limit ∧ o.placeAddr < limit ∧ o.digitsAddr+o.digits.length ≤ limit ∧
    ∀ r ∈ o.digits, r.1 < limit

/-- A consecutive input descriptor region and its separate indirect sources. -/
def supplied (m : Memory w) (limit : ℕ) : ℕ → List Operand → Prop
  | _, [] => True
  | p, o::os => p+5 ≤ limit ∧ o.before limit ∧ o.resident m p ∧ o.fits w ∧ supplied m limit (p+5) os

private theorem refs_congr (m m' : Memory w) (limit p : ℕ) (xs : List (ℕ × Bool))
    (he : ∀ a < limit, m' a = m a) (hr : digitRefsAt m p xs) (hp : p+xs.length ≤ limit)
    (hv : ∀ r ∈ xs, r.1 < limit) : digitRefsAt m' p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨a,b⟩ := r
    simp only [List.length_cons] at hp
    refine ⟨(congrArg Fin.val (he _ (by omega))).trans hr.1,
      (congrArg Fin.val (he _ (hv _ List.mem_cons_self))).trans hr.2.1,
      ih _ hr.2.2 (by omega) (fun x hx => hv x (.tail _ hx))⟩

private theorem supplied_congr (m m' : Memory w) (limit p : ℕ) (xs : List Operand)
    (he : ∀ a < limit, m' a = m a) (h : supplied m limit p xs) : supplied m' limit p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons o os ih =>
    obtain ⟨hp,ho,hr,hf,ht⟩ := h
    refine ⟨hp,ho,?_,hf,ih _ ht⟩
    obtain ⟨a,b,c,d,e,f,g,r⟩ := hr
    obtain ⟨hOff,hPlace,hDigits,hRefs⟩ := ho
    refine ⟨?_,?_,?_,?_,?_,?_,?_,refs_congr m m' limit _ _ he r hDigits hRefs⟩
    all_goals rwa [he _ (by omega)]

/-- Successive writes in the exact two-word layout read by the scatter routine. -/
def storeAll (m : Memory w) : ℕ → List Operand → Memory w
  | _, [] => m
  | dst, o::os => storeAll (storePair m dst o.pair) (dst+2) os

/-- Source addresses and earlier output records survive every remaining write. -/
theorem storeAll_before (m : Memory w) (dst i : ℕ) (os : List Operand) (hi : i < dst) :
    storeAll m dst os i = m i := by
  induction os generalizing m dst with
  | nil => rfl
  | cons o os ih =>
    rw [storeAll,ih _ _ (by omega)]
    simp [storePair,Function.update_of_ne (by omega : i ≠ dst+1),Function.update_of_ne hi.ne]

/-- The emitted dynamic words can be passed directly to the previously verified
native scatter routine. -/
theorem storeAll_recordsAt (m : Memory w) (dst : ℕ) (os : List Operand)
    (hf : ∀ o ∈ os, o.fits w) :
    DiagonalTallyScatter.RecordsAt (storeAll m dst os) dst (os.map Operand.pair) := by
  induction os generalizing m dst with
  | nil => trivial
  | cons o os ih =>
    have h := hf o List.mem_cons_self
    refine ⟨?_,?_,ih _ _ (fun x hx => hf x (.tail _ hx))⟩
    · rw [storeAll,storeAll_before _ _ _ _ (by omega)]
      simp [storePair,word_val _ _ h.1]
    · rw [storeAll,storeAll_before _ _ _ _ (by omega)]
      simp [storePair,word_val _ _ h.2.2]

/-- An actual run of the materializer loop, using one shared instruction table for all
rows. Its work is linear in the number of rows and the number of reached bit addresses. -/
theorem loop_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (os : List Operand) (p stop dst limit : ℕ) (hs : ready s p stop dst)
    (hr : supplied m limit p os) (hsep : limit ≤ dst) (hend : p+5*os.length = stop)
    (hroom : dst+2*os.length < 2^w) :
    ∃ es t, Runs pub mac loop s m es t (storeAll m dst os) ∧
      traceCost es ≤ 21*os.length+8*(os.map fun o => o.digits.length).sum+1 ∧
      ready t stop stop (dst+2*os.length) := by
  induction os generalizing s m p dst with
  | nil =>
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at hend
    refine ⟨_,s,.whileDone (by change ¬(s 40).val < (s 41).val; rw [hs.1,hs.2.1,hend]; omega),?_,?_⟩
    · simp [traceCost,VPVNP.RAMBuckets.cost,tick,TeamTranscript.Action.extra]
    · simpa [hend] using hs
  | cons o os ih =>
    obtain ⟨_,_,resident,fits,tail⟩ := hr
    have hstop : stop < 2^w := hs.2.1 ▸ (s 41).isLt
    simp only [List.length_cons,Nat.mul_succ] at hend hroom
    obtain ⟨a,t,ra,ha,ht⟩ := body_runs pub mac s m o p stop dst hs resident fits (by omega) (by omega)
    have keep (i : ℕ) (hi : i < limit) : storePair m dst o.pair i = m i := by
      simp [storePair,Function.update_of_ne (by omega : i ≠ dst+1),Function.update_of_ne (by omega : i ≠ dst)]
    have updated := supplied_congr m _ limit (p+5) os keep tail
    obtain ⟨b,z,rb,hb,hz⟩ := ih t (storePair m dst o.pair) (p+5) (dst+2) ht updated
      (by omega) (by omega) (by omega)
    refine ⟨_,z,.whileStep (by change (s 40).val < (s 41).val; rw [hs.1,hs.2.1]; omega) ra rb,?_,?_⟩
    · change 1+traceCost (a++b) ≤ _
      rw [show traceCost (a++b) = traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]
      simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.mul_succ,Nat.mul_add]
      omega
    · simpa only [List.length_cons,Nat.mul_succ,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hz

private theorem supplied_fits (m : Memory w) (limit p : ℕ) (os : List Operand)
    (hs : supplied m limit p os) (o : Operand) (ho : o ∈ os) : o.fits w := by
  induction os generalizing p with
  | nil => simp at ho
  | cons x xs ih =>
    rcases List.mem_cons.mp ho with rfl | h
    · exact hs.2.2.2.1
    · exact ih _ hs.2.2.2.2 h

/-- The directory points to this team's *delivered* metadata and the destination bank. -/
def frameAt (pub : Arg → Word w) (m : Memory w) (p dst n : ℕ) : Prop :=
  (m ((pub 0).val+44)).val = p ∧ (m ((pub 0).val+34)).val = dst ∧ (m ((pub 0).val+35)).val = n

/-- Execute the actual directory loader, the whole descriptor loop and all output writes. -/
theorem materialize_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (os : List Operand) (p dst limit : ℕ) (hf : frameAt pub m p dst os.length)
    (hs : supplied m limit p os) (hsep : limit ≤ dst) (hdir : (pub 0).val+44 < 2^w)
    (hin : p+5*os.length < 2^w) (hout : dst+2*os.length < 2^w) :
    ∃ es t, Runs pub mac materialize s m es t (storeAll m dst os) ∧
      traceCost es ≤ setup.slots+21*os.length+8*(os.map fun o => o.digits.length).sum+1 ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0) ∧
      DiagonalTallyScatter.RecordsAt (storeAll m dst os) dst (os.map Operand.pair) := by
  obtain ⟨hp,hd,hn⟩ := hf
  have hw : w ≠ 0 := by intro hh; subst w; simp at hdir
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [setup,readFrame,Code.block,Code.evalNat,Code.safeReadOnly,readings,Function.update,addressOp,
      addressOpFits,hp,hn,Nat.mul_comm os.length 5,hw]; omega
  obtain ⟨a,t,ra,ha,ht⟩ := Code.runReadOnly setup pub mac m s safe
  have loaded : ready t p (p+5*os.length) dst := by
    change readings t 40 = _ ∧ readings t 41 = _ ∧ readings t 42 = _ ∧ readings t 63 = _
    rw [ht]
    simp [setup,readFrame,Code.block,Code.evalNat,readings,Function.update,addressOp,hp,hd,hn,Nat.mul_comm]
  obtain ⟨b,z,rb,hb,_⟩ := loop_runs pub mac t m os p _ dst limit loaded hs hsep rfl hout
  have run := ra.seq rb
  refine ⟨_,z,run,?_,DiagonalTallyRAM.ordinary_run (show DiagonalTallyRAM.ordinary materialize = true by decide) run,
    storeAll_recordsAt m dst os (supplied_fits m limit p os hs)⟩
  rw [show traceCost (a++b) = traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]
  omega

end DiagonalTallyMaterialize

end BorderVNP
end Computability
end OAI
