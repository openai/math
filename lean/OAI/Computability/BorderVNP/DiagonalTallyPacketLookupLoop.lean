import OAI.Computability.BorderVNP.DiagonalTallyPacketRecipe

/-! # Exact native execution over the selected packet vertices -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyPacket

open VPVNP.BurstRAM RoutingISA DiagonalResidueRAM
open private refs_congr from OAI.Computability.BorderVNP.DiagonalTallyMaterializeLoop

variable {w : ℕ}

/-- Bounds for the packet descriptor, every referenced bit, and the selected ID table word. -/
def supplied (m : Memory w) (table limit : ℕ) : ℕ → List Request → Prop
  | _, [] => True
  | p, r::rs => p+2 ≤ limit ∧ r.start+r.digits.length ≤ limit ∧
    (∀ d ∈ r.digits, d.1 < limit) ∧ table+r.index < limit ∧ r.resident m p ∧
    supplied m table limit (p+2) rs

private theorem supplied_congr (m m' : Memory w) (table limit p : ℕ) (rs : List Request)
    (he : ∀ i < limit, m' i = m i) (h : supplied m table limit p rs) : supplied m' table limit p rs := by
  induction rs generalizing p with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨hp,hd,href,ht,⟨a,b,c⟩,tail⟩ := h
    exact ⟨hp,hd,href,ht,⟨(congrArg Fin.val (he p (by omega))).trans a,
      (congrArg Fin.val (he _ (by omega))).trans b,refs_congr m m' _ _ _ he c hd href⟩,
      ih _ tail⟩

/-- Successive selected ID words in the actual output array. -/
def selectedWords (m : Memory w) : ℕ → List (Word w) → Memory w
  | _, [] => m
  | d, x::xs => selectedWords (Function.update m d x) (d+1) xs

theorem selectedWords_before (m : Memory w) (d a : ℕ) (xs : List (Word w)) (ha : a<d) :
    selectedWords m d xs a = m a := by
  induction xs generalizing m d with
  | nil => rfl
  | cons x xs ih =>
    rw [selectedWords,ih _ _ (by omega),Function.update_of_ne ha.ne]

/-- Exact one-word output per owned vertex. -/
theorem selectedWords_at (m : Memory w) (d : ℕ) (xs : List (Word w))
    (i : ℕ) (hi : i<xs.length) : selectedWords m d xs (d+i) = xs[i] := by
  induction xs generalizing m d i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero => simp [selectedWords,selectedWords_before _ (d+1) d _ (by omega)]
    | succ i =>
      rw [selectedWords,show d+(i+1) = (d+1)+i by omega,ih _ _ _ (by simpa using hi)]
      rfl

private theorem loop_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (rs : List Request) (p stop dst table limit : ℕ) (hs : ready s p stop dst table)
    (hr : supplied m table limit p rs) (hsep : limit ≤ dst) (hend : p+2*rs.length = stop)
    (hroom : dst+rs.length < 2^w) :
    ∃ es t, Runs pub mac loop s m es t (selectedWords m dst (rs.map fun r => m (table+r.index))) ∧
      traceCost es ≤ 11*rs.length+8*(rs.map fun r => r.digits.length).sum+1 ∧
      ready t stop stop (dst+rs.length) table := by
  induction rs generalizing s m p dst with
  | nil =>
    simp only [List.length_nil,Nat.mul_zero,Nat.add_zero] at hend
    refine ⟨_,s,.whileDone (by change ¬(s 40).val < (s 41).val; rw [hs.1,hs.2.1,hend]; omega),?_,?_⟩
    · simp [traceCost,VPVNP.RAMBuckets.cost,tick,TeamTranscript.Action.extra]
    · simpa [hend] using hs
  | cons r rs ih =>
    obtain ⟨_,_,_,hTable,resident,tail⟩ := hr
    have hstop : stop < 2^w := hs.2.1 ▸ (s 41).isLt
    simp only [List.length_cons,Nat.mul_succ] at hend hroom
    obtain ⟨a,t,ra,ha,ht⟩ := body_runs pub mac s m r p stop dst table hs resident (by omega)
      (by omega) (by omega)
    let mt := Function.update m dst (m (table+r.index))
    have preserve (i : ℕ) (hi : i<limit) : mt i = m i := Function.update_of_ne (by omega) ..
    have hr' := supplied_congr m mt table limit (p+2) rs preserve tail
    obtain ⟨b,z,rb,hb,hz⟩ := ih t mt (p+2) (dst+1) ht hr' (by omega) (by omega) (by omega)
    have stable : (rs.map fun q => mt (table+q.index)) = rs.map fun q => m (table+q.index) := by
      apply List.map_congr_left
      intro q hq
      have loc (rs : List Request) (ptr : ℕ) (hr : supplied m table limit ptr rs)
          (hq : q ∈ rs) : table+q.index < limit := by
        induction rs generalizing ptr with
        | nil => simp at hq
        | cons z zs ih =>
          rcases List.mem_cons.mp hq with rfl | hm
          · exact hr.2.2.2.1
          · exact ih _ hr.2.2.2.2.2 hm
      exact preserve _ (loc rs (p+2) tail hq)
    rw [stable] at rb
    refine ⟨_,z,.whileStep (by change (s 40).val < (s 41).val; rw [hs.1,hs.2.1]; omega) ra rb,?_,?_⟩
    · change 1+traceCost (a++b) ≤ _
      rw [show traceCost (a++b) = traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]
      simp only [List.length_cons,List.map_cons,List.sum_cons,Nat.mul_succ,Nat.mul_add]
      omega
    · simpa only [List.length_cons,Nat.add_assoc,Nat.add_left_comm,Nat.add_comm] using hz

/-- The four directory words accessed by the fixed packet table routine. -/
def frameAt (pub : Arg → Word w) (m : Memory w) (p dst table n : ℕ) : Prop :=
  (m ((pub 0).val+45)).val = p ∧ (m ((pub 0).val+46)).val = n ∧
    (m ((pub 0).val+47)).val = table ∧ (m ((pub 0).val+71)).val = dst

/-- Run the compiled table on the actual list of owned packet vertices, producing
exactly the IDs retrieved from the finite table. The loop's digits come only from the
referenced selector, vertex, shared demand and supply banks and the two literal words. -/
theorem packetLookup_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (rs : List Request) (p dst table limit : ℕ)
    (hf : frameAt pub m p dst table rs.length) (hs : supplied m table limit p rs)
    (hsep : limit ≤ dst) (hdir : (pub 0).val+71 < 2^w)
    (hptr : p+2*rs.length < 2^w) (hout : dst+rs.length < 2^w) :
    ∃ es t, Runs pub mac packetLookup s m es t (selectedWords m dst (rs.map fun r => m (table+r.index))) ∧
      traceCost es ≤ setup.slots+11*rs.length+8*(rs.map fun r => r.digits.length).sum+1 ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0) := by
  obtain ⟨hp,hn,hTab,hd⟩ := hf
  have hw : w ≠ 0 := by rintro rfl; simp at hdir
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [setup,readFrame,Code.block,Code.evalNat,Code.safeReadOnly,readings,Function.update,addressOp,
      addressOpFits,hp,hn,hw]; omega
  obtain ⟨a,t,ra,ha,ht⟩ := Code.runReadOnly setup pub mac m s safe
  have loaded : ready t p (p+2*rs.length) dst table := by
    change readings t 40 = _ ∧ readings t 41 = _ ∧ readings t 42 = _ ∧ readings t 43 = _ ∧ readings t 63 = _
    rw [ht]
    simp [setup,readFrame,Code.block,Code.evalNat,readings,Function.update,addressOp,hp,hd,hTab,hn,two_mul]
  obtain ⟨b,z,rb,hb,_⟩ := loop_runs pub mac t m rs p _ dst table limit loaded hs hsep rfl hout
  have run := ra.seq rb
  refine ⟨_,_,run,?_,DiagonalTallyRAM.ordinary_run (show DiagonalTallyRAM.ordinary packetLookup = true by decide) run⟩
  rw [show traceCost (a++b) = traceCost a+traceCost b from VPVNP.RAMBuckets.cost_append ..]; omega

end DiagonalTallyPacket

end BorderVNP
end Computability
end OAI
