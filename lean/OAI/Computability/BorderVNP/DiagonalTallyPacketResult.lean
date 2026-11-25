import OAI.Computability.BorderVNP.DiagonalTallyPacketEvidence

/-! # Producing the actual cube gadget IDs from the physical packet assignments -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyPacketEmit

open VPVNP.BurstRAM RoutingISA Cube Cube.Tally DiagonalTallyPacket

variable {w n b h K s D : ℕ}

/-- The two linked finite programs first generate local physical references and then
read each vertex's selected gadget ID. -/
def producePacketIDs : Code := .seq emitReferences packetLookup

private theorem supplied_ofFn {N : ℕ} (m : Memory w) (table limit p : ℕ) (r : Fin N → Request)
    (hf : ∀ i, p+2*i.val+2 ≤ limit ∧ (r i).start+(r i).digits.length ≤ limit ∧
      (∀ d ∈ (r i).digits, d.1<limit) ∧ table+(r i).index<limit ∧ (r i).resident m (p+2*i.val)) :
    supplied m table limit p (List.ofFn r) := by
  induction N generalizing p with
  | zero => simp [supplied]
  | succ N ih =>
    rw [List.ofFn_succ]
    have h0 := hf 0
    simp only [Fin.val_zero,Nat.mul_zero,Nat.add_zero] at h0
    refine ⟨h0.1,h0.2.1,h0.2.2.1,h0.2.2.2.1,h0.2.2.2.2,ih (p+2) (fun i => r i.succ) ?_⟩
    intro i
    have hh := hf i.succ
    simpa only [Fin.val_succ,Nat.mul_succ,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using hh

private theorem selectedWords_after (m : Memory w) (dst a : ℕ) (xs : List (Word w))
    (ha : dst+xs.length ≤ a) : selectedWords m dst xs a=m a := by
  induction xs generalizing m dst with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons] at ha
    rw [selectedWords,ih _ _ (by omega),Function.update_of_ne (by omega)]

private theorem written_after (base : ℕ) (val orig : ℕ → ℕ) (len a : ℕ) (h : base+len ≤ a) :
    written base val orig len a=orig a := by
  rw [written,ite_eq_right (by omega)]

/-- End-to-end register-level execution with the full writable address interval bounded on the current team's triples. Each output ID
is the lookup on the actual selector, vertex, attached ends and incident supply words.
The constant finite tables are common to all packets. -/
theorem producePacketIDs_runs_separated (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w)
    (m : Memory w) (f : Frame) (visits : Fin f.count → Visit n b h K s)
    (id : TableEntry n b h K s → ℕ) (table dst D : ℕ)
    (hr : f.resident (readings pub) (readings m)) (fit : f.Fits (readings m) w (pub 0).val)
    (hRecipe : f.recipeAt (readings m) n b h K s)
    (hTriples : ∀ i, (visits i).tripleAt (readings m) (f.triples+3*i.val))
    (hBanks : ∀ i, VertexAt m (visits i).base (visits i).selector (visits i).vertex (visits i).ends (visits i).supply)
    (hz : (m f.zeroAddr).val=0) (ho : (m f.oneAddr).val=1)
    (below : ∀ i, ∀ r ∈ recipe (visits i).selector (visits i).vertex b s,
      r.address (visits i).base f.zeroAddr f.oneAddr<f.descriptors)
    (h47 : (m ((pub 0).val+47)).val=table) (h71 : (m ((pub 0).val+71)).val=dst)
    (hTable : ∀ k < 2^argumentWidth n b h K s,
      (m (table+k)).val=idTable (selectorOrder n K h) (vertexOrder _) id k)
    (tableFit : table+2^argumentWidth n b h K s ≤ f.descriptors)
    (separate : f.refs+f.count*f.width ≤ dst) (room : dst+f.count < 2^w) :
    ∃ es t m', Runs pub mac producePacketIDs bank m es t m' ∧
      traceCost es ≤ DiagonalTallyPacketEmit.setup.slots + DiagonalTallyPacket.setup.slots + 4 +
        f.count*(2*(descStep.slots+1)+11) + (f.count*f.width)*(refStep.slots+1+8) ∧
      (∀ i : Fin f.count, (m' (dst+i.val)).val = id ((visits i).entry D)) ∧
      (∀ a, a<f.descriptors ∨ dst+f.count ≤ a → m' a = m a) ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0) := by
  obtain ⟨a,t,mt,ra,ha,image,_⟩ := emitReferences_runs pub mac bank m f hr fit
  let rq (i : Fin f.count) := (visits i).request f (readings m) i.val
  let rs := List.ofFn rq
  have hlen : rs.length=f.count := List.length_ofFn
  have widths (i : Fin f.count) : (rq i).digits.length=f.width := by
    simp [rq,Visit.request,recipe_length,← hRecipe.1]
  have total : (rs.map fun r => r.digits.length).sum=f.count*f.width := by
    simp [rs,List.map_ofFn,Function.comp_def,widths,List.ofFn_const]
  have hd := fit.outputs
  have hFrame := fit.frameBefore
  have hpre (i : ℕ) (hi : i<f.descriptors) : mt i=m i := by
    apply Fin.ext
    change readings mt i = readings m i
    rw [image,f.image_before _ (by omega) _ hi]
  obtain ⟨hcount,_,_,_,hdesc,_,_,_,_⟩ := hr
  have frame : DiagonalTallyPacket.frameAt pub mt f.descriptors dst table rs.length := by
    rw [hlen]
    refine ⟨?_,?_,?_,?_⟩
    all_goals rwa [hpre _ (by omega)]
  have allRows := supplied_ofFn mt table dst f.descriptors rq (by
    intro i
    have hblock := Nat.mul_le_mul_right f.width i.isLt
    rw [Nat.succ_mul] at hblock
    have hidx := (visits i).request_index f m i.val (hBanks i) hz ho D
    have bound := lookupIndex_lt ((visits i).entry D)
    refine ⟨by have := i.isLt; omega,?_,?_,?_,?_⟩
    · rw [widths]; change f.refs+i.val*f.width+f.width ≤ dst; omega
    · intro d hm
      obtain ⟨r,hr,rfl⟩ := List.mem_map.mp hm
      exact (below i r hr).trans_le (by omega)
    · change table+((visits i).request f (readings m) i.val).index < dst
      rw [hidx]; omega
    · exact (visits i).resident_after_emit f m mt i.val i.isLt hRecipe (hTriples i) (hBanks i)
        hz ho (below i) hd image)
  obtain ⟨btrace,z,rb,hb,_⟩ := packetLookup_runs pub mac t mt rs f.descriptors dst table dst frame allRows
    le_rfl (by omega) (by rw [hlen]; omega) (by rwa [hlen])
  have run := ra.seq rb
  refine ⟨_,_,_,run,?_,?_,?_,DiagonalTallyRAM.ordinary_run (show DiagonalTallyRAM.ordinary producePacketIDs = true by decide) run⟩
  · rw [show traceCost (a++btrace) = traceCost a+traceCost btrace from VPVNP.RAMBuckets.cost_append ..]
    rw [hlen,total] at hb
    nlinarith only [ha,hb]
  · intro i
    have hi : i.val < (rs.map fun r => mt (table+r.index)).length := by simp [hlen]
    rw [selectedWords_at _ _ _ _ hi,List.getElem_map]
    have he : rs[i.val] = rq i := List.getElem_ofFn ..
    rw [he]
    have hidx := (visits i).request_index f m i.val (hBanks i) hz ho D
    change (mt (table+((visits i).request f (readings m) i.val).index)).val=_
    rw [hidx,hpre _ (by have := lookupIndex_lt ((visits i).entry D); omega),
      hTable _ (lookupIndex_lt ((visits i).entry D)),← lookupDigits_index,idTable_lookup]
  · intro p hp
    rcases hp with before | after
    · rw [selectedWords_before _ _ _ _ (by omega),hpre p before]
    · rw [selectedWords_after _ _ _ _ (by simpa [hlen] using after)]
      apply Fin.ext
      change readings mt p=readings m p
      rw [image,Frame.image,written_after _ _ _ _ _ (by omega),written_after _ _ _ _ _ (by omega)]


/-- End-to-end register-level execution on the current team's triples. Each output ID
is the lookup on the actual selector, vertex, attached ends and incident supply words.
The constant finite tables are common to all packets. -/
theorem producePacketIDs_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (bank : Bank w)
    (m : Memory w) (f : Frame) (visits : Fin f.count → Visit n b h K s)
    (id : TableEntry n b h K s → ℕ) (table dst D : ℕ)
    (hr : f.resident (readings pub) (readings m)) (fit : f.Fits (readings m) w (pub 0).val)
    (hRecipe : f.recipeAt (readings m) n b h K s)
    (hTriples : ∀ i, (visits i).tripleAt (readings m) (f.triples+3*i.val))
    (hBanks : ∀ i, VertexAt m (visits i).base (visits i).selector (visits i).vertex (visits i).ends (visits i).supply)
    (hz : (m f.zeroAddr).val=0) (ho : (m f.oneAddr).val=1)
    (below : ∀ i, ∀ r ∈ recipe (visits i).selector (visits i).vertex b s,
      r.address (visits i).base f.zeroAddr f.oneAddr<f.descriptors)
    (h47 : (m ((pub 0).val+47)).val=table) (h71 : (m ((pub 0).val+71)).val=dst)
    (hTable : ∀ k < 2^argumentWidth n b h K s,
      (m (table+k)).val=idTable (selectorOrder n K h) (vertexOrder _) id k)
    (tableFit : table+2^argumentWidth n b h K s ≤ f.descriptors)
    (separate : f.refs+f.count*f.width ≤ dst) (room : dst+f.count < 2^w) :
    ∃ es t m', Runs pub mac producePacketIDs bank m es t m' ∧
      traceCost es ≤ DiagonalTallyPacketEmit.setup.slots + DiagonalTallyPacket.setup.slots + 4 +
        f.count*(2*(descStep.slots+1)+11) + (f.count*f.width)*(refStep.slots+1+8) ∧
      (∀ i : Fin f.count, (m' (dst+i.val)).val = id ((visits i).entry D)) ∧
      (∀ a < f.descriptors, m' a = m a) ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0) := by
  obtain ⟨es,t,m',run,cost,vals,keep,trace⟩ := producePacketIDs_runs_separated pub mac bank m f visits
    id table dst D hr fit hRecipe hTriples hBanks hz ho below h47 h71 hTable tableFit separate room
  exact ⟨es,t,m',run,cost,vals,fun a ha => keep a (.inl ha),trace⟩

end DiagonalTallyPacketEmit

end BorderVNP
end Computability
end OAI
