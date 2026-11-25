import OAI.Computability.BorderVNP.DiagonalTallyPacketEmitRef

/-! # Returning native execution for all owned packet argument references -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyPacketEmit

open VPVNP.BurstRAM RoutingISA

variable {w : ℕ}

/-- Memory after the complete descriptor and reference arrays have been written. -/
def Frame.image (f : Frame) (orig : ℕ → ℕ) : ℕ → ℕ :=
  written f.refs (f.refValue orig) (written f.descriptors f.descValue orig (2*f.count)) (f.count*f.width)

/-- Physical addresses preceding both output arrays retain their original values. -/
theorem Frame.image_before (f : Frame) (m : ℕ → ℕ) (hd : f.descriptors ≤ f.refs) (a : ℕ)
    (h : a < f.descriptors) : f.image m a = m a := by
  rw [Frame.image,written_before _ _ _ (h.trans_le hd),written_before _ _ _ h]

/-- An entire generated digit-address vector is in the bank starting at slot 80. -/
theorem Frame.image_ref (f : Frame) (m : ℕ → ℕ) (i : ℕ) (hi : i < f.count*f.width) :
    f.image m (f.refs+i) = f.refValue m i := written_at _ _ _ hi

/-- The end pointers and start pointers for all vertices are in the descriptor bank. -/
theorem Frame.image_descriptor (f : Frame) (m : ℕ → ℕ) (h : f.descriptors+2*f.count ≤ f.refs)
    (i : ℕ) (hi : i<2*f.count) : f.image m (f.descriptors+i) = f.descValue i := by
  rw [Frame.image,written_before _ _ _ (by omega),written_at _ _ _ hi]

set_option maxRecDepth 4000 in
private theorem setup_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (f : Frame) (hr : f.resident (readings pub) (readings m))
    (fit : f.Fits (readings m) w (pub 0).val) :
    ∃ es t, Runs pub mac setup s m es t m ∧ traceCost es ≤ setup.slots ∧ State f 0 (.ofWords t m) := by
  obtain ⟨count,triples,recipes,refs,desc,zeroAddr,oneAddr,width,vertices⟩ := hr
  have dir : readings pub 0+84 < 2^w := by
    change (pub 0).val+84 < _
    have := fit.frameBefore; have := fit.outputs; have := fit.room; omega
  have space := fit.room
  have hd := fit.outputs
  have hw : w ≠ 0 := by rintro rfl; simp at dir
  have safe : setup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp (config := {decide := true}) [setup,readFrame,Code.block,Code.safeReadOnly,Code.evalNat,
      Function.update,addressOpFits,addressOp,count,width,hw]; omega
  obtain ⟨es,t,r,hc,ht⟩ := setup.runReadOnly pub mac m s safe
  refine ⟨es,t,r,hc,?_⟩
  constructor
  all_goals
    change readings t _ = _
    rw [ht]
    simp (config := {decide := true}) [setup,readFrame,Code.block,Code.evalNat,Function.update,addressOp,
      count,triples,recipes,refs,desc,zeroAddr,oneAddr,width,vertices,two_mul]

/-- The actual finite native table resolves every owned triple and static recipe.
No dynamic bit-address vector is assumed on entry. -/
theorem emitReferences_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (f : Frame) (hr : f.resident (readings pub) (readings m))
    (fit : f.Fits (readings m) w (pub 0).val) :
    ∃ es t m', Runs pub mac emitReferences s m es t m' ∧
      traceCost es ≤ setup.slots+(2*f.count)*(descStep.slots+1)+1+1+
        (f.count*f.width)*(refStep.slots+1)+1 ∧
      readings m' = f.image (readings m) ∧
      (∀ e ∈ es, e.choices = [] ∧ e.sign = .plus ∧ e.action.extra = 0) := by
  let orig := readings m
  obtain ⟨a,t,ra,ha,ht⟩ := setup_runs pub mac s m f hr fit
  let I (i : ℕ) (z : NatState) := State f i z ∧ z.mem = written f.descriptors f.descValue orig i
  have hI : I 0 (.ofWords t m) := ⟨ht,by funext k; simp [written,orig,NatState.ofWords]⟩
  obtain ⟨b,u,mu,rb,hb,hu⟩ := run_counted_loop pub mac 15 13 descStep (2*f.count) descStep.slots I
    (fun _ _ h => ⟨h.1.cursor,h.1.numDesc⟩)
    (fun i hi su mu h => descStep_runs f pub mac su mu orig i hi fit h.1 h.2) 0 (by omega) t m hI
  let previous := written f.descriptors f.descValue orig (2*f.count)
  have mPrev : readings mu = previous := hu.2
  have hc : (Code.copy 15 0).safeReadOnly w (readings pub) (readings mu) (readings u) := trivial
  obtain ⟨c,y,rc,hc',cy⟩ := (Code.copy 15 0).runReadOnly pub mac mu u hc
  have hReset : State f 0 (.ofWords y mu) := by
    apply hu.1.preserve
    · intro j hj
      change readings y j = readings u j
      rw [cy]
      exact (Code.copy 15 0).evalNat_protected _ _ _ (by decide) j hj
    · change readings y 15 = 0
      rw [cy]; simp only [Code.evalNat,Function.update_self]; exact hu.1.zeroEq
  let J (i : ℕ) (z : NatState) := State f i z ∧ z.mem = written f.refs (f.refValue orig) previous i
  have hJ : J 0 (.ofWords y mu) := ⟨hReset,by funext k; simp [written,NatState.ofWords,mPrev]⟩
  have step (i : ℕ) (hi : i<f.count*f.width) (sy : Bank w) (my : Memory w)
      (h : J i (.ofWords sy my)) :
      BoundedRun pub mac refStep sy my refStep.slots (J (i+1)) := by
    apply refStep_runs pub mac sy my f orig previous i hi fit h.1 _ h.2
    intro k hk
    change (NatState.ofWords sy my).mem k = orig k
    rw [h.2,written_before _ _ _ (by have := fit.outputs; omega)]
    exact written_before _ _ _ hk
  obtain ⟨d,z,mz,rd,hd,hz⟩ := run_counted_loop pub mac 15 14 refStep (f.count*f.width) refStep.slots J
    (fun _ _ h => ⟨h.1.cursor,h.1.numRefs⟩) step 0 (by omega) y mu hJ
  have run : Runs pub mac emitReferences s m (a++(b++(c++d))) z mz := ra.seq (rb.seq (rc.seq rd))
  refine ⟨_,z,mz,run,?_,hz.2,DiagonalTallyRAM.ordinary_run (by decide) run⟩
  unfold traceCost
  simp only [VPVNP.RAMBuckets.cost_append]
  change traceCost a+(traceCost b+(traceCost c+traceCost d)) ≤ _
  simp only [Nat.sub_zero] at hb hd
  change traceCost c ≤ 1 at hc'
  omega

end DiagonalTallyPacketEmit

end BorderVNP
end Computability
end OAI
