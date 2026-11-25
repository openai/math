import OAI.Computability.BorderVNP.DiagonalTallyPacketEmit

/-! # Native computation of each packet-relative address -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyPacketEmit

open VPVNP.BurstRAM RoutingISA

variable {w : ℕ}

private theorem read_preserves_state (c : Code) (pub : Arg → Word w) (m : Memory w)
    (s t : Bank w) (f : Frame) (i : ℕ) (state : State f i (.ofWords s m))
    (hc : c.protects 16 = true) (he : readings t = c.evalNat (readings pub) (readings m) (readings s)) :
    State f i (.ofWords t m) := by
  have hr (r : Reg) (h : r.val<16) : readings t r = readings s r := by
    rw [he,c.evalNat_protected _ _ _ hc r h]
  apply state.preserve (fun r h => hr r (by omega))
  exact (hr 15 (by decide)).trans state.cursor

private theorem select_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (orig : ℕ → ℕ) (i : ℕ) (hi : i<f.count*f.width)
    (fit : f.Fits orig w (pub 0).val) (state : State f i (.ofWords s m))
    (unchanged : ∀ a < f.descriptors, readings m a = orig a) :
    ∃ es t, Runs pub mac selectRef s m es t m ∧ traceCost es ≤ selectRef.slots ∧
      State f i (.ofWords t m) ∧ readings t 18 = orig (f.triples+3*(i/f.width)) ∧
      readings t 21 = orig (f.recipeAddr orig (i/f.width) (i%f.width)) := by
  have initial := state
  obtain ⟨_,h1,_,h3,_,h5,h6,_,_,_,_,h11,h12,_,_,h15⟩ := state
  change readings s 1 = _ at h1
  change readings s 3 = _ at h3
  change readings s 5 = _ at h5
  change readings s 6 = _ at h6
  change readings s 11 = _ at h11
  change readings s 12 = _ at h12
  change readings s 15 = _ at h15
  have hw : 0<f.width := by by_contra! h; rw [show f.width=0 by omega,Nat.mul_zero] at hi; omega
  have hrow : i/f.width<f.count := (Nat.div_lt_iff_lt_mul hw).mpr hi
  have hdigit := Nat.mod_lt i hw
  have htr := fit.triplesBefore
  have hdir := fit.outputs
  have hroom := fit.room
  have hBase := unchanged (f.triples+3*(i/f.width)) (by omega)
  have hSel := unchanged (f.triples+3*(i/f.width)+1) (by omega)
  have hVert := unchanged (f.triples+3*(i/f.width)+2) (by omega)
  have hRecipe := fit.recipesBefore (i/f.width) hrow (i%f.width) hdigit
  have hCode := unchanged _ hRecipe
  have hSlice := fit.slice (i/f.width) hrow
  unfold Frame.recipeAddr at hRecipe hCode
  have safe : selectRef.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [selectRef,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,addressOp,addressOpFits,
      h1,h3,h5,h6,h11,h12,h15,hSel,hVert,hw]
    omega
  obtain ⟨es,t,r,hc,ht⟩ := Code.runReadOnly selectRef pub mac m s safe
  refine ⟨es,t,r,hc,read_preserves_state selectRef pub m s t f i initial (by decide) ht,?_⟩
  rw [ht]
  simp [selectRef,Code.block,Code.evalNat,Function.update,addressOp,h1,h3,h5,h6,h11,h12,h15,
    hBase,hSel,hVert,hCode,Frame.recipeAddr]

private theorem resolve_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (i base code : ℕ) (state : State f i (.ofWords s m))
    (h18 : readings s 18 = base) (h21 : readings s 21 = code)
    (hfit : f.resolve base code < 2^w) :
    ∃ es t, Runs pub mac resolveRef s m es t m ∧ traceCost es ≤ resolveRef.slots ∧
      State f i (.ofWords t m) ∧ readings t 22 = f.resolve base code := by
  have h0 : readings s 0 = 0 := state.zeroEq
  have h1 : readings s 1 = 1 := state.oneEq
  have h2 : readings s 2 = 2 := state.twoEq
  have h9 : readings s 9 = f.zeroAddr := state.zeroAddr
  have h10 : readings s 10 = f.oneAddr := state.oneAddr
  have spec : resolveRef.safeReadOnly w (readings pub) (readings m) (readings s) ∧
      resolveRef.evalNat (readings pub) (readings m) (readings s) 22 = f.resolve base code := by
    by_cases hz : code=0 <;> by_cases ho : code=1 <;>
      simp_all [resolveRef,Code.safeReadOnly,Code.evalNat,Frame.resolve,Function.update,addressOpFits,addressOp]
    omega
  obtain ⟨es,t,r,hc,ht⟩ := Code.runReadOnly resolveRef pub mac m s spec.1
  exact ⟨es,t,r,hc,read_preserves_state resolveRef pub m s t f i state (by decide) ht,
    (congrFun ht 22).trans spec.2⟩

/-- Fetch and relocate the current digit's reference, and write that word into the
generated vector. The earlier prefix and each protected register survive. -/
theorem refStep_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w)
    (m : Memory w) (f : Frame) (orig previous : ℕ → ℕ) (i : ℕ) (hi : i<f.count*f.width)
    (fit : f.Fits orig w (pub 0).val) (state : State f i (.ofWords s m))
    (unchanged : ∀ a < f.descriptors, readings m a = orig a)
    (mem : readings m = written f.refs (f.refValue orig) previous i) :
    BoundedRun pub mac refStep s m refStep.slots (fun z => State f (i+1) z ∧
      z.mem = written f.refs (f.refValue orig) previous (i+1)) := by
  obtain ⟨a,t,ra,ha,ht,t18,t21⟩ := select_runs pub mac s m f orig i hi fit state unchanged
  obtain ⟨b,u,rb,hb,hu,u22⟩ := resolve_runs pub mac t m f i _ _ ht t18 t21 (fit.digit i hi)
  change readings u 22 = f.refValue orig i at u22
  let z := NatState.ofWords u m
  change State f i z at hu
  have h1 := hu.oneEq
  have h7 := hu.refs
  have h15 := hu.cursor
  change z.reg 22 = _ at u22
  have room := fit.room
  have safe : storeRef.fixedSafe w (readings pub) z := by
    simp [storeRef,Code.block,Code.fixedSafe,Code.fixedEval,Code.safeReadOnly,Code.evalNat,Function.update,
      addressOp,addressOpFits,h7,h15,h1]; omega
  obtain ⟨c,y,my,rc,hc,eq⟩ := storeRef.runFixed pub mac u m safe
  refine ⟨_,y,my,ra.seq (rb.seq rc),?_,?_⟩
  · unfold traceCost
    simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost a+(traceCost b+traceCost c) ≤ selectRef.slots+(resolveRef.slots+storeRef.slots)
    omega
  · rw [eq]
    change State f (i+1) (storeRef.fixedEval (readings pub) z) ∧
      (storeRef.fixedEval (readings pub) z).mem = _
    constructor
    · apply hu.preserve (Code.fixedEval_protected _ _ _ (show storeRef.protects 15 = true by decide))
      simp [storeRef,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,h15,h1]
    · change z.mem = written f.refs (f.refValue orig) previous i at mem
      simp [storeRef,Code.block,Code.fixedEval,Code.evalNat,Function.update,addressOp,h7,h15,u22]
      rw [mem,written_step]

end DiagonalTallyPacketEmit

end BorderVNP
end Computability
end OAI
