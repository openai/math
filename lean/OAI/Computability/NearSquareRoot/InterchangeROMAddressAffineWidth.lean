import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineProgram
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineWidthRestore

/-! # The standalone signed affine width command on native packed records -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMAddress.Affine

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Carry IntegerMultiplication.Bits
  IntegerMultiplication.Strip IntegerMultiplication.Strip.Dims IntegerMultiplication.Port
  IntegerMultiplication.Loom IntegerMultiplication.Adic CommonRegisters RegisterWitness GeneratorSyntax
  Space AffineAddress InterchangeROMAddress

/-- A single sign bit in the template controls whether to mirror the
original stream and restore its header before routing the carry lanes. -/
noncomputable def widthCommand (neg : Bool) (slot : Location) (static : Template) : Cmd :=
  bif neg then (restoring (InterchangeROMMirror.compiled slot)).join (compile core static)
  else compile core static

theorem width_registers : ∃ R, ∀ neg l s, Within R (widthCommand neg l s) := by
  obtain ⟨a,ha⟩ := uniform_registers
  obtain ⟨b,hb⟩ := InterchangeROMMirror.uniform_registers
  obtain ⟨c,hp,hr⟩ := ((RegisterSelect.within_eventually parkHeader).and
    (RegisterSelect.within_eventually returnHeader)).exists
  let R := max a (max b c)
  have h₁ := RegisterSelect.within_mono (A:=Ltr) (R:=a) (S:=R) (le_max_left ..)
  have h₂ := RegisterSelect.within_mono (A:=Ltr) (R:=b) (S:=R) ((le_max_left ..).trans (le_max_right ..))
  have h₃ := RegisterSelect.within_mono (A:=Ltr) (R:=c) (S:=R) ((le_max_right ..).trans (le_max_right ..))
  refine ⟨R,fun n loc static => ?_⟩
  cases n with
  | false => exact h₁ _ (ha static)
  | true => exact ⟨⟨h₃ _ hp,h₂ _ (hb loc),h₃ _ hr⟩,h₁ _ (ha static)⟩

noncomputable def numericWidth (p n : ℕ) (s : Bool × ℕ) (neg : Bool) (top down : ℕ) : Cmd :=
  let l := InterchangeROMMirror.numericLocation p n s
  let ab := InterchangeAffineMask.widthRows neg top down
  widthCommand neg l ((l,l),InterchangeAffineMask.template ab.1 ab.2)

theorem width_effective {X : Type} [Primcodable X] {p n : X → ℕ} {s : X → Bool × ℕ}
    {neg : X → Bool} {top down : X → ℕ} (hp : Computable p) (hn : Computable n)
    (hs : Computable s) (hneg : Computable neg) (ht : Computable top) (hd : Computable down) :
    Effective ltr fun x => numericWidth (p x) (n x) (s x) (neg x) (top x) (down x) := by
  have rows := InterchangeAffineMask.primrec_widthRows.to_comp.comp (hneg.pair (ht.pair hd))
  have lanes := effective hp hn hs hs (Computable.fst.comp rows) (Computable.snd.comp rows)
  have pre := effective_restoring (InterchangeROMMirror.effective_compiled hp hn hs)
  apply (Computable.cond hneg (pre.join lanes) lanes).of_eq
  intro x
  cases h : neg x <;> simp only [numericWidth,widthCommand,h,Bool.cond_false,Bool.cond_true]

def joinUsage (u v : Usage) : Usage :=
  ⟨u.time+v.time+2,max u.space v.space,max (u.depth+1) v.depth⟩

private theorem join_bounded {u v : Usage} {c g : Cmd} {x y z : Tree} {env : Env} {r : Deck} {base : ℕ}
    (p : BoundedFits env c (pile 0 x r) (pile 0 y r) u.time (base+u.space) u.depth)
    (q : BoundedFits env g (pile 0 y r) (pile 0 z r) v.time (base+v.space) v.depth) :
    BoundedFits env (c.join g) (pile 0 x r) (pile 0 z r) (joinUsage u v).time
      (base+(joinUsage u v).space) (joinUsage u v).depth := by
  exact (p.mono le_rfl (Nat.add_le_add_left (le_max_left ..) base) le_rfl).join
    (q.mono le_rfl (Nat.add_le_add_left (le_max_right ..) base) (le_max_right ..)) (le_max_left ..)

def mirrorUsage (K d C : ℕ) (place : Location) (h : Header) (stream : Tree) (cells : ℕ) : Usage :=
  let t := InterchangeROMMirror.projectTime K d place h
  let u := C*((Tree.fork (send (projection (place,h))) stream).count + cells + 1)
  ⟨t+u+2, max ((Tree.fork (send h) stream).count+t) u, max (t+1) u⟩

noncomputable def positiveUsage (K d e : ℕ) (x : Input InterchangeAffineMask.modulus) : Usage :=
  let t := time K d e x
  ⟨t,(input x).count+t,t⟩

/-- Exact clocks and peak allowances compose only the phases used by the
selected sign. `z` is the stream after the optional mirror. -/
def widthUsage (neg : Bool) (h x z : Tree) (m lane : Usage) : Usage :=
  bif neg then joinUsage (restoreUsage h x z m) lane else lane

theorem run_width :
    ∃ K d e Km dm Cm : ℕ, ∀ {J : Type} [DecidableEq J] {n b f : ℕ} [NeZero b]
      (ord : J ≃ Fin n) (P G S : Tape) (hp : solid P) (hg : solid G) (hs : solid S) (hb : 2 ≤ b)
      (slot : Spot J) (a : Span b) (v : Keys P G S J (Block b f) → Tree)
      env deck base, DeckCap base deck →
      let h := header f P G S
      let loc := location ord b slot
      let sl := oneStop (p:=b) (j:=f) (P:=P) (G:=G) (B:=S) ord slot
      let rows := arrays ord (line b f) P G S
      let z := signedSource a.neg sl v
      let x := width ord P G S hp hg hs hb slot a z
      let u := widthUsage a.neg (send h) (stripe rows v) (stripe rows z)
        (mirrorUsage Km dm Cm loc h (stripe rows v) rows.count) (positiveUsage K d e x)
      BoundedFits env (numericWidth b n (slot.1,(ord slot.2).val) a.neg a.top.count a.down.count)
        (pile 0 (.fork (send h) (stripe rows v)) deck)
        (pile 0 (stripe rows (v ∘ (reflect ord (.width slot a) trivial P G S f).symm)) deck)
        u.time (base+u.space) u.depth := by
  obtain ⟨K,d,e,run⟩ := compiled
  obtain ⟨Km,dm,Cm,mirrorRun⟩ := InterchangeROMMirror.compiled_slot
  refine ⟨K,d,e,Km,dm,Cm,?_⟩
  intro J dec n b f nz ord P G S hp hg hs hb slot a v env deck base hd
  let h := header f P G S
  let loc := location ord b slot
  let sl := oneStop (p:=b) (j:=f) (P:=P) (G:=G) (B:=S) ord slot
  let rows := arrays ord (line b f) P G S
  let z := signedSource a.neg sl v
  let x := width ord P G S hp hg hs hb slot a z
  let target := stripe rows (v ∘ (reflect ord (.width slot a) trivial P G S f).symm)
  let lane := positiveUsage K d e x
  let m := mirrorUsage Km dm Cm loc h (stripe rows v) rows.count
  have source : input x = .fork (send h) (stripe rows z) := by
    change Tree.fork (send h) (send ((slotRows sl a z).source.map Prod.snd)) = _
    rw [slotRows_source,stripe_eq]
  have dest : x.rows.answer = target := by
    change send ((slotRows sl a (signedSource a.neg sl v)).target.map Prod.snd) = _
    rw [slotRows_signed]
    exact (stripe_eq _ _).symm
  have advance : BoundedFits env (compile core x.static)
      (pile 0 (.fork (send h) (stripe rows z)) deck) (pile 0 target deck)
      lane.time (base+lane.space) lane.depth := by
    have k := run x env deck base hd
    rw [dest] at k
    rw [← source]
    simpa only [lane,positiveUsage,Nat.add_assoc] using k
  change BoundedFits env (widthCommand a.neg loc x.static)
    (pile 0 (.fork (send h) (stripe rows v)) deck) (pile 0 target deck)
    (widthUsage a.neg (send h) (stripe rows v) (stripe rows z) m lane).time
    (base+(widthUsage a.neg (send h) (stripe rows v) (stripe rows z) m lane).space)
    (widthUsage a.neg (send h) (stripe rows v) (stripe rows z) m lane).depth
  cases eql : a.neg with
  | false =>
    have eqz : z = v := by simp [z,signedSource,eql]
    simpa only [eqz,widthCommand,widthUsage,Bool.cond_false] using advance
  | true =>
    have mir : ∀ r k, DeckCap k r →
        BoundedFits env (InterchangeROMMirror.compiled loc)
          (pile 0 (.fork (send h) (stripe rows v)) r) (pile 0 (stripe rows z) r)
          m.time (k+m.space) m.depth := by
      intro r k hr
      have arm := mirrorRun ord slot P G S hp hg hs hb v env r k hr
      simpa only [m,mirrorUsage,h,loc,rows,z,sl,signedSource,eql,ite_true] using arm
    have both := restoring_bounded _ (send h) (stripe rows v) (stripe rows z) m env mir deck base hd
    exact join_bounded both advance

end InterchangeROMAddress.Affine

end NearSquareRoot
end Computability
end OAI
