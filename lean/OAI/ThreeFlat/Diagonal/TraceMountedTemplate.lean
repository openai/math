import OAI.ThreeFlat.RAM.TraceMountedSeed
import OAI.ThreeFlat.RAM.PhysicalInputPhases

namespace OAI
/-! # Packing the mounted H gate table into private words for selected reads -/

namespace ThreeFlat.Diagonal.NavigationPass
open RAM Computability.VPVNP.BurstRAM TraceAddressRecord RAM.PhysicalPrelude
open scoped Fin.CommRing
variable {F : Type} [Field F] [Fintype F] {w q : ℕ}

/-- Scalar words of the fixed local row program. Its data are shared by all physical rows. -/
def templateWords {n : ℕ} (H : BitNetwork F n) (codec : FieldCode F w)
    (records : Fin n→TraceAddressRecord.Record) : List ℕ :=
  List.ofFn (fun j : Fin (FixedTraceImage.count H) => (FixedTraceImage.word H codec records j.val).val)

omit [Field F] [Fintype F] in
@[simp] theorem templateWords_length {n : ℕ} (H : BitNetwork F n) (codec : FieldCode F w)
    (records : Fin n→TraceAddressRecord.Record) : (templateWords H codec records).length=FixedTraceImage.count H := by
  simp [templateWords]

omit [Field F] [Fintype F] in
private theorem template_at (nav : List ℕ) (G : BitNetwork F q) (code : FieldCode F w)
    (key : Fin q→Record) (i : ℕ) (live : i<FixedTraceImage.count G) :
    (((nav++templateWords G code key)[nav.length+i]?.getD 0 : ℕ) : Word w) =
      FixedTraceImage.word G code key i := by
  rw [List.getElem?_append_right (Nat.le_add_right _ _),Nat.add_sub_cancel_left]
  simp [templateWords,live]

omit [Field F] [Fintype F] in
/-- The ordinary word-prefix coordinates returned by the physical parameter mount
supply exactly the MSB-first H gate/port bit tape required by the fifteen-label
packing boot. -/
theorem template_bits (nav : List ℕ) (G : BitNetwork F q) (code : FieldCode F w)
    (key : Fin q→Record) (base : ℕ) (m : Memory w) (hw : 0<w)
    (read : ∀ i, i<(nav++templateWords G code key).length → ∀ j,j<w →
      m (base+w*i+j) =
        (((((nav++templateWords G code key)[i]?.getD 0 : ℕ) : Word w).val.testBit (w-1-j)).toNat : Word w)) :
    ∀ i : Fin (w*FixedTraceImage.count G),
      m ((base+w*nav.length)+i.val)=((FixedTraceImage.parameter G code key i).toNat : Word w) := by
  intro i
  let a := i.val/w
  let b := i.val%w
  have ha : a<FixedTraceImage.count G := by
    apply (Nat.div_lt_iff_lt_mul hw).mpr
    simp [Nat.mul_comm]
  have hb : b<w := Nat.mod_lt _ hw
  have sum : w*a+b=i.val := Nat.div_add_mod i.val w
  have atWord := read (nav.length+a) (by simp [ha]) b hb
  rw [template_at nav G code key a ha] at atWord
  have addr : (base+w*nav.length)+i.val=base+w*(nav.length+a)+b := by
    rw [Nat.mul_add]; omega
  rw [addr]
  exact atWord

/-- Specialize the native packing input to the actual mounted tick pins after
choosing both endpoint words, including writes beyond the compact template. -/
theorem mounted_template_bits {nt ns a : ℕ} (I : Image F w) (nav : List ℕ) (G : BitNetwork F q)
    (code : FieldCode F w) (key : Fin q→Record) (tmp : ℕ) (es : List (EffectStream.Record w))
    (D : Fin I.advice→Bool) (team : Fin nt→Bool) (step : Fin ns→Bool)
    (par : Fin I.parameters→Bool) (oa na oc nc : Fin a→Bool) (hw : 0<w)
    (fit : w*((nav++templateWords G code key).length+2*es.length)+w*FixedTraceImage.count I.G≤I.parameters)
    (remount : let words := nav++templateWords G code key
      TraceMountedParameters.parameters I 0 (words.length+2*es.length)
        (TraceMountedParameters.seedWords words.length tmp (fun i=>(words[i]?.getD 0 : Word w)) es)
        (fun _=>false)=par) :
    let m := TickMountedPins.memory (w:=w) (ApproximateImage.fields D team step par oa na oc nc)
    ∀ i : Fin (w*FixedTraceImage.count G),
      m ((2+I.advice+nt+ns+w*nav.length)+i.val)=((FixedTraceImage.parameter G code key i).toNat : Word w) := by
  intro m
  let words := nav++templateWords G code key
  let word := fun i : ℕ=>(words[i]?.getD 0 : Word w)
  have H := (TraceMountedParameters.physical_seed I D team step (fun _=>false) oa na oc nc 0 words.length tmp
    0 0 0 word es hw (by simpa only [Nat.zero_add] using fit)).2.1
  change (∀ i,i<words.length → ∀ j,j<w →
    TickMountedPins.memory (w:=w) (ApproximateImage.fields D team step
      (TraceMountedParameters.parameters I 0 (words.length+2*es.length)
        (TraceMountedParameters.seedWords words.length tmp word es) (fun _=>false)) oa na oc nc)
      (2+I.advice+nt+ns+0+w*i+j)=(((word i).val.testBit (w-1-j)).toNat : Word w)) at H
  rw [remount] at H
  exact template_bits nav G code key _ m hw (by simpa only [Nat.add_zero] using H)

omit [Fintype F] in
/-- Pack precisely the finite H template, leaving the virtual global trace in the
denotation of the selected 430-bind read. -/
theorem template_pack_spec (nav : List ℕ) (G : BitNetwork F q) (code : FieldCode F w)
    (key : Fin q→Record) (base dst : ℕ) (hw : 0<w)
    (apart : dst+FixedTraceImage.count G≤base+w*nav.length ∨
       (base+w*nav.length)+w*FixedTraceImage.count G≤dst)
    (dstFit : dst+FixedTraceImage.count G<2^w) (srcFit : (base+w*nav.length)+w*FixedTraceImage.count G<2^w) :
    (PhysicalInputPhases.packing w (base+w*nav.length) dst (FixedTraceImage.count G)).Spec
      (fun m=> ∀ i,i<(nav++templateWords G code key).length → ∀ j,j<w →
        m (base+w*i+j) =
          (((((nav++templateWords G code key)[i]?.getD 0 : ℕ) : Word w).val.testBit (w-1-j)).toNat : Word w))
      (fun m m'=>m'=FixedTraceImage.packed G code key dst m) (FixedTraceImage.count G*(5*w+6)+6) := by
  intro P r K M pc reg pub exit installed data c m start read
  exact PhysicalInputPhases.packing_spec_disjoint G code key _ dst apart dstFit srcFit
    M pc reg pub exit installed data c m start (template_bits nav G code key base m hw read)


end ThreeFlat.Diagonal.NavigationPass

end OAI
