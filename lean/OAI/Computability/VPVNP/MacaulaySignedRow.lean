import OAI.Computability.VPVNP.MacaulayAppendedPower

/-! # Native read of a shifted integer equation in the Macaulay matrix

The reader decodes both monomials, checks divisibility, and, on its true
branch, counts the signed coefficient at their coordinatewise difference.
The reader restores its flag and residual buffer after returning the scalar.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead.Arms

open BurstRAM RAMTape UniversalCountStack JointLabelSystem RadicalCertificate.MonomialIndex
open MacaulayRowDispatch MvPolynomial

variable {K : Type} [DecidableEq K] {p e w A S v : ℕ} [Fact p.Prime] [NeZero e]
variable {modulus : SliceArithmetic.Vector p e}
variable {E : Type*} [Field E] [Algebra (ZMod p) E]
variable (V I : Type*) [Fintype V] [Fintype I] (F : I → MvPolynomial V ℤ) {n : ℕ} (c : ℕ)

/-- The complete guarded original-row phase on the ordinary reader advice. -/
theorem signed_row (hn : 2 ≤ n) (φ : AdjoinRoot (SliceArithmetic.modulus modulus) ≃ₐ[ZMod p] E)
    (inc : JointScalar.Leaf.Port ↪ K) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    {eqs : ℕ} (Q : QueryData (FixedRows.labelTotal V n c) eqs E)
    (rs : Reg → Word w) (aux : Stacks K)
    (pre : Preload (w := w) A (BaseAdvice.inputs Q) (BaseAdvice.scalars modulus v) aux)
    (hw : 1 ≤ w) (row : Fin (2^n+Fintype.card I))
    (source : Fin (size (FixedRows.labelTotal V n c) Q.multiplierDegree))
    (column : Fin (size (FixedRows.labelTotal V n c) Q.columnDegree))
    (hrow : (rs (outReg 1)).val = row.val) (hsource : (rs (outReg 2)).val = source.val)
    (hcolumn : (rs (outReg 3)).val = column.val) (hwidth : PairCall.requiredWidth (BaseAdvice.inputs Q false) ≤ w)
    (loaded : SignedLeaf.Loaded (JointScalar.Leaf.layout V I F c hn w p e v) inc aux)
    (hspace : PairCall.equationSpace w A (BaseAdvice.inputs Q false) ≤ S)
    (htrans : transient A (FixedRows.labelTotal V n c) w ≤ S)
    (hscalar : SignedLeaf.callSpace V I F c hn w v modulus ≤ S) :
    let t := FixedRows.labelTotal V n c
    let a := enumeration t Q.multiplierDegree source
    let b := enumeration t Q.columnDegree column
    let poly := MvPolynomial.map (Int.castRingHom E) (unionEquations (grammarEquation hn c) F (FixedRows.rowIndex I n row))
    let ans : Scalar modulus := if a.val ≤ b.val then AffinePin.Query.encode φ (poly.coeff (b.val-a.val)) else 0
    let ticks := SignedLeaf.callTime V I F c hn w v modulus
    ∃ steps ≤ PairCall.scanClock w A (BaseAdvice.inputs Q false) + PairCall.packClock t w A +
      PairCall.clearCost w + postTicks A t w ticks,
      (phase false (JointScalar.Leaf.machine.onPorts (SignedLeaf.ports inc))).BoundedRun S steps
        (frame rs [] (storage w (BaseAdvice.inputs Q) blank blank (BaseAdvice.scalars modulus v) aux))
        (frame rs (Engine.scalar v ans) (storage w (BaseAdvice.inputs Q) blank blank (BaseAdvice.scalars modulus v) aux)) := by
  intro t a b poly ans ticks
  let data := BaseAdvice.inputs Q
  let constants := BaseAdvice.scalars modulus v
  let d := addressed rs (data false)
  let ords : PairCall.Ordinals d := fun bit => match bit with
    | false => source
    | true => column
  have hk (bit : Bool) : d.ordinal bit = (ords bit).val := by cases bit; exact hsource; exact hcolumn
  obtain ⟨fit,_⟩ := PairCall.fits_of_width d ords hwidth
  let residual := b.val-a.val
  let yes := Engine.scalar v (AffinePin.Query.encode φ (poly.coeff residual))
  let packed := PairCall.difference w a b
  let pack := selected false packed
  let flag := selected false (digits w (decide (a.val ≤ b.val)).toNat)
  have hp : packed.length = t*w := PairCall.length_difference ..
  have hflag : ∀ q, (flag q).length ≤ w := by intro q; cases q <;> simp [flag,selected,blank]
  have hA : e*v ≤ A := by simpa only [BaseAdvice.scalars,Engine.scalar_length] using pre.scalars false
  have hy : yes.length ≤ A := (Engine.scalar_length ..).le.trans hA
  have hbig : A+t*w+w ≤ S := by change transient A t w ≤ S at htrans; unfold transient at htrans; omega
  have room : ∀ z, (frame rs [] (storage w data pack flag constants aux) z).length ≤ S := by
    apply frame_bound
    · exact pre.words.trans (by omega)
    · simp
    · intro q; exact (pre.arity q).trans (by omega)
    · intro q; cases q <;> simp [pack,selected,blank,hp]; omega
    · intro q; exact (hflag q).trans (pre.words.trans (by omega))
    · intro q; exact (pre.scalars q).trans (by omega)
    · intro k; exact (pre.payload k).trans (by omega)
  have hres (i : Fin t) : residual i < 2^w := by
    have hb : b.val i < Q.columnDegree+1 := (b.encode i).isLt
    have hdeg : Q.columnDegree+1 < 2^w := (fit true).base_lt
    change b.val i - a.val i < 2^w
    exact (Nat.sub_le ..).trans_lt (hb.trans hdeg)
  have read := equation_execution rs data constants aux pre hw (JointScalar.Leaf.machine.onPorts (SignedLeaf.ports inc))
    yes hy ticks ords hk fit hspace htrans
  obtain ⟨steps,ht,run⟩ := read (fun _ => by
    obtain ⟨steps,ht,call⟩ := SignedLeaf.coefficient V I F c hn φ inc hv row residual hres rs hrow data pack flag
      constants aux (by rw [show pack false = packed from Function.update_self ..]; rfl) loaded hscalar room
    exact ⟨steps,ht,packed,hp.le,call⟩)
  have result : (if a.val ≤ b.val then yes else constants false) = Engine.scalar v ans := by
    by_cases h : a.val ≤ b.val <;> simp only [ans,h,ite_true,ite_false] <;> rfl
  change (phase false _).BoundedRun S steps _ (frame rs (if a.val ≤ b.val then yes else constants false) _) at run
  exact ⟨steps,ht,result ▸ run⟩


/-- A single reader plan supplies the scan, temporary-buffer and counted
coefficient budgets before the matrix entry is selected. -/
theorem signed_row_plan (hn : 2 ≤ n) (φ : AdjoinRoot (SliceArithmetic.modulus modulus) ≃ₐ[ZMod p] E)
    (inc : JointScalar.Leaf.Port ↪ K) (hv : SliceArithmetic.Word.workingWidth p ≤ v)
    (P : ReaderPlan) {eqs : ℕ} (Q : QueryData (FixedRows.labelTotal V n c) eqs E)
    (ha : FixedRows.labelTotal V n c = P.arity)
    (hl : Q.multiplierDegree ≤ P.source) (hd : Q.columnDegree ≤ P.column)
    {Emax vmax : ℕ} (he : e ≤ Emax) (hvw : v ≤ vmax) (sp ex : ℕ)
    (hsp : SignedLeaf.callSpace V I F c hn w v modulus ≤ sp)
    (htime : SignedLeaf.callTime V I F c hn w v modulus ≤ 2^ex) (hw : P.wordWidth ≤ w)
    (rs : Reg → Word w) (aux : Stacks K)
    (pre : Preload (w := w) (P.live Emax vmax w sp) (BaseAdvice.inputs Q) (BaseAdvice.scalars modulus v) aux)
    (loaded : SignedLeaf.Loaded (JointScalar.Leaf.layout V I F c hn w p e v) inc aux)
    (row : Fin (2^n+Fintype.card I))
    (source : Fin (size (FixedRows.labelTotal V n c) Q.multiplierDegree))
    (column : Fin (size (FixedRows.labelTotal V n c) Q.columnDegree))
    (hrow : (rs (outReg 1)).val = row.val) (hsource : (rs (outReg 2)).val = source.val)
    (hcolumn : (rs (outReg 3)).val = column.val) :
    let t := FixedRows.labelTotal V n c
    let a := enumeration t Q.multiplierDegree source
    let b := enumeration t Q.columnDegree column
    let poly := MvPolynomial.map (Int.castRingHom E) (unionEquations (grammarEquation hn c) F (FixedRows.rowIndex I n row))
    let ans : Scalar modulus := if a.val ≤ b.val then AffinePin.Query.encode φ (poly.coeff (b.val-a.val)) else 0
    ∃ steps ≤ P.armTime Emax vmax w sp ex,
      (phase false (JointScalar.Leaf.machine.onPorts (SignedLeaf.ports inc))).BoundedRun (P.armSpace Emax vmax w sp) steps
        (frame rs [] (storage w (BaseAdvice.inputs Q) blank blank (BaseAdvice.scalars modulus v) aux))
        (frame rs (Engine.scalar v ans) (storage w (BaseAdvice.inputs Q) blank blank (BaseAdvice.scalars modulus v) aux)) := by
  intro t a b poly ans
  let A := P.live Emax vmax w sp
  let d := BaseAdvice.inputs Q false
  let ticks := SignedLeaf.callTime V I F c hn w v modulus
  have hwidth := (P.pairWidth_le d ha hl hd (le_max_left ..) (Nat.zero_le _)).trans hw
  obtain ⟨live,space,time⟩ := P.leaf_bounds w sp ex he hvw d ha hl hd
  have had : A + MacaulayRowDispatch.ticks w ≤ P.armSpace Emax vmax w sp := space.2.2.1
  have hspA : sp ≤ A := live.2.2.2.2.1
  have hs := hspA.trans ((Nat.le_add_right A (MacaulayRowDispatch.ticks w)).trans had)
  have htrans : transient A t w ≤ P.armSpace Emax vmax w sp := by
    rw [show t = P.arity from ha]
    exact space.2.2.2.1
  obtain ⟨steps,ht,run⟩ := signed_row V I F c hn φ inc hv Q rs aux pre
    ((by decide : 1≤2).trans (P.dispatchWidth.2.2.trans hw)) row source column hrow hsource hcolumn
    hwidth loaded space.1 htrans (hsp.trans hs)
  have scan := (P.scan_bounds w A d ha hl hd).1
  have hpost : postTicks A t w ticks ≤
      postTicks A P.arity w (max ticks (max (Pin.cost P.arity e w v) (5*(e*v)+2))) := by
    rw [show t = P.arity from ha]
    unfold postTicks
    gcongr
    exact le_max_left ..
  exact ⟨steps,ht.trans ((Nat.add_le_add scan hpost).trans (time ticks htime)),run⟩

end RankQuery.Stack.MacaulayRead.Arms

end VPVNP
end Computability
end OAI
