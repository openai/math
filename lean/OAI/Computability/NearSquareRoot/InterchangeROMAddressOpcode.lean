import OAI.Computability.NearSquareRoot.InterchangeROMAddressGather
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineWidth
import OAI.Computability.NearSquareRoot.InterchangeOpcodeTypes

/-! # Dispatch for each operation in a numerical movement program -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OpcodeProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Port
  IntegerMultiplication.Loom CommonRegisters RegisterWitness GeneratorSyntax
  InterchangeROMAddress
open InterchangeAffineMask (gatherRows)
/-- The header generator of recursive pivot batches is fixed once. -/
noncomputable def pivotCore : Cmd := exists_core.choose

noncomputable def numericGather (b n : ℕ) (tgt src : Bool × ℕ)
    (neg : Bool) (top down : ℕ) : Cmd :=
  let A := gatherRows neg top down
  Affine.compile Affine.core
    ((InterchangeROMMirror.numericLocation b n src, InterchangeROMMirror.numericLocation b n tgt),
      InterchangeAffineMask.template A.1 A.2)

/-- Tags 0 and 1 select width and gather. A valid remaining tag is a pivot.
The pivot shares its recursion binder with the enclosing interchange. -/
noncomputable def dispatch (b n : ℕ) (o : Opcode.Op) : Cmd :=
  if Opcode.tag o = 0 then
    Affine.numericWidth b n (Opcode.target o) (Opcode.negative o) (Opcode.numerator o) (Opcode.denominator o)
  else if Opcode.tag o = 1 then
    numericGather b n (Opcode.target o) (Opcode.source o) (Opcode.negative o) (Opcode.numerator o) (Opcode.denominator o)
  else InterchangeROMAddress.command pivotCore (numericSpec b n [((Opcode.target o).2,(Opcode.source o).2)])

theorem pivot_core : ∃ R K d, (∀ sp, Within R (InterchangeROMAddress.command pivotCore sp)) ∧
    ∀ spec h (stream : Tree) env deck,
      Fits env (InterchangeROMAddress.prepare pivotCore spec) (pile 0 (.fork (send h) stream) deck)
        (pile 0 (.fork (send (plan (spec,h))) stream) deck) (headerTime spec h K d) :=
  exists_core.choose_spec

theorem within : ∃ R, ∀ b n o, Within R (dispatch b n o) := by
  obtain ⟨R,hr⟩ := Affine.width_registers
  obtain ⟨S,hs⟩ := Affine.uniform_registers
  obtain ⟨T,_,_,ht,_⟩ := pivot_core
  refine ⟨max R (max S T),fun b n o => ?_⟩
  unfold dispatch
  split
  · exact RegisterSelect.within_mono (le_max_left ..) _ (hr ..)
  split
  · exact RegisterSelect.within_mono ((le_max_left ..).trans (le_max_right ..)) _ (hs _)
  · exact RegisterSelect.within_mono ((le_max_right ..).trans (le_max_right ..)) _ (ht _)

theorem effective {X : Type} [Primcodable X] {b n : X → ℕ} {op : X → Opcode.Op}
    (hb : Computable b) (hn : Computable n) (ho : Computable op) :
    Effective ltr fun x => dispatch (b x) (n x) (op x) := by
  have tag : Computable fun x => Opcode.tag (op x) := Computable.fst.comp ho
  have tgt : Computable fun x => Opcode.target (op x) := Computable.fst.comp (Computable.snd.comp ho)
  have tail_ := Computable.snd.comp (Computable.snd.comp ho)
  have src : Computable fun x => Opcode.source (op x) := Computable.fst.comp tail_
  have coeff := Computable.snd.comp tail_
  have neg : Computable fun x => Opcode.negative (op x) := Computable.fst.comp coeff
  have top : Computable fun x => Opcode.numerator (op x) := Computable.fst.comp (Computable.snd.comp coeff)
  have down : Computable fun x => Opcode.denominator (op x) := Computable.snd.comp (Computable.snd.comp coeff)
  have hg := InterchangeAffineMask.primrec_gatherRows.to_comp.comp (neg.pair (top.pair down))
  have gather := Affine.effective hb hn src tgt (Computable.fst.comp hg) (Computable.snd.comp hg)
  have width := Affine.width_effective hb hn tgt neg top down
  have piv := effective_pivots pivotCore hb hn (Computable.list_cons.comp
    ((Computable.snd.comp tgt).pair (Computable.snd.comp src)) (Computable.const []))
  have h0 := Primrec.eq.decide.to_comp.comp tag (Computable.const 0)
  have h1 := Primrec.eq.decide.to_comp.comp tag (Computable.const 1)
  apply (Computable.cond h0 width (Computable.cond h1 gather piv)).of_eq
  intro x
  by_cases z : Opcode.tag (op x)=0
  · simp only [dispatch,z,ite_true,decide_true,Bool.cond_true]
  by_cases o : Opcode.tag (op x)=1
  · simp [dispatch,o,numericGather]
  simp [dispatch,z,o]

@[simp] theorem dispatch_width {n b : ℕ} (j : Spot (Fin n)) (a : Span b) :
    dispatch b n (Opcode.encode (.width j a)) =
      Affine.numericWidth b n (Opcode.eraseSpot j) a.neg a.top.count a.down.count := rfl

@[simp] theorem dispatch_gather {n b : ℕ} (x y : Spot (Fin n)) (a : Pinpoint b) :
    dispatch b n (Opcode.encode (.gather x y a)) =
      Affine.compile Affine.core (Affine.spec (Equiv.refl (Fin n)) b y x
        (InterchangeAffineMask.pinRows a).1 (InterchangeAffineMask.pinRows a).2) := by
  cases a <;> rfl

@[simp] theorem dispatch_pivot {b n : ℕ} (x y : Fin n) :
    dispatch b n (Opcode.encode (b:=b) (.pivot x y)) =
      InterchangeROMAddress.command pivotCore (metadata b (Equiv.refl _) [(x,y)]) := rfl

end OpcodeProgram

end NearSquareRoot
end Computability
end OAI
