import OAI.Computability.NearSquareRoot.InterchangeROMAddressWordRaw
import OAI.Computability.NearSquareRoot.InterchangeROMAddressStepClock
import OAI.Computability.NearSquareRoot.InterchangeROMWordPrice

/-! # Frozen numerical cost of an effective native movement word -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OpcodeProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Port
  IntegerMultiplication.Loom IntegerMultiplication.Adic IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims InterchangeROMAddress InterchangeAddress InterchangeSpace

def wordWeight (M C K j b n : ℕ) (ops : Opcode.Word) : ℕ :=
  InterchangeROMSequence.weight (perWord M C K j b n ops) ops.length

theorem computable_wordWeight {X : Type} [Primcodable X] {M C K j b n : X → ℕ} {ops : X → Opcode.Word}
    (hm : Computable M) (hc : Computable C) (hk : Computable K) (hj : Computable j)
    (hb : Computable b) (hn : Computable n) (ho : Computable ops) :
    Computable fun x => wordWeight (M x) (C x) (K x) (j x) (b x) (n x) (ops x) :=
  InterchangeROMSequence.primrec_weight.to_comp.comp
    (computable_perWord hm hc hk hj hb hn ho) (Primrec.list_length.to_comp.comp ho)

/-- All geometry-independent prices can be computed as soon as the template
is selected. The geometry uses only the actual packed input volume, the
number of addresses and the unary header, raised to a fixed absolute power. -/
theorem run_raw_scaled : ∃ M C K j : ℕ, 1 ≤ j ∧ ∀ {n b f : ℕ} [NeZero b] (P G S : Tape)
    (_ : solid P) (_ : solid G) (_ : solid S) (_ : 2 ≤ b) (l : ℕ)
    (ops : Opcode.Word) (ok : Opcode.admissible b n ops = true)
    (v : Keys P G S (Fin n) (Block b f) → Tree) (good : Tree → Prop) (_ : ∀ k, good (v k)),
    let ord := Equiv.refl (Fin n)
    let s := arrays ord (line b f) P G S
    let h := header f P G S
    let src := stripe s v
    let decoded := Opcode.decodeWord ops ok
    let dst := stripe s (v ∘ (recreation ord P G S f decoded (Opcode.legal_decodeWord ops ok)).symm)
    let F := wordWeight M C K j b n ops * geometry j h s.count src src
    ∃ qs, qs.length = Opcode.price ops ∧
      (∀ q∈qs, Valid (b:=b) f s.count l P G S good q) ∧
      InterchangeROMSequence.Step (Request.job b) (word b n ops) (send h) src dst qs F F F := by
  obtain ⟨c,run⟩ := run_raw
  let j := max 1 c.maxDegree
  have hj : 1 ≤ j := le_max_left ..
  refine ⟨c.maxCoefficient,c.maxScale,c.pivotSize,j,hj,?_⟩
  intro n b f nz P G S p g s hb l ops ok v good hgood
  let r := arrays (Equiv.refl (Fin n)) (line b f) P G S
  let h := header f P G S
  let src := stripe r v
  let tick (o : Opcode.Op) := cost c b n o h r.count src src
  let a := perOp c.maxCoefficient c.maxScale c.pivotSize j b n
  let geom := geometry j h r.count src src
  have coeff (o) (_ : o ∈ ops) : tick o ≤ a o * geom := cost_le_perOp_of_degree c (le_max_right ..) b n o h r.count src src
  obtain ⟨qs,card,typed,step⟩ := run P G S p g s hb l ops ok v good hgood
  refine ⟨qs,card,typed,?_⟩
  exact InterchangeROMSequence.scaled _ _ _ _ _ qs ops tick tick tick a src.count geom
    (geometry_source j h r.count src src) (geometry_header hj h r.count src src) coeff coeff coeff step

end OpcodeProgram

end NearSquareRoot
end Computability
end OAI
