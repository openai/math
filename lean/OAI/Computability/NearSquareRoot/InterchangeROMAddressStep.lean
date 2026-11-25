import OAI.Computability.NearSquareRoot.InterchangeROMAddressPivot
import OAI.Computability.NearSquareRoot.InterchangeROMAddressAffineWidthClock
import OAI.Computability.NearSquareRoot.InterchangeROMWordLedger

/-! # Open recursive semantics of every generated address opcode -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OpcodeProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Loom IntegerMultiplication.Adic
  IntegerMultiplication.Port InterchangeROMAddress InterchangeAddress InterchangeROMSequence

structure Factors where
  coefficient : ℕ
  scale : ℕ
  degree : ℕ

structure Clocks where
  width : Factors
  gather : Factors
  pivotSize : ℕ
  pivotDegree : ℕ

def scan (c : Factors) (b n : ℕ) (s t : Bool × ℕ) (ab : InterchangeAffineMask.Row ℕ × InterchangeAffineMask.Row ℕ)
    (h : Header) (N : ℕ) (src dst : Tree) : ℕ :=
  let spec := ((InterchangeROMMirror.numericLocation b n s,InterchangeROMMirror.numericLocation b n t),
    InterchangeAffineMask.template ab.1 ab.2)
  Affine.scanPrice c.coefficient c.scale c.degree (InterchangeAffineMask.colors ab.1 ab.2).length
    spec h N src dst

def cost (c : Clocks) (b n : ℕ) (o : Opcode.Op) (h : Header) (N : ℕ) (src dst : Tree) : ℕ :=
  if Opcode.tag o = 0 then scan c.width b n (Opcode.target o) (Opcode.target o)
    (InterchangeAffineMask.widthRows (Opcode.negative o) (Opcode.numerator o) (Opcode.denominator o)) h N src dst
  else if Opcode.tag o = 1 then scan c.gather b n (Opcode.source o) (Opcode.target o)
    (InterchangeAffineMask.gatherRows (Opcode.negative o) (Opcode.numerator o) (Opcode.denominator o)) h N src dst
  else pivotPrice c.pivotSize c.pivotDegree (numericSpec b n [((Opcode.target o).2,(Opcode.source o).2)]) h src dst

def Valid {b : ℕ} (f N l : ℕ) (P G S : Tape) (good : Tree → Prop) (q : Request b) : Prop :=
  (q.width=f ∧ q.rows.count=N ∧ q.recordWidth=l) ∧ (∀ z, good (q.contents z)) ∧ inherited b P G S q

private theorem free {b : ℕ} {code_ : Cmd} {h x y : Tree} {t : ℕ}
    (run : ∀ env deck base, Space.DeckCap base deck →
      Space.BoundedFits env code_ (pile 0 (.fork h x) deck) (pile 0 y deck) t (base+t) t) :
    Step (Request.job b) code_ h x y [] t t t := by
  intro parent env _ _ _ _ deck base hbase
  simpa only [InterchangeSpace.childPeak,List.foldr_nil,List.map_nil,List.sum_nil,Nat.add_zero] using
    run (parent::env) deck base hbase

/-- The same finite numerical dispatcher serves all radices and dimensions.
A pivot contributes its unique physical request, and the two nonrecursive
cases consume no calls. The child copies only original cells and inherits
every exposed radix from the layout or the common field. -/
theorem run_step : ∃ c : Clocks, ∀ {n b f : ℕ} [NeZero b] (P G S : Tape)
    (_ : solid P) (_ : solid G) (_ : solid S) (_ : 2 ≤ b) (l : ℕ)
    (op : Lag (Fin n) b) (legal : op.legal (ranking (Equiv.refl (Fin n))))
    (v : Keys P G S (Fin n) (Block b f) → Tree) (good : Tree → Prop) (_ : ∀ k, good (v k)),
    let ord := Equiv.refl (Fin n)
    let s := arrays ord (line b f) P G S
    let h := header f P G S
    let src := stripe s v
    let dst := stripe s (v ∘ (reflect ord op legal P G S f).symm)
    let t := cost c b n (Opcode.encode op) h s.count src dst
    ∃ qs, qs.length = op.prices ∧ (∀ q∈qs, Valid (b:=b) f s.count l P G S good q) ∧
      Step (Request.job b) (dispatch b n (Opcode.encode op)) (send h) src dst qs t t t := by
  obtain ⟨Mw,Cw,jw,width⟩ := Affine.width_command
  obtain ⟨Mg,Cg,jg,gather⟩ := Affine.gather_command
  obtain ⟨K,j,pivot⟩ := pivot_command
  refine ⟨⟨⟨Mw,Cw,jw⟩,⟨Mg,Cg,jg⟩,K,j⟩,?_⟩
  intro n b f nz P G S hP hG hS hb l op leg v good cells
  let ord := Equiv.refl (Fin n)
  cases op with
  | width i a =>
    refine ⟨[],rfl,by simp,free ?_⟩
    exact width ord P G S hP hG hS hb i a v
  | gather i k a =>
    refine ⟨[],rfl,by simp,free ?_⟩
    have run := gather ord P G S hP hG hS hb i k leg a v
    cases a <;> exact run
  | pivot i k =>
    exact pivot P G S i k l v good cells

end OpcodeProgram

end NearSquareRoot
end Computability
end OAI
