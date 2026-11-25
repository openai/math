import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalSweep
import OAI.Computability.NearSquareRoot.InterchangeROMAddressEffective
import OAI.Computability.NearSquareRoot.InterchangeSpectralPacked

/-! # A single compiled pivot on the occupied spectral field -/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section
namespace InterchangeROMRepair.Sweep

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Adic IntegerMultiplication.Loom
  CommonRegisters Space InterchangeROMAddress InterchangeAddress InterchangeBatch InterchangeSpace
  GeneratorSyntax
open InterchangeROMRepair.Physical (Allowance)
open private inherits from OAI.Computability.NearSquareRoot.InterchangeSpectralPacked

def pivot (b n j : ℕ) := InterchangeROMAddress.command exists_core.choose (numericSpec b n [(j,j)])

def pivotRegs := exists_core.choose_spec.choose
def pivotK := exists_core.choose_spec.choose_spec.choose
def pivotDegree := exists_core.choose_spec.choose_spec.choose_spec.choose

theorem pivot_within (b n j : ℕ) : Within pivotRegs (pivot b n j) :=
  exists_core.choose_spec.choose_spec.choose_spec.choose_spec.1 _

theorem effective_pivot {X : Type} [Primcodable X] {b n j : X → ℕ}
    (hb : Computable b) (hn : Computable n) (hj : Computable j) :
    Effective ltr (fun x => pivot (b x) (n x) (j x)) :=
  effective_pivots exists_core.choose hb hn
    (Computable.list_cons.comp (hj.pair hj) (Computable.const []))

def pivotCost (b n j : ℕ) (h : Header) (hdr input output : Tree) (a : Allowance) : Allowance :=
  let T := headerTime (numericSpec b n [(j,j)]) h pivotK pivotDegree
  let H := (Task.forest id [hdr]).count
  let V := max input.count output.count
  ⟨T + (a.time + 1 + 110 * (H+1)) + 2,
    max ((Tree.fork (send h) input).count + T) (dataSpace V H a.cap),
    max (T+1) (returnSpace H a.depth)⟩

variable {I J : Type} [DecidableEq J] {b n : ℕ}
  (ord : J ≃ Fin n) (P G B : I → Dims.Tape) (f l : I → ℕ) (j : J)
  (v : (i : I) → domain (J:=J) (b:=b) P G B f i → Tree) (u : I)

abbrev child := InterchangeSpectralRequest.child ord P G B f j l v u

theorem child_allowed :
    allowed f (countRows (b:=b) ord P G B f) l u (child ord P G B f l j v u) :=
  InterchangeSpectralRequest.allowed_child ord P G B f j l v u

theorem child_inherited : inherited b (P u) (G u) (B u) (child ord P G B f l j v u) :=
  inherits ord P G B f l j v u

/-- The selected mover invokes the enclosing recursive command on precisely the
one canonical spectral request. Its time enters the clock with coefficient one. -/
theorem pivot_bounded (parent : Cmd) (env : Env) (a : Allowance)
    (childRun : Run (parent::env) parent ((Request.job b).issue (child ord P G B f l j v u))
      ((Request.job b).reply (child ord P G B f l j v u)) a) :
    let q := child ord P G B f l j v u
    let h := header (f u) (P u) (G u) (B u)
    let x := stripe (layoutRows ord P G B f u) (v u)
    let y := stripe (layoutRows ord P G B f u) (fun z => v u (InterchangeSpectralRequest.swapAt j z))
    Run (parent::env) (pivot b n (ord j)) (.fork (send h) x) y
      (pivotCost b n (ord j) h q.header x y a) := by
  intro q h x y
  have issue := congrFun (InterchangeSpectralRequest.child_issue ord P G B f j l v) u
  change Tree.fork q.header (Request.payload q) = .fork q.header x at issue
  have hx : Request.payload q = x := (Tree.fork.inj issue).2
  have hy : (Request.job b).reply q = y :=
    congrFun (InterchangeSpectralRequest.reply ord P G B f j l v) u
  let sp := numericSpec b n [((ord j).val,(ord j).val)]
  have ht : send (plan (sp,h)) = headers Request.header [q] := by
    change Tree.fork (send (InterchangeROMAddress.one _)) (.atom false) = Tree.fork q.header (.atom false)
    exact congrArg (fun z : Header => Tree.fork (send z) (.atom false))
      (one_header ord (P u) (G u) (B u) b (f u) j j)
  have chain : Chain Request.payload (Request.job b).reply x [q] y := by
    rw [← hx,← hy]
    exact .cons q (.nil _)
  intro deck base hd
  have call := InterchangeROMAddress.run exists_core.choose pivotK pivotDegree
    exists_core.choose_spec.choose_spec.choose_spec.choose_spec.2 sp h Request.header Request.payload
    (Request.job b).reply (fun _ => a.time) (fun _ => a.cap) (fun _ => a.depth)
    parent env (max x.count y.count) ht chain
    (by intro z hz; simp only [List.mem_singleton] at hz; subst z; rw [hx]; exact le_max_left ..)
    (le_max_right ..)
    (by intro z hz; simp only [List.mem_singleton] at hz; subst z; exact childRun)
    deck base hd
  simpa only [pivot,pivotCost,sp,childPeak,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
    List.foldr_cons,List.foldr_nil,List.length_cons,List.length_nil,Nat.zero_add,Nat.add_zero,
    Nat.zero_le,Nat.max_eq_left,headers,Task.forest_cons,Task.forest_nil,id_eq] using call

end InterchangeROMRepair.Sweep

end

end NearSquareRoot
end Computability
end OAI
