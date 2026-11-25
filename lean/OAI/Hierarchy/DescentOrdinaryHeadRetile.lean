import OAI.Hierarchy.DescentOrdinaryRoleRetile
import OAI.Hierarchy.DescentOrdinaryHeadRetileLayout

namespace OAI
/-! # Materialize measured expressions at their source pitch and resample the host prefix -/
namespace Hierarchy.DescentOrdinaryHeadRetile
open DescentSIMDLookup DescentPackedColony DescentPackedZip DescentSixParty.Chronology ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

namespace Shape
variable (S : Shape)
def role : DescentOrdinaryRoleRetile.Layout :=⟨S.n,S.hosts,S.groups,S.before,S.after,S.bits⟩
def staged (base : ℕ) (i : Fin S.n) : Bank :=⟨base+i.val*S.oldRows,Nat.clog 2 (S.oldRows+1)⟩
def bank (base : ℕ) (i : Fin S.n) :=S.role.bank (S.roleStart base) i

def column (src : Fin S.n→Expr) (j : ℕ) : Expr := if live:j<S.n then src ⟨j,live⟩ else .lit 0
def gather (base : ℕ) (src : Fin S.n→Expr) :=DescentPackedFlowBatch.passes base S.oldRows S.oldRows (S.column src) 0 S.n
def head (base : ℕ) (src : Fin S.n→Expr) (w : ℕ) : NativePhase w :=
  ⟨ProtocolRAM.program w (S.gather base src),clock (S.gather base src),result (S.gather base src),
    ProtocolRAM.program_cheap w (S.gather base src)⟩
def phase (base : ℕ) (src : Fin S.n→Expr) (w : ℕ) : NativePhase w :=
  (S.head base src w).seq (S.role.phase (S.roleStart base) (S.staged base) w)

variable (base : ℕ) (src : Fin S.n→Expr) {w : ℕ} (m : Memory w)
variable (fits : ∀i,(src i).Fits w base) (room : S.endAddress base<2^w)

include room in
theorem staged_placed (i : Fin S.n) :
    (S.staged base i).Fits w (S.roleStart base) ∧ S.oldRows≤(S.staged base i).size :=by
  have before:=Nat.add_le_add_left (Nat.mul_le_mul_right S.oldRows i.isLt.le) base
  have e:(S.staged base i).base+(S.staged base i).size≤S.roleStart base :=Nat.add_le_add_right before _
  exact ⟨⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (e.trans_lt ((S.layout base).2.trans_lt room)),e⟩,
    (Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)⟩

include room in
theorem placed (i : Fin S.n) :
    (S.bank base i).Fits w (S.endAddress base) ∧ S.hosts*chunks S.groups S.after≤(S.bank base i).size :=
  S.role.placed (S.roleStart base) room i

include fits room in
private theorem measured :
    (S.head base src w).Runs m ∧
    (∀p : Fin S.n,∀j : Fin S.oldRows,(S.head base src w).image m (base+p.val*S.oldRows+j.val)=(src p).eval m (j.val:Word w)) ∧
      ∀a<base,(S.head base src w).image m a=m a :=by
  have live:=DescentPackedFlowBatch.execute base S.oldRows S.oldRows S.n (S.column src) m
    (fun j hj=>by simpa only [column,dite_eq_left hj] using fits ⟨j,hj⟩)
    ((S.layout base).1.trans ((S.layout base).2) |>.trans_lt room) le_rfl
  refine ⟨live.1,?_,live.2.2⟩
  intro p j
  simpa only [head,gather,column,dite_eq_left p.isLt,Fin.eta] using live.2.1 p j

include fits room in
theorem any : (S.phase base src w).Runs m ∧
    ∀a, a < base ∨ S.endAddress base ≤ a → (S.phase base src w).image m a=m a :=by
  have head_:=S.measured base src m fits room
  have retile:=S.role.any (S.roleStart base) (S.staged base) ((S.head base src w).image m)
    (fun p=>(S.staged_placed base room p).1) room
  refine ⟨NativePhase.seq_runs _ _ m head_.1 retile.1,?_⟩
  intro a away
  rcases away with lo|hi
  · exact (retile.2 a (.inl (lo.trans_le ((Nat.le_add_right ..).trans (S.layout base).1)))).trans (head_.2.2 a lo)
  · have stop_:base+(0+S.n)*S.oldRows≤a:=by
      rw [Nat.zero_add]
      exact (S.layout base).1.trans ((S.layout base).2.trans hi)
    exact (retile.2 a (.inr hi)).trans (DescentPackedFlowBatch.above base S.oldRows S.oldRows _ m 0 S.n a le_rfl stop_)

include fits room in
theorem reads (i : Fin S.n) (value : Fin S.hosts→Fin S.groups→Cell S.bits)
    (nonempty : 0<S.before) (original : Source (src i) value S.before m) :
    Reads (S.bank base i) value S.after ((S.phase base src w).image m) :=by
  have physical:=S.measured base src m fits room
  apply S.role.reads (S.roleStart base) (S.staged base) ((S.head base src w).image m)
    (fun j=>(S.staged_placed base room j).1) room i value nonempty (S.staged_placed base room i).2
  intro r
  exact (physical.2.1 i (row S.hosts S.groups S.before r)).trans (original r)

def restrict {H : ℕ} (bound : H≤S.hosts) (value : Fin S.hosts→Fin S.groups→Cell S.bits) :
    Fin H→Fin S.groups→Cell S.bits :=fun h=>value (Fin.castLE bound h)

/-- The numeric row inputs of an expression are identical on any initial host interval. -/
theorem restrict_source {H M : ℕ} (bound : H≤S.hosts) (value : Fin S.hosts→Fin S.groups→Cell S.bits)
    (e : Expr) (represented : Source e value M m) : Source e (S.restrict bound value) M m :=by
  intro t
  let u : Row S.hosts S.groups M :=(Fin.castLE bound t.1,t.2)
  have index : (row S.hosts S.groups M u).val=(row H S.groups M t).val :=by
    simp [row,finProdFinEquiv_apply_val,u]
  have words : data value u=data (S.restrict bound value) t := rfl
  simpa only [index,words] using represented u

include fits room in
theorem source (i : Fin S.n) (value : Fin S.hosts→Fin S.groups→Cell S.bits) (nonempty : 0<S.before)
    (original : Source (src i) value S.before m) {H : ℕ} (bound : H≤S.hosts) :
    Source (.lookup (S.bank base i) .row) (S.restrict bound value) S.after ((S.phase base src w).image m) :=by
  have read:=S.reads base src m fits room i value nonempty original
  have banked:=S.placed base room i
  apply S.restrict_source _ bound value
  exact source_column _ (S.endAddress base) banked.1 _ value banked.2 read

end Shape
end
end Hierarchy.DescentOrdinaryHeadRetile

end OAI
