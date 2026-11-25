import OAI.Hierarchy.DescentPreparedRootWords
import OAI.Hierarchy.DescentPrimitiveBirthDigits

namespace OAI
/-! # The immutable prior opcode register of a named side, rotor vertex and base -/
namespace Hierarchy.DescentPrimitiveBirth
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHostDirectory DescentSixParty.Chronology
open DescentFallbackPeriod.Projected ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
def rootParts (r n : ℕ) (q : Fin (2*(2^r*2^n))) : Bool×Fin (2^r)×Fin (2^n) :=
  let p : Fin 2×Fin (2^r*2^n):=finProdFinEquiv.symm q
  (finTwoEquiv p.1,finProdFinEquiv.symm p.2)

def rootPage (r n : ℕ) (q : Fin (2*(2^r*2^n))) (l : Fin (r+1)) : Option (RootPage r (2^n)) :=
  let p:=rootParts r n q
  if h:p.2.1.val<2^l.val then
    some (p.1,.inl (⟨(l.val,p.2.1.val),mem_codes (by omega) h⟩,.inr p.2.2))
  else none

def guardBank (base H J M r n D : ℕ) (page : RootPage r (2^n)) : Bank :=
  ⟨(RootTemplates.arena base H J M r n D).output ((rootIndex r (2^n)) page).val,Nat.clog 2 (H*chunks J M)⟩
def guards (base H J M r n D : ℕ) (q : Fin (2*(2^r*2^n))) (l : Fin (r+1)) : Option Bank :=
  (rootPage r n q l).map (guardBank base H J M r n D)

theorem guards_at (base H J M r n D : ℕ) (side : Bool) (low : Fin (2^r)) (gate : Fin (2^n)) (l : Fin (r+1)) (fit : low.val<2^l.val) :
    let id:=finProdFinEquiv (finTwoEquiv.symm side,finProdFinEquiv (low,gate))
    guards base H J M r n D id l=some (guardBank base H J M r n D
      (side,.inl (⟨(l.val,low.val),mem_codes (by omega) fit⟩,.inr gate))) :=by
  simp [guards,rootPage,rootParts,fit]

theorem guard_room {w : ℕ} (base H J M r n D floor : ℕ)
    (past : (RootTemplates.arena base H J M r n D).first (Fintype.card (RootPage r (2^n)))≤floor)
    (room : floor<2^w) (p : RootPage r (2^n)) :
    (guardBank base H J M r n D p).Fits w floor ∧ H*chunks J M≤(guardBank base H J M r n D p).size:=by
  let A:=RootTemplates.arena base H J M r n D
  let i:=(rootIndex r (2^n) p).val
  have slot : A.output i+RootArena.span A.rows≤floor:=(A.end_row i).le.trans <|
    (Nat.add_le_add_left (Nat.mul_le_mul_left A.stride (Nat.succ_le_of_lt ((rootIndex r (2^n)) p).isLt)) A.start).trans past
  change (0<RootArena.span A.rows ∧ RootArena.span A.rows<2^w ∧ A.output i+RootArena.span A.rows≤floor) ∧ A.rows≤RootArena.span A.rows
  exact ⟨⟨Nat.two_pow_pos _,((Nat.le_add_left ..).trans slot).trans_lt room,slot⟩,RootArena.le_span _⟩

theorem guards_room {w : ℕ} (base H J M r n D floor : ℕ)
    (past : (RootTemplates.arena base H J M r n D).first (Fintype.card (RootPage r (2^n)))≤floor)
    (room : floor<2^w) (q l B) (eqn : guards base H J M r n D q l=some B) : B.Fits w floor:=by
  cases source:rootPage r n q l with
  | none=>simp [guards,source] at eqn
  | some p=>have bank : guardBank base H J M r n D p=B:=by simpa [guards,source] using eqn
            exact bank ▸ (guard_room base H J M r n D floor past room p).1

section Receipt
variable {D cap N n r c H G K R M h l t field Ht w : ℕ}
    (a : Receiver D cap N n r c H G K R M h l t field Ht w) (b : RootBook n r D (2^r) cap field)
    (space : a.PreparedFits b) (m : Memory w) (p : RootPage r (2^n))
set_option quotPrecheck false in
local notation "T" => (b.table p).2
theorem prior_guard (floor : ℕ) (past : a.preparedEnd b≤floor) (room : floor<2^w)
    (values : Fin H→Fin (2^c)→Fin (b.table p).1→Cell (T).field)
    (held : ∀j,((T).reads j).Fits w ((RootTemplates.arena (a.headerEnd b) H (2^c) M r n D).middle ((rootIndex r (2^n) p).val)))
    (packed : M*max ((T).field*(b.table p).1) (T).outputBits≤w/2) (positive : 0<M)
    (read : ∀j,Source ((T).reads j) (fun h g=>values h g j) M (a.rootInputState b space m p))
    (later : Memory w) (frame : ∀x,x<floor→later x=a.preparedImage b space m x) :
    Source (.lookup (guardBank (a.headerEnd b) H (2^c) M r n D p) .row)
      (fun h g=>(T).law (encode (T).field (b.table p).1 (values h g))) M later:=by
  let B:=guardBank (a.headerEnd b) H (2^c) M r n D p
  obtain ⟨fit,capacity⟩:=guard_room (a.headerEnd b) H (2^c) M r n D floor past room p
  have old:=source_column B floor fit (a.preparedImage b space m) _ capacity
    (a.prepared_root_words b space m p values held packed read positive)
  intro j
  exact (eval_below (.lookup B .row) _ _ later ⟨fit,trivial⟩ frame).trans (old j)
end Receipt
end
end Hierarchy.DescentPrimitiveBirth

end OAI
