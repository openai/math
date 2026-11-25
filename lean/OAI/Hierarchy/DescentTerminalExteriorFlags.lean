import OAI.Hierarchy.DescentExteriorUniversal

namespace OAI
/-! # The chronological exterior failure word and its complete decoding law -/
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure

theorem exec_cheap_seq {w a b : ℕ} {P Q : Procedure w} {x y z : Memory w}
    (left : P.Exec x y a ∧ CheapCode P) (right : Q.Exec y z b ∧ CheapCode Q) :
    (P.seq Q).Exec x z (a+b) ∧ CheapCode (P.seq Q) := by
  obtain ⟨runP,cheapP⟩:=left
  obtain ⟨runQ,cheapQ⟩:=right
  exact ⟨@Procedure.Exec.then w P Q x y z a b (@runP) (@runQ),
    @cheap_seq w P Q (@cheapP) (@cheapQ)⟩

end Hierarchy.ProtocolRAM

namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w e j r t : ℕ}
local notation "N" => e*2^(j+r)
local notation "k" => j+(j+r)
local notation "H" => span j r t e

def flagBank (origin : ℕ) : Bank := ⟨start j r t e origin,exponent j r t e+1⟩
def flagOut (origin : ℕ) := origin+21*H
def flagged (w e j r t origin : ℕ) : Procedure w :=
  (service w j r t e origin).seq (SumScores.procedure w (flagOut (j:=j) (r:=r) (t:=t) (e:=e) origin)
    (2*(e*2^(j+r))) 1 (DescentExteriorRejectWord.indicator (flagBank (j:=j) (r:=r) (t:=t) (e:=e) origin)))
def flaggedMem (origin : ℕ) (m : Memory w) :=
  DescentExteriorRejectWord.destination N (flagBank (j:=j) (r:=r) (t:=t) (e:=e) origin)
    (flagOut (j:=j) (r:=r) (t:=t) (e:=e) origin) (serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin m)
def flagAt (origin : ℕ) := flagOut (j:=j) (r:=r) (t:=t) (e:=e) origin+2*N

attribute [local irreducible] Procedure.Exec CheapCode

theorem flagged_exec (origin : ℕ) (m : Memory w) (space : origin+24*H<2^w) :
    (flagged w e j r t origin).Exec m (flaggedMem (j:=j) (r:=r) (t:=t) (e:=e) origin m) (84+492*N) ∧
    CheapCode (flagged w e j r t origin) := by
  have hp : 0<H:=Nat.two_pow_pos _
  have nRoom : N≤H := row_room j r t e
  have cap : (flagBank (j:=j) (r:=r) (t:=t) (e:=e) origin).size=2*H := by
    simp [flagBank,Bank.size,span,pow_succ,Nat.mul_comm]
  have fit : (flagBank (j:=j) (r:=r) (t:=t) (e:=e) origin).Fits w (flagOut (j:=j) (r:=r) (t:=t) (e:=e) origin) := by
    unfold Bank.Fits
    rw [cap]
    change 0 < 2*H ∧ 2*H < 2^w ∧ origin+18*H+2*H ≤ origin+21*H
    omega
  have a:=run_unconditional (j:=j) (r:=r) (t:=t) (e:=e) origin (by omega) m
  have b:=DescentExteriorRejectWord.run_unconditional (n:=N) (flagBank (j:=j) (r:=r) (t:=t) (e:=e) origin)
    (flagOut (j:=j) (r:=r) (t:=t) (e:=e) origin) fit (by rw [cap];omega) (by dsimp [flagOut];omega)
    (serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin m)
  unfold flagged flaggedMem
  rw [←show 16+364*N+(4+(2*N+1)*64)=84+492*N by omega]
  exact exec_cheap_seq a b

theorem flag_canonical (origin : ℕ) (pos : 0<w) (payload : 2^j*t≤w) (space : origin+24*H<2^w)
    (M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) (m : Memory w)
    (init : Loaded origin M x z m) :
    flaggedMem (j:=j) (r:=r) (t:=t) (e:=e) origin m (flagAt (j:=j) (r:=r) (t:=t) (e:=e) origin)=0 ↔
    z=canonical M x := by
  have hp : 0<H:=Nat.two_pow_pos _
  have good:=(machine_trace origin pos payload (by omega) M x z m 0 0 init).2.2
  have one : (1:Word w)≠0 := by
    have o : 1<2^w:=by omega
    intro he;have hv:=congrArg Fin.val he;simp [Nat.mod_eq_of_lt o] at hv
  rw [flaggedMem,flagAt,DescentExteriorRejectWord.read_flag]
  change (if ∀s:Fin 2,∀i:Fin N,serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin m
    (start j r t e origin+s.val*N+i.val)=0 then (0:Word w) else 1)=0 ↔ _
  by_cases valid : z=canonical M x
  · rw [ite_eq_left (good.1.mpr valid)]
    simp [valid]
  · rw [ite_eq_right (fun flags=>valid (good.1.mp flags))]
    simp [one,valid]

theorem preserves_flights (origin : ℕ) (m : Memory w) (phase : Fin 3) (i : Fin N) :
    flaggedMem (j:=j) (r:=r) (t:=t) (e:=e) origin m (start j r t e origin+phase.val*N+i.val)=
      serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin m (start j r t e origin+phase.val*N+i.val) := by
  apply DescentExteriorRejectWord.before
  have a:=Nat.mul_le_mul_right N (show phase.val+1≤3 by omega)
  rw [Nat.succ_mul] at a
  have cap : N≤H := row_room j r t e
  dsimp [flagOut,start]
  omega

/-- The earlier finite seed-and-epoch program may reject any assignment. Only
its successful states need a correct selected matrix. -/
theorem both_flags {A T : Type} (origin : ℕ) (pos : 0<w) (payload : 2^j*t≤w) (space : origin+24*H<2^w)
    (record : Fin e→Plane j r→Fin t→Bool) (layouts : T→Fin e→Layout k) (decode : (A→Bool)→Option T)
    (z : A⊕Hidden e j r t→Bool) (m : Memory w) (seedFlag : Word w)
    (prior : seedFlag=0 ↔ ∃t,decode (z∘Sum.inl)=some t)
    (loaded : ∀t,decode (z∘Sum.inl)=some t→Loaded origin (layouts t) record (z∘Sum.inr) m) :
    (seedFlag=0 ∧ flaggedMem (j:=j) (r:=r) (t:=t) (e:=e) origin m (flagAt (j:=j) (r:=r) (t:=t) (e:=e) origin)=0) ↔
    ∃t,proposed decode layouts record z=some t := by
  constructor
  · rintro ⟨ok,exc⟩
    obtain ⟨t,known⟩:=prior.1 ok
    exact ⟨t,(proposed_eq ..).2 ⟨known,(flag_canonical origin pos payload space (layouts t) record _
      m (loaded t known)).1 exc⟩⟩
  · rintro ⟨t,known⟩
    obtain ⟨old,new⟩:=(proposed_eq ..).1 known
    exact ⟨prior.2 ⟨t,old⟩,(flag_canonical origin pos payload space (layouts t) record _ m (loaded t old)).2 new⟩

end
end Hierarchy.DescentExteriorShelf

end OAI
