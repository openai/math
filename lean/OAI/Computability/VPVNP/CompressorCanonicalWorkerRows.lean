import OAI.Computability.VPVNP.CompressorSelectedTermWorker

/-!
# A fixed dense representation of the demand rows of a semantic pass

The representation uses the exact demand vector of every motif of the
shrinking or refresh pass. The native verifier on this memory has the same
successful tapes as on any physical level directory representing those
vectors, including on an empty set of demand coordinates.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.CanonicalWorker

open BurstRAM Compression SelectedTerms PairSimulation.LocalHistory
open scoped Fin.CommRing

variable {m d n w : ℕ} {D : Type} (order : Fin d ≃ D) (demand : Fin m → D → ℕ)

/-- Row-major initial memory for the demand scan, storing motif demands in the specified
coordinate order and zero outside the table. -/
def memory (w : ℕ) : Memory w := fun x =>
  if h : x/d < m ∧ x%d < d then Fin.ofNat _ (demand ⟨x/d,h.1⟩ (order ⟨x%d,h.2⟩)) else 0

theorem cell (i : Fin m) (j : Fin d) :
    memory order demand w (i.val*d+j.val) = Fin.ofNat _ (demand i (order j)) := by
  have div : (i.val*d+j.val)/d = i.val := by
    rw [Nat.mul_comm i.val d,Nat.mul_add_div (by have := j.isLt; omega),Nat.div_eq_of_lt j.isLt,Nat.add_zero]
  have mod : (i.val*d+j.val)%d = j.val := Nat.mul_add_mod_of_lt j.isLt
  simp [memory,div,mod,i.isLt,j.isLt]

/-- Disjoint strided demand and term tables, with the first term record immediately after the
final demand row. -/
def layout (space : m*d+m*(2+n) < 2^w) : TermRecordScan.Layout m d n w :=
  TermRecordScan.strided m d n w 0 (m*d) d (2+n) le_rfl le_rfl (Nat.zero_add _).le space

theorem inputs (space : m*d+m*(2+n) < 2^w) (values : ∀ i e, demand i e < 2^w) :
    TermRecordScan.Inputs order (layout space) demand (memory order demand w) := by
  intro i
  funext e
  obtain ⟨j,rfl⟩ := order.surjective e
  rw [DemandPreparation.demandAt_address order _ _ ((layout space).sourceFits i) j]
  have hmul := Nat.mul_le_mul_right d i.isLt.le
  have addr : ((layout space).source i).val = i.val*d := by
    change (0+i.val*d) % 2^w = _
    rw [Nat.zero_add,Nat.mod_eq_of_lt (by omega)]
  rw [addr,cell]
  exact Nat.mod_eq_of_lt (values i (order j))

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {A : Type*} [CommRing A] {f : B.Entry → A} {hf : B.IsSolution f}
variable {a g b l : ℕ} {X : State a g} {p : StatePass A X b l} (o : PassOrigin B f hf p)
local notation "G" => grid o

/-- The fixed dense encoding runs the real native term program and uses
its uniform clock. It only depends on the old graph and the pass origin. -/
def input (w : ℕ) (space : o.motifCount*(G).d+o.motifCount*(2+(G).e) < 2^w)
    (width : SelectedTermWorker.fitConstant B+4*Nat.clog 2 (X.maxWireWidth+1) ≤ w)
    (values : X.maxWireWidth < 2^w) : WorkerInput o w :=
  let L := layout space
  let order := (G).demandOrder.entries
  let demand := (termRows o).demand
  SelectedTermWorker.input o width L ![0,((G).d : ℕ),(o.motifCount*(G).d : ℕ),(2+(G).e : ℕ)]
    (TermWorker.addresses_strided 0 (o.motifCount*(G).d) (G).d (2+(G).e) le_rfl le_rfl (Nat.zero_add _).le space)
    (memory order demand w) (inputs order demand space fun i e => ((termRows o).bounded i e).trans_lt values)

theorem accepts_iff (I J : WorkerInput o w) (bs : Fin o.motifCount → List Bool) :
    (I.run bs).isSome ↔ (J.run bs).isSome := by
  have transport (P Q : WorkerInput o w) (h : (P.run bs).isSome) : (Q.run bs).isSome := by
    let x : P.Accepted := ⟨bs,h⟩
    let v := P.termEquiv.symm x
    have eqn : workerTapes o w v = bs := congrArg Subtype.val (P.termEquiv.apply_symm_apply x)
    have yes := (Q.termEquiv v).property
    rw [WorkerInput.termEquiv_tapes,eqn] at yes
    exact yes
  exact ⟨transport I J,transport J I⟩

end CompressorRecords.CanonicalWorker

end

end VPVNP
end Computability
end OAI
