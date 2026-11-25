import OAI.Hierarchy.DescentTerminalScatterChip

namespace OAI
/-! # Fixed footprint of writes to the endpoint chip columns on every selector -/
namespace Hierarchy.DescentTerminalScatterChip
open DescentTerminalHeaderScatter Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w n pool : ℕ}
def put (L : Layout) (bank : Bank) (sink : ℕ) := bounded bank (dest L bank.base sink)
def boundedProgram (L : Layout) (bank : Bank) (bits src n pool sink offset blank : ℕ) :=
  (scan bits bank.base pool (.lit blank)).seq (DescentTerminalHeaderScatter.program bits src n
    (put L bank sink) (datum L offset) L.lane)
def boundedCost (L : Layout) (bank : Bank) (n pool sink offset : ℕ) :=
  (4+pool*(2*Expr.work (.lit 0)+4))+DescentTerminalHeaderScatter.cost n (put L bank sink) (datum L offset) L.lane
def heap (L : Layout) (bank : Bank) (src n pool sink offset blank : ℕ) (m : Memory w) :=
  imageAt src n (put L bank sink) (datum L offset) L.lane (image bank.base pool (.lit blank) m)

section Execution

attribute [local irreducible] Procedure.Exec CheapCode

private theorem bounded_steps (L : Layout) (bank : Bank) (src n pool sink offset blank : ℕ)
    (m clear final : Memory w)
    (wipe : (scan w bank.base pool (.lit blank)).Exec m clear (4+pool*(2*Expr.work (.lit blank)+4)))
    (write : (DescentTerminalHeaderScatter.program w src n (put L bank sink) (datum L offset) L.lane).Exec
      clear final (DescentTerminalHeaderScatter.cost n (put L bank sink) (datum L offset) L.lane))
    (good : CheapCode (DescentTerminalHeaderScatter.program w src n (put L bank sink) (datum L offset) L.lane)) :
    (boundedProgram L bank w src n pool sink offset blank).Exec m final (boundedCost L bank n pool sink offset) ∧
      CheapCode (boundedProgram L bank w src n pool sink offset blank) := by
  let A:=scan w bank.base pool (.lit blank)
  let B:=DescentTerminalHeaderScatter.program w src n (put L bank sink) (datum L offset) L.lane
  exact ⟨@Procedure.Exec.then w A B m clear final (4+pool*(2*Expr.work (.lit blank)+4))
    (DescentTerminalHeaderScatter.cost n (put L bank sink) (datum L offset) L.lane) (@wipe) (@write),
    @cheap_seq w A B (@scan_cheap w bank.base pool (.lit blank)) (@good)⟩

theorem any (L : Layout) (bank : Bank) (src n pool sink offset blank : ℕ) (m : Memory w)
    (fit : bank.Fits w src) (laneLow : L.lane.Fits w bank.base)
    (ready : (stage (put L bank sink) (datum L offset) L.lane).Fits w src) (allocation : pool≤bank.size)
    (room : src+2*n<2^w) (pos : 0<w)
    (lane : ∀(i : Fin n) (j:Fin 2),L.lane.read m ((field i j).val:Word w)=(j.val:Word w)) :
    (boundedProgram L bank w src n pool sink offset blank).Exec m (heap L bank src n pool sink offset blank m)
      (boundedCost L bank n pool sink offset) ∧ CheapCode (boundedProgram L bank w src n pool sink offset blank) := by
  let clear:=image bank.base pool (.lit blank) m
  have first:=@scan_exec w bank.base pool (.lit blank) m trivial (by have:=fit.2.2;omega)
  have lane_readback (i : Fin n) (j : Fin 2) :
      L.lane.read clear ((field i j).val:Word w)=(j.val:Word w) := by
    let x : Word w := (field i j).val
    have early : L.lane.base+x.val%L.lane.size<bank.base :=
      (Nat.add_lt_add_left (Nat.mod_lt x.val laneLow.1) L.lane.base).trans_le laneLow.2.2
    exact (DescentTerminalChipRuntime.image_low m bank.base pool (.lit blank) early).trans (lane i j)
  obtain ⟨replay,good⟩:=exec_any bank L.lane (dest L bank.base sink) (datum L offset) clear src pos fit ready room lane_readback
  exact bounded_steps L bank src n pool sink offset blank m clear (heap L bank src n pool sink offset blank m)
    (@first) (@replay) (@good)

end Execution

theorem before (L : Layout) (bank : Bank) (src n pool sink offset blank : ℕ) (m : Memory w)
    (fit : bank.Fits w src) (room : src<2^w) {j : ℕ} (prior : j<bank.base) :
    heap L bank src n pool sink offset blank m j=m j := by
  let clear:=image bank.base pool (.lit blank) m
  let before:=image src (2*n) (stage (put L bank sink) (datum L offset) L.lane) clear
  let events:=actual (n:=n) (put L bank sink) (datum L offset) clear
  have off (i : Fin n) : (events i).1.val≠j := by
    change ((bounded bank (dest L bank.base sink)).eval _ _).val≠j
    rw [bounded_val bank _ _ _ fit room]
    omega
  change after before (EffectStream.events (List.ofFn events)) j=m j
  apply published
  · intro i h;exact (off i h).elim
  · left
    have early : j<src:=by have:=fit.2.2;omega
    simp [before,clear,image,fillSegment,not_le.mpr prior,not_le.mpr early]

variable {A : Type} (issued : Fin n→Option A) (atRow : A ↪ Fin pool)
    (key site pre start localR : A→ℕ) (onPublic : A→Bool) (ans : A→Word w)
theorem truth (L : Layout) (bank : Bank) (m : Memory w) (src sink offset blank : ℕ) (pos : 0<w)
    (r : Ranks issued key site pre start localR onPublic L m) (data : Columns atRow site pre start localR onPublic ans L m offset)
    (cover : ∀a,∃i,issued i=some a) (fit : bank.Fits w src)
    (padding : pool ≤ sink-bank.base) (within : sink-bank.base<bank.size) (starts : bank.base≤ sink)
    (low : (stage (dest L bank.base sink) (datum L offset) L.lane).Fits w bank.base)
    (room : src+2*n<2^w) :
    ∀i : Fin pool,heap L bank src n pool sink offset blank m (bank.base+i.val)=
      Function.extend atRow ans (fun _=>(blank:Word w)) i := by
  let clear:=image bank.base pool (.lit blank) m
  let addr:=dest L bank.base sink
  let high:=datum L offset
  let guarded:=stage (put L bank sink) high L.lane
  let before:=image src (2*n) guarded clear
  have last:=fit.2.2
  have ready (a : ℕ) (h:a<bank.base) : clear a=m a:=by simp [clear,image,fillSegment,not_le.mpr h]
  have props (i : Fin n) (j : Fin 2) : (stage addr high L.lane).eval clear ((field i j).val:Word w)=
      if j=0 then (record issued atRow ans bank.base sink i).1 else (record issued atRow ans bank.base sink i).2 :=
    (eval_below _ _ m clear low (fun a h=>ready a h)).trans
      (record_read issued atRow key site pre start localR onPublic ans L m bank.base sink offset pos r data i j)
  have lane (i : Fin n) (j : Fin 2) : L.lane.read clear ((field i j).val:Word w)=(j.val:Word w) := by
    rw [←r.lane i j]
    apply ready
    have lf : L.lane.Fits w bank.base:=low.1.1
    have:=lf.2.2;have:=Nat.mod_lt ((field i j).val:Word w).val lf.1
    omega
  have equal : actual (n:=n) (put L bank sink) high clear=record issued atRow ans bank.base sink := by
    funext i
    have a:=props i 0
    have v:=props i 1
    rw [lane_read _ _ _ _ _ _ pos (lane i 0)] at a
    rw [lane_read _ _ _ _ _ _ pos (lane i 1)] at v
    simp only [ite_eq_right (by decide : (1:Fin 2)≠0)] at a v
    apply Prod.ext
    · cases h : issued i with
      | none=>
        have value : addr.eval clear ((field i 0).val:Word w)=((bank.base+(sink-bank.base):ℕ):Word w):=by simpa [record,h,Nat.add_sub_of_le starts] using a
        exact (bounded_exact bank addr clear _ fit (by omega) within value).trans a
      | some z=>
        have value : addr.eval clear ((field i 0).val:Word w)=((bank.base+(atRow z).val:ℕ):Word w):=by simpa [record,h] using a
        exact (bounded_exact bank addr clear _ fit (by omega) ((atRow z).isLt.trans_le (by omega)) value).trans a
    · exact v
  have address (k : Fin n) (a : A) (assigned : issued k=some a) :
      (record issued atRow ans bank.base sink k).1.val=bank.base+(atRow a).val := by
    have small : bank.base+(atRow a).val<2^w := by have := (atRow a).isLt; omega
    simpa only [record,assigned] using (Fin.val_cast_of_lt small)
  intro i
  change after before (EffectStream.events (List.ofFn (actual (put L bank sink) high clear))) (bank.base+i.val)=_
  rw [equal]
  apply published
  · intro k hit
    cases e:issued k with
    | none=>simp [record,e,Fin.val_cast_of_lt (show sink<2^w by omega)] at hit;have:=i.isLt;omega
    | some z=>
      have eq : atRow z=i := Fin.ext (Nat.add_left_cancel ((address k z e).symm.trans hit))
      rw [←eq,atRow.injective.extend_apply]
      simp [record,e]
  · by_cases h:∃a,atRow a=i
    · obtain ⟨a,rfl⟩:=h
      obtain ⟨j,hj⟩:=cover a
      exact Or.inr ⟨j,address j a hj⟩
    · apply Or.inl
      have early : bank.base+i.val<src:=by have:=i.isLt;omega
      simp [before,clear,image,fillSegment,not_le.mpr early,show bank.base+i.val<bank.base+pool by omega,
        Expr.eval,Function.extend,h]

end
end Hierarchy.DescentTerminalScatterChip

end OAI
