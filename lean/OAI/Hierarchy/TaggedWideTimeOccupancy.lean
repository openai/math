import OAI.Hierarchy.TaggedWireCalendarPorts

namespace OAI
/-! # Exact allocated digits of every chronological state -/

noncomputable section
namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe CalendarTape
open scoped Classical

namespace NamedAperture
variable {S n : ℕ} {H : Type} (ends : Fin n → Chord S) (bits : Fin n→ℕ)
    (port : Fin n × Bool ↪ H) (cap : H→ℕ) (room : ∀i b,bits i ≤ cap (port (i,b)))

/-- The native sparse width array is zero on every absent socket. Its
comparison with a fixed local digit is exactly membership in the image
of the true, physically oriented incident row bits. -/
theorem range_read (width : H→ℕ) (live : ∀i b,width (port (i,b))=bits i)
    (empty : ∀p,p∉Set.range port → width p=0) (u : (p:H) × Fin (cap p)) :
    u∈Set.range (place ends bits port cap room) ↔ u.2.val<width u.1 := by
  constructor
  · rintro ⟨a,rfl⟩
    obtain ⟨⟨⟨i,j⟩,s⟩,rfl⟩ := (halfBits ends bits).surjective a
    rw [read,live]
    exact j.isLt
  · rcases u with ⟨p,d⟩
    intro active
    by_cases existsPort : p∈Set.range port
    · obtain ⟨⟨i,s⟩,rfl⟩ := existsPort
      rw [live] at active
      let j : Fin (bits i) := ⟨d.val,active⟩
      exact ⟨halfBits ends bits (⟨i,j⟩,s),read ends bits port cap room ⟨i,j⟩ s⟩
    · simp [empty p existsPort] at active
end NamedAperture

namespace CalendarTape
open ProtocolRAM.Calendar
variable {S : ℕ} {X Q : Type} (slot : Event → Slot X) (wire : X → Widths S)
    (cells : ∀x,(Σs,SiteBit (wire x) s) ↪ Q)

/-- State at each actual calendar boundary, including the final boundary
and the initial state of a zero-length calendar. -/
def boundaryState : ∀ es x,Path slot es x → Fin (es.length+1) → X
  | [],x,_,_=>x
  | e::es,x,j,i=>Fin.cases x (boundaryState es ((slot e).next x j.1) j.2) i

theorem timeline_range : ∀es x (j : Path slot es x) (t : Fin (es.length+1)) (q : Q),
    (t,q)∈Set.range (timeline slot wire cells es x j) ↔
      q∈Set.range (cells (boundaryState slot es x j t))
  | [],x,j,t,q=>by
    have isZero : t=0 := by
      apply Fin.ext
      have bounded : t.val < 1 := t.isLt
      change t.val=0
      omega
    subst t
    constructor
    · rintro ⟨⟨s,b|b⟩,eqn⟩
      · exact ⟨⟨s,b⟩,congrArg Prod.snd eqn⟩
      · exact nomatch b
    · rintro ⟨⟨s,b⟩,rfl⟩
      exact ⟨⟨s,.inl b⟩,rfl⟩
  | e::es,x,j,t,q=>by
    refine Fin.cases ?_ (fun k=>?_) t
    · constructor
      · rintro ⟨⟨s,b|b⟩,eqn⟩
        · exact ⟨⟨s,b⟩,congrArg Prod.snd eqn⟩
        · rw [timeline_tail] at eqn
          exact (Fin.succ_ne_zero _ (congrArg Prod.fst eqn)).elim
      · rintro ⟨⟨s,b⟩,rfl⟩
        exact ⟨⟨s,.inl b⟩,rfl⟩
    · change _ ↔ q∈Set.range (cells (boundaryState slot es ((slot e).next x j.1) j.2 k))
      rw [←timeline_range es ((slot e).next x j.1) j.2 k q]
      constructor
      · rintro ⟨⟨s,b|b⟩,eqn⟩
        · exact (Fin.succ_ne_zero k (congrArg Prod.fst eqn).symm).elim
        · have lifted := (timeline_tail slot wire cells e es x j s b).symm.trans eqn
          obtain ⟨ht,hq⟩ := Prod.mk.inj lifted
          exact ⟨⟨s,b⟩,Prod.ext (Fin.succ_inj.mp ht) hq⟩
      · rintro ⟨⟨s,b⟩,eqn⟩
        exact ⟨⟨s,.inr b⟩,(timeline_tail slot wire cells e es x j s b).trans
          (congrArg (fun z : Fin (es.length+1) × Q => (z.1.succ,z.2)) eqn)⟩

def timeOrder [Fintype Q] (es : List Event) :
    (Fin (es.length+1) × Q) ≃ Fin ((es.length+1)*Fintype.card Q) :=
  ((Equiv.refl _).prodCongr (Fintype.equivFin Q)).trans finProdFinEquiv

theorem timelineFin_range [Fintype Q] (es : List Event) (x : X) (j : Path slot es x)
    (i : Fin ((es.length+1)*Fintype.card Q)) :
    let v := (timeOrder (Q:=Q) es).symm i
    i∈Set.range (timelineFin slot wire cells es x j) ↔ v.2∈Set.range (cells (boundaryState slot es x j v.1)) := by
  intro v
  rw [←timeline_range slot wire cells]
  constructor
  · rintro ⟨a,eqn⟩
    refine ⟨a,?_⟩
    exact (timeOrder es).injective ((show timeOrder es (timeline slot wire cells es x j a)=i from eqn).trans
      ((timeOrder es).apply_symm_apply i).symm)
  · rintro ⟨a,eqn⟩
    exact ⟨a,(congrArg (timeOrder es) eqn).trans ((timeOrder es).apply_symm_apply i)⟩

end CalendarTape
end Hierarchy.WireTelescope

end
end OAI
