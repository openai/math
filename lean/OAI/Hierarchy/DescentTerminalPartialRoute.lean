import OAI.Hierarchy.DescentTerminalEpochChart

namespace OAI
/-! # Total reference histories for arbitrary raw profile prefixes -/
namespace Hierarchy.DescentTerminalEpochChart
open DescentTerminalEpochBits DescentSixParty
open scoped Classical
noncomputable section
variable {S Z U : Type} {bits : Z→S→Bool} {ok : (S→Bool)→Prop} {source : U→Z}

def Chart.counts (b : Chart bits ok source) (z : b.Pin→Bool) := (b.rows z).map Observation.count

/-- The fallback changes only the interpretation of damaged data. Through the
first bad profile the actual decoder sees a prefix of those same physical counts. -/
structure Route (b : Chart bits ok source) where
  follow : (b.Pin→Bool)→U
  stored : ∀t,follow (b.store t)=t
  «prefix» : ∀z,List.IsPrefix (b.counts z) (b.counts (b.store (follow z)))

variable (b : Chart bits ok source) {C n : ℕ} {I Fiber : U→Type} (count : U→ℕ)
    (number : ∀u,I u≃Fin (count u)) (room : ∀u,count u ≤ n)
    (profile : ∀u,Fiber u≃(I u→Profile C))
local notation "next" => extend b count number room profile

theorem extend_stored_counts (t : Σu,Fiber u) :
    (next).counts ((next).store t)=b.counts (b.store t.1)++[count t.1] := by
  have l : left b (extendedStore (seats:=n) b count number profile t)=b.store t.1 := rfl
  have hit := (b.read_iff _ _).mpr (rfl : b.store t.1=b.store t.1)
  change (extendedRows b count (extendedStore b count number profile t)).map Observation.count=_
  simp only [extendedRows,l,hit,List.map_append,List.map_cons,List.map_nil,Chart.counts]

def reference (p : Route b) (z : b.Pin⊕Pins C n→Bool) : Σu,Fiber u :=
  let u:=p.follow (left b z)
  let fields:=DescentTerminalEpochBits.read (number u) (room u) (right b z)
  ⟨u,(profile u).symm (fields.getD (fun _=>⟨fun _=>0,by simp⟩))⟩

def Route.extend (p : Route b) : Route next where
  follow := reference b count number room profile p
  stored t := by
    rcases t with ⟨u,v⟩
    let raw : Pins C n → Bool := DescentTerminalEpochBits.store (number u) (profile u v)
    let recover (x : U) : Σ a,Fiber a :=
      let fields := DescentTerminalEpochBits.read (number x) (room x) raw
      ⟨x,(profile x).symm (fields.getD (fun _=>⟨fun _=>0,by simp⟩))⟩
    have fields := (DescentTerminalEpochBits.read_iff (number u) (room u)
      raw (profile u v)).mpr rfl
    change recover (p.follow (b.store u))=⟨u,v⟩
    rw [p.stored]
    simp only [recover,fields,Option.getD_some,Equiv.symm_apply_apply]
  «prefix» z := by
    rw [extend_stored_counts]
    change List.IsPrefix ((extendedRows b count z).map Observation.count)
      (b.counts (b.store (p.follow (left b z)))++[count (p.follow (left b z))])
    have counts : (extendedRows (C:=C) (seats:=n) b count z).map Observation.count =
        b.counts (left b z) ++ (match b.read (left b z) with
          | none => []
          | some u => [count u]) := by
      delta extendedRows Chart.counts
      rw [List.map_append]
      cases b.read (left b z) <;> rfl
    rw [counts]
    cases h : b.read (left b z) with
    | none=>
      obtain ⟨tail,eqn⟩:=p.prefix (left b z)
      refine ⟨tail++[count (p.follow (left b z))],?_⟩
      simpa only [List.append_nil,List.append_assoc] using
        congrArg (·++[count (p.follow (left b z))]) eqn
    | some u=>
      have same := (b.read_iff _ _).mp h
      exact ⟨[],by simp only [List.append_nil,same,p.stored]⟩


end
end Hierarchy.DescentTerminalEpochChart

end OAI
