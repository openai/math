import OAI.Hierarchy.DescentSignedCoverage

namespace OAI
/-! # Normalized-parent windows at both genuine signed receiver roles -/
namespace Hierarchy.DescentNextSignedWindow.Roster
open DescentSharedCableNames DescentParallelBase DescentSixParty DescentColonies
open scoped Classical
noncomputable section
variable {F P V J E : Type} [Field F] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] [Fintype E]
  {d k i c : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
  (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ)
variable (C : Blocks (DescentSharedCableNames.Stage.source A native) E) (h : DescentSharedCableNames.Stage.Host J V k)

abbrev Face := {u:E×Bool // 0<C.count u.1 ∧ (if u.2 then C.dst u.1 else C.src u.1)=h}

def resident (f : Face A native C h) : Local C h := ⟨f.val.1,f.property.1,by
  have valid:=f.property.2;cases val:f.val.2 <;> simp [val] at valid <;> tauto⟩

def addr (where_ : Local C h↪Fin c) : Face A native C h↪Fin (2*c) where
  toFun f:=finProdFinEquiv ((if f.val.2 then 1 else 0:Fin 2),where_ (resident A native C h f))
  inj' :=by
    intro a b eqn;have e:=finProdFinEquiv.injective eqn
    apply Subtype.ext;apply Prod.ext
    · exact congrArg Subtype.val (where_.injective (congrArg Prod.snd e))
    · have d:=congrArg Prod.fst e;cases aa:a.val.2 <;> cases bb:b.val.2 <;> simp [aa,bb] at d ⊢

variable (where_ : Local C h↪Fin c) (info : Face A native C h→Record A.degree A.cap)
local notation "slot" => addr A native C h where_

def rows (j:Fin (2*c)) : Option (Record A.degree A.cap):=if has:∃f,slot f=j then some (info has.choose) else none

@[simp] theorem mounted (f:Face A native C h): rows A native C h where_ info (slot f)=some (info f):=by
  have has:∃e,slot e=slot f:=⟨f,rfl⟩
  simp only [rows,dite_eq_left has,(slot).injective has.choose_spec]

local notation "row" => rows A native C h where_ info

/-- No row uniqueness/coverage assumption is needed: separate signs use
the physical resident's own short slot, including both signs of a loop. -/
def physical (weight:∀f,(info f).count=C.count f.val.1) : GrainPorts.Unit A native C h≃Occupied A row :=by
  let build (t:GrainPorts.Unit A native C h) : Face A native C h:=⟨(t.val.1.1,t.val.2),Nat.zero_lt_of_lt t.val.1.2.isLt,t.property⟩
  let put (t:GrainPorts.Unit A native C h) : Occupied A row:=⟨(slot (build t),t.val.1.2.val),info (build t),mounted A native C h where_ info _,by rw [weight];exact t.val.1.2.isLt⟩
  apply Equiv.ofBijective put
  constructor
  · intro a b eqn
    have key :=(slot).injective (congrArg (fun p : Occupied A row=>p.val.1) eqn)
    have f: a.val.1.1=b.val.1.1:=congrArg (fun p : Face A native C h=>p.val.1) key
    have side:a.val.2=b.val.2:=congrArg (fun p : Face A native C h=>p.val.2) key
    have off:a.val.1.2.val=b.val.1.2.val:=congrArg (fun p : Occupied A row=>p.val.2) eqn
    apply Subtype.ext;apply Prod.ext _ side;apply Sigma.ext f;exact (Fin.heq_ext_iff (congrArg C.count f)).mpr off
  · intro z
    obtain ⟨r,here,small⟩:=z.property
    unfold rows at here
    split at here
    next has=>
      let f:=has.choose
      have actual:info f=r:=Option.some.inj here
      have bound:z.val.2<C.count f.val.1:=by rw [←weight f,actual];exact small
      let t:GrainPorts.Unit A native C h:=⟨(⟨f.val.1,⟨z.val.2,bound⟩⟩,f.val.2),f.property.2⟩
      refine ⟨t,Subtype.ext (Prod.ext ?_ rfl)⟩;exact has.choose_spec
    next absent=>contradiction

def face (t:GrainPorts.Unit A native C h):Face A native C h:=⟨(t.val.1.1,t.val.2),Nat.zero_lt_of_lt t.val.1.2.isLt,t.property⟩

theorem physical_at (weight:∀f,(info f).count=C.count f.val.1) (t:GrainPorts.Unit A native C h):
    (physical A native C h where_ info weight t).val=(slot (face A native C h t),t.val.1.2.val):=rfl

theorem physical_data (weight:∀f,(info f).count=C.count f.val.1) (t:GrainPorts.Unit A native C h):
    data A row (physical A native C h where_ info weight t)=info (face A native C h t):=by
  let u:=physical A native C h where_ info weight t
  exact Option.some.inj ((stored A row u).1.symm.trans (mounted A native C h where_ info (face A native C h t)))

end
end Hierarchy.DescentNextSignedWindow.Roster

end OAI
