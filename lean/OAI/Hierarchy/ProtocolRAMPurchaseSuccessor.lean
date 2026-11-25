import OAI.Hierarchy.ProbeStagePorts

namespace OAI
/-! # The unique actual tile at a sampler-selected input socket -/

namespace Hierarchy.ProtocolRAMPurchaseOwners
open ProbeStage
variable {n m groups : ℕ} {G : Type*}

/-- Logical socket ordinal in the fixed group-major table. -/
def socket (g : Fin groups) (i : Fin m) := (finProdFinEquiv (g,i)).val

theorem socket_eq (g : Fin groups) (i : Fin m) : socket g i = g.val*m+i.val := by
  change i.val+m*g.val=g.val*m+i.val
  ac_rfl

theorem socket_lt (g : Fin groups) (i : Fin m) : socket g i < groups*m :=
  (finProdFinEquiv (g,i)).isLt

theorem socket_inj {g h : Fin groups} {i j : Fin m} (e : socket g i=socket h j) :
    g=h ∧ i=j := Prod.mk.inj (finProdFinEquiv.injective (Fin.ext e))

/-- A missing socket or sampler lane is encoded by zero. -/
def portCode {k : ℕ} : Option (Fin k) → ℕ
  | none => 0
  | some i => i.val+1

noncomputable def owner? (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (g : Fin groups) (i : Fin m) : Option (Fin n) := by
  classical
  exact if h : ∃ r, encode (p.group r)=g ∧ p.input r=i then some h.choose else none

theorem owner_some_iff (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (g : Fin groups) (i : Fin m) (r : Fin n) :
    owner? p encode g i=some r ↔ encode (p.group r)=g ∧ p.input r=i := by
  classical
  unfold owner?
  split
  next h =>
    rw [Option.some.injEq]
    constructor
    · rintro rfl
      exact h.choose_spec
    · intro hr
      exact p.input_inj (Prod.ext (encode.injective (h.choose_spec.1.trans hr.1.symm))
        (h.choose_spec.2.trans hr.2.symm))
  next h =>
    simp only [reduceCtorEq,false_iff]
    exact fun hr => h ⟨r,hr⟩

noncomputable def ownerValue (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (g : Fin groups) (i : Fin m) := portCode (owner? p encode g i)

noncomputable def successor {D : ℕ} (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (r : Fin n) (j : Fin D) : Option (Fin n) :=
  (sampler (p.output r) j).bind (owner? p encode (encode (p.group r)))

theorem successor_eq_some_iff {D : ℕ} (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (sampler : Fin m → Fin D → Option (Fin m)) (r v : Fin n) (j : Fin D) :
    successor p encode sampler r j=some v ↔
      p.group v=p.group r ∧ sampler (p.output r) j=some (p.input v) := by
  unfold successor
  cases h : sampler (p.output r) j with
  | none => simp
  | some i =>
    change owner? p encode (encode (p.group r)) i=some v ↔ _
    rw [owner_some_iff]
    simp [eq_comm (a := i)]

noncomputable def nextRow (p : Tiles (Fin n) G m) (encode : G ↪ Fin groups)
    (select : Fin m → Option (Fin m)) (r : Fin n) :=
  portCode ((select (p.output r)).bind (owner? p encode (encode (p.group r))))

end Hierarchy.ProtocolRAMPurchaseOwners

end OAI
