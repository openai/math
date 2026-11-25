import OAI.ThreeFlat.Diagonal.TracePhysicalAddress

namespace OAI
/-! # Row-local ports for the ordinary trace and the replicated program text -/

namespace ThreeFlat.Diagonal.TraceUniformRow

variable {w p r k f S d : ℕ}

/-- A row reads its ordinary local operands and the local and succeeding text copies. -/
abbrev Port (w p r k d : ℕ) := TracePhysical.Port w r d ⊕ (Bool × (Fin (1+6*p+k) × Fin w))

abbrev CopyCount (w p k d : ℕ) := 2^d*((1+6*p+k)*w)
abbrev SharedCount (w p r k d f : ℕ) := Fintype.card (TracePhysical.Shared w r f d) + CopyCount w p k d

def copyOrdinal (v : Fin (2^d)) (j : (Fin (1+6*p+k) × Fin w)) : Fin (CopyCount w p k d) :=
  finProdFinEquiv (v,finProdFinEquiv j)

def keepSource {n e q : ℕ} : BitSource n q → BitSource (n+e) q
  | .hidden i => .hidden (i.castAdd e)
  | .pin j => .pin j
  | .constant v => .constant v

@[simp] theorem keepSource_at {n e q : ℕ} (z : BitSource n q) (h : Fin n → Bool)
    (c : Fin e → Bool) (pin : Fin q → Bool) :
    (keepSource z).read (Fin.append h c) pin = z.read h pin := by
  cases z <;> simp [keepSource,BitSource.read]

def addresses (hw : 2 ≤ w+1) (S f : ℕ) (v : Fin (2^d)) :
    Port w p r k d → BitSource (SharedCount w p r k d f) (S*w)
  | .inl a => keepSource (TracePhysical.address hw S f v a)
  | .inr (b,j) =>
    let send (u : Fin (2^d)) := BitSource.hidden (Fin.natAdd (Fintype.card (TracePhysical.Shared w r f d)) (copyOrdinal u j))
    if b then if h : v.val+1<2^d then send ⟨_,h⟩ else .constant false else send v

end ThreeFlat.Diagonal.TraceUniformRow

end OAI
