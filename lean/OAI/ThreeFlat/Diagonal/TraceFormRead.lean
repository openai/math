import OAI.ThreeFlat.Diagonal.HistoryPortBit
import OAI.ThreeFlat.Diagonal.TraceCircuitArray

namespace OAI
/-! # Reading equal-width outgoing and incoming half-ports in physical order -/

namespace ThreeFlat.Diagonal.HistoryContraction.PortLayout
open scoped BigOperators Classical

variable {S : Shape} {Pins : Type*} (L : PortLayout S Pins) (v : S.Site) {n t : ℕ}

theorem uniform_portBit {a : S.graph.Port v} (j : Fin (L.width a.1.1))
    (same : ∀ i, L.lengths v i=t) :
    (L.portBit v a j).val=((L.port v).symm a).val*t+j.val := by
  simp only [portBit,finSigmaFinEquiv_apply,same]
  simp; rfl

/-- Read the native outgoing half-bank and then the incoming half-bank. The
two evaluation hypotheses are local projections of one incident word. -/
theorem encode_banks (x : S.Half v) (send recv : Fin n→Fin t→Bool)
    (total : n*t+n*t=L.halfBits v)
    (atSend : ∀ (i : Fin n) (j : Fin t), ∃ a : S.graph.Port v, ∃ k : Fin (L.width a.1.1),
      (L.portBit v a k).val=i.val*t+j.val ∧ L.binary a.val.1 (x a) k=send i j)
    (atRecv : ∀ (i : Fin n) (j : Fin t), ∃ a : S.graph.Port v, ∃ k : Fin (L.width a.1.1),
      (L.portBit v a k).val=n*t+(i.val*t+j.val) ∧ L.binary a.val.1 (x a) k=recv i j) :
    (fun j => L.encode v x (Fin.cast total j)) =
      Fin.append (TraceCircuit.blocks _ _ send) (TraceCircuit.blocks _ _ recv) := by
  funext j
  refine Fin.addCases ?_ ?_ j
  · intro k
    obtain ⟨⟨u,b⟩,rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨a,c,idx,val⟩ := atSend u b
    rw [Fin.append_left,TraceCircuit.blocks_at,←val,←L.portBit_read v x]
    apply congrArg (L.encode v x)
    apply Fin.ext
    refine Eq.trans ?_ idx.symm
    change (finProdFinEquiv (u,b)).val=u.val*t+b.val
    simp [finProdFinEquiv]; ac_rfl
  · intro k
    obtain ⟨⟨u,b⟩,rfl⟩ := finProdFinEquiv.surjective k
    obtain ⟨a,c,idx,val⟩ := atRecv u b
    rw [Fin.append_right,TraceCircuit.blocks_at,←val,←L.portBit_read v x]
    apply congrArg (L.encode v x)
    apply Fin.ext
    refine Eq.trans ?_ idx.symm
    change n*t+(finProdFinEquiv (u,b)).val=n*t+(u.val*t+b.val)
    simp [finProdFinEquiv]; ac_rfl

end ThreeFlat.Diagonal.HistoryContraction.PortLayout

namespace ThreeFlat.Diagonal.HistoryContraction

theorem Form.ext_read {S : Shape} {Pins : Type*} (V W : Form S Pins)
    (size : ∀ v, V.width v = W.width v)
    (same : ∀ v pin x j, V.read v pin x j = W.read v pin x (Fin.cast (size v) j)) : V=W := by
  rcases V with ⟨wv,rv⟩
  rcases W with ⟨ww,rw'⟩
  have hs : wv=ww := funext size
  subst ww
  have eq : rv=rw' := by
    funext v p x j
    exact same v p x j
  subst rw'
  rfl

theorem append_cast_read {a b c d : ℕ} (ha : a=c) (hb : b=d) (left : Fin a→Bool) (right : Fin b→Bool)
    (left' : Fin c→Bool) (right' : Fin d→Bool)
    (hl : ∀ j, left j=left' (Fin.cast ha j)) (hr : ∀ j, right j=right' (Fin.cast hb j))
    (j : Fin (a+b)) :
    Fin.append left right j=Fin.append left' right' (Fin.cast (congrArg₂ Nat.add ha hb) j) := by
  subst c
  subst d
  rw [show left = left' from funext hl,show right = right' from funext hr]
  rfl

end ThreeFlat.Diagonal.HistoryContraction

end OAI
