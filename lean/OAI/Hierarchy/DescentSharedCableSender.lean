import OAI.Hierarchy.DescentSharedCableExchange

namespace OAI
/-! # Sending a short outgoing ordinal from a true bounded signed panel -/
namespace Hierarchy.DescentSharedCableNames.Exchange.Sender
open DescentSIMDLookup Stage
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
variable {D cap : ℕ}

def pair (a b : ℕ) : Cell a × Cell b ≃ Cell (a+b) := finProdFinEquiv.trans (finCongr (pow_add 2 a b).symm)
def slotBits (D cap : ℕ) := Packed.bits D+(Packed.bits cap+Packed.bits cap)
def inputBits (D cap : ℕ) := slotBits D cap*(2*cap)
def outputBits (D cap : ℕ) := Packed.bits cap*(D*cap)

def slot (x : Option (Triple D cap)) : Cell (slotBits D cap) :=
  pair _ _ (Packed.token (x.map Prod.fst),pair _ _ (Packed.token (x.map (fun t=>t.2.1)),Packed.token (x.map (fun t=>t.2.2))))

def unslot (D cap : ℕ) (c : Cell (slotBits D cap)) : Option (Triple D cap) :=do
  let f:=(pair (Packed.bits D) (Packed.bits cap+Packed.bits cap)).symm c
  let z:=(pair (Packed.bits cap) (Packed.bits cap)).symm f.2
  let p←Packed.readToken D f.1
  let s←Packed.readToken cap z.1
  let w←Packed.readToken cap z.2
  return (p,s,w)

@[simp] theorem slot_back (x : Option (Triple D cap)) : unslot D cap (slot x)=x :=by
  cases x with
  | none=>simp [unslot,slot]
  | some x=>obtain ⟨p,s,w⟩:=x;simp [unslot,slot]

/-- Only source-side records are retained. In particular no remote source
ordinal at a target-side occurrence is required on any input pin. -/
def input (row : Fin (2*cap)→Option (Live D cap)) : Cell (inputBits D cap) :=
  encode _ _ (fun s=>slot ((row s).bind sender))

def answer (row : Fin (2*cap)→Option (Live D cap)) : Cell (outputBits D cap) :=
  encode _ _ (fun j=>let p : Fin D × Fin cap:=finProdFinEquiv.symm j;Packed.token (chooseWire row p.1 p.2))

def table (D cap : ℕ) (key : Cell (inputBits D cap)) : Cell (outputBits D cap) :=
  let row:=unslot D cap ∘ (encode (slotBits D cap) (2*cap)).symm key
  encode _ _ (fun j=>let p : Fin D × Fin cap:=finProdFinEquiv.symm j;Packed.token (query row p.1 p.2))

theorem table_at (row : Fin (2*cap)→Option (Live D cap)) : table D cap (input row)=answer row :=by
  unfold table input answer chooseWire
  simp only [Equiv.symm_apply_apply]
  have restored : unslot D cap ∘ (fun s=>slot ((row s).bind sender))=fun s=>(row s).bind sender :=funext fun s=>slot_back _
  rw [restored]

theorem answer_at (row : Fin (2*cap)→Option (Live D cap)) (p : Fin D) (s : Fin cap) :
    digit (Packed.bits cap) (finProdFinEquiv (p,s)).val (answer row).val=(Packed.token (chooseWire row p s)).val :=by
  unfold answer;rw [digit_encode,Equiv.symm_apply_apply]

/-- One actual lookup produces every short outgoing ticket in its public
(peer,serial) order. Groups share the same ROM; final unused lanes are masked. -/
theorem publish {H r M w : ℕ} (L : Banks) (out : ℕ) (fit : Fits L (inputBits D cap) (outputBits D cap) M H r w out)
    (rows : Fin H→Fin r→Fin (2*cap)→Option (Live D cap)) (m : Memory w)
    (inputPins : PinFrame (M:=M) L (table D cap) (fun v g=>input (rows v g)) m) (positive : 0<M) :
    let result:=image out (H*chunks r M) (DescentSIMDLookup.lookup L) m
    let x:=fun v g=>input (rows v g)
    (DescentSIMDLookup.program L out H r M w).Exec m result (4+(H*chunks r M)*44) ∧
      (∀p : Row H r M,result (out+(row H r M p).val)=((masked (table D cap) x p : ℕ):Word w)) ∧
      (∀v g p s,digit (Packed.bits cap) (finProdFinEquiv (p,s)).val (digit (outputBits D cap) (lane g positive).val
        (result (out+(row H r M (position v g positive)).val)).val)=(Packed.token (chooseWire (rows v g) p s)).val) ∧
      CheapCode (DescentSIMDLookup.program L out H r M w) :=by
  intro result x
  have fitsExpr : (DescentSIMDLookup.lookup L).Fits w out:=by simp [DescentSIMDLookup.lookup,Expr.Fits,fit.source,fit.mask,fit.dictionary]
  have stored (p : Row H r M) : result (out+(row H r M p).val)=((masked (table D cap) x p:ℕ):Word w):=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (row H r M p)).trans (lookup_read L out fit (table D cap) x m inputPins p)
  refine ⟨?_,stored,?_,(DescentSIMDLookup.spec L out fit (table D cap) x).2⟩
  · intro P R K
    exact scan_exec out (H*chunks r M) (DescentSIMDLookup.lookup L) m fitsExpr fit.output
      (P:=P) (R:=R) (K:=K)
  · intro v g p s
    rw [physical_read L out fit (table D cap) x result stored v g positive,show table D cap (x v g)=answer (rows v g) from table_at _]
    exact answer_at _ p s


end
end Hierarchy.DescentSharedCableNames.Exchange.Sender

end OAI
