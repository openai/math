import OAI.Hierarchy.DescentDatedTicketNativeRows
import OAI.Hierarchy.DescentDatedTicketSocketCore

namespace OAI
/-! # The raw selector address of the unique ordinary donor seat -/
namespace Hierarchy.DescentDatedOperandReadPipeline
open DescentDatedOperandCoordinates DescentSIMDLookup
open scoped Fin.CommRing
noncomputable section
variable (g : Geometry) (v : Data g) (j : Fin g.jobs) (h : Fin g.hosts) (k : Fin g.groups)
variable {B C : ℕ} (blocks : g.blocks=B) (cap : g.cap=C)
  (p : Fin g.paths) (born : Bool) (z : Ticket.SocketSeat B C)

def rawCandidate : Fin (g.paths*(g.blocks*(g.cap*11))) :=
  Fin.cast (by rw [blocks,cap]) (finProdFinEquiv (p,Ticket.seatNo z))

theorem rawCandidate_at : Ticket.socket p born z=(rawCandidate g blocks cap p z).val+1 :=
  Ticket.socket_at p born z

include blocks cap in
/-- The active raw gate uses the measured fourth anchor and the corresponding old or newborn path. -/
theorem rawKey_at_socket (cause : (v.origin j 0 h k).val=if born then 2 else 1)
    (path : (if born then (v.origin j 1 h k).val+1 else (pathV g v j 0 h k).val)=p.val+1)
    (anchor : (anchorV g v j 4 h k).val=Ticket.anchor born z 4)
    (mouth : born=true → (v.mouth j 1 h k).val=z.2.2.val) :
    (rawKey g v j h k).val=Ticket.socket p born z := by
  calc
    _=(rawLaw g.paths (B*(C*11)) g.digitBits 0 (fun i=>rawInputs g v j i h k)).val :=
      congrArg (fun n=>(rawLaw g.paths n g.digitBits 0 (fun i=>rawInputs g v j i h k)).val)
        (by rw [blocks,cap] : g.blocks*(g.cap*11)=B*(C*11))
    _=_ := Ticket.gate_socket p born z (fun i=>rawInputs g v j i h k) cause path anchor mouth

private theorem fields_at {B S actor kind rank block key start peer mouth start' peer' mouth' : ℕ}
    {x y : Fin 5→ℕ} {r t : Fin 6→ℕ} (born : Bool)
    (b : B=S) (a : actor=if born then 2 else 1) (k : kind=1)
    (str : start=start') (pr : peer=peer') (m : born=true→mouth=mouth')
    (ax : ∀f : Fin 5,f.val≤2 → x f=y f) (rx : ∀f : Fin 6,2≤f.val → r f=t f) :
    Ticket.fields B actor kind rank block key start peer mouth x r=
      Ticket.fields S (if born then 2 else 1) 1 rank block key start' peer' mouth' y t := by
  subst B
  subst actor
  subst kind
  subst start
  subst peer
  have same:=Ticket.fields_visible S (if born then 2 else 1) 1 rank block key start' peer' mouth
    (ax 0 (by decide)) (ax 1 (by decide)) (ax 2 (by decide)) (rx 2 (by decide)) (rx 3 (by decide))
    (rx 4 (by decide)) (rx 5 (by decide))
  rw [same]
  cases born with
  | false => simp [Ticket.fields]
  | true => rw [m rfl]


/-- At the two selected heads, the native ticket uses exactly the three observed
matcher columns and four raw columns. The serial and peer remain the values
of the actual eighth-column bank. -/
theorem ticketAt_active_fields (a : Fin (g.paths*(g.blocks*(g.cap*3))))
    (chosen : (anchorChoice g v j h k).val=a.val+1)
    (present : (rawKey g v j h k).val=Ticket.socket p born z)
    (cause : (v.origin j 0 h k).val=if born then 2 else 1) (kind : (v.prior j 0 h k).val=1)
    (mouth : born=true→(v.mouth j 1 h k).val=z.2.2.val)
    (matcher : ∀f : Fin 5,f.val≤2→(v.anchor j f a h k).val=Ticket.anchor born z f)
    (raw : Fin 6→ℕ) (material : ∀f : Fin 6,2≤f.val→
      (v.raw j (f.castLE (by decide : 6≤8)) (rawCandidate g blocks cap p z) h k).val=raw f) :
    let i:=rawCandidate g blocks cap p z
    ticketAt g v j h k=Ticket.fields B (if born then 2 else 1) 1 (rankV g v j 0 h k).val
      (v.origin j 2 h k).val (rawKey g v j h k).val (v.raw j 6 i h k).val (v.raw j 7 i h k).val
      z.2.2.val (Ticket.anchor born z) raw := by
  dsimp only
  have key:=(present.trans (rawCandidate_at g blocks cap p born z))
  rw [ticketAt_read_rows g v j h k a chosen _ key]
  exact fields_at born blocks cause kind rfl rfl mouth matcher material

/-- The literal eight words on the selected native row, before assigning any
interpretation to its original material. Either capture flag blanks serial
and peer; the surviving row carries both. -/
theorem ticketAt_socket_board (a : Fin (g.paths*(g.blocks*(g.cap*3))))
    (chosen : (anchorChoice g v j h k).val=a.val+1)
    (present : (rawKey g v j h k).val=Ticket.socket p born z)
    (cause : (v.origin j 0 h k).val=if born then 2 else 1) (kind : (v.prior j 0 h k).val=1)
    (mouth : born=true→(v.mouth j 1 h k).val=z.2.2.val)
    (matcher : ∀f : Fin 5,f.val≤2→(v.anchor j f a h k).val=Ticket.anchor born z f) :
    let i:=rawCandidate g blocks cap p z
    let raw:=fun f : Fin 6=>(v.raw j (f.castLE (by decide : 6≤8)) i h k).val
    let got:=raw 2≠0 ∨ raw 3≠0
    ticketAt g v j h k= ![if got then raw 4*B+z.1.val else 0,raw 2,raw 3,
      if z.2.2.val=0 then raw 5 else 1,if got then 0 else (v.raw j 6 i h k).val,
      if got then 0 else (v.raw j 7 i h k).val,z.2.1.val,z.2.2.val] := by
  let i:=rawCandidate g blocks cap p z
  let raw:=fun f : Fin 6=>(v.raw j (f.castLE (by decide : 6≤8)) i h k).val
  exact (ticketAt_active_fields g v j h k blocks cap p born z a chosen present cause kind mouth
    matcher raw (fun _ _=>rfl)).trans (Ticket.seat_fields p born z _ _ _ _ _ raw present)

end
end Hierarchy.DescentDatedOperandReadPipeline

end OAI
