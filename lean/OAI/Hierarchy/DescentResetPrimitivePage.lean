import OAI.Hierarchy.DescentResetEmissionPalette
import OAI.Hierarchy.DescentContactWidthPage
import OAI.Hierarchy.DescentOperandFieldJoin

namespace OAI
/-! # Translating compact reset roles into the global literal coefficient dictionary -/
namespace Hierarchy.DescentResetPrimitivePage
open DescentSIMDLookup DescentPackedZip DescentPrimitivePalette DescentSixParty DescentEpochTagKeys
open DescentPackedResetRotorRoles DescentOrdinaryAtomFieldRAM.ROM DescentResetGates
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {F : Type} [Field F] (G : PoweredGadget F) (s Z : ℕ) (op : RotorSpec)
local notation "t" => printedBits G s Z op

def gate (a : ℕ) (x : Cell a) (_ : Cell 0) :=decoded G s Z op x.val
def relay (x : Cell 1) (_ : Cell 0) :=if x=0 then (0:Cell t) else relayToken G s Z op
def words (a M : ℕ) :=2*2^(a*M)+2*2^M
def middle (floor a M : ℕ) :=floor+2*2^(a*M)
def endAddress (floor a M : ℕ) :=middle floor a M+2*2^M
def clock (a M : ℕ) :=8+10*words a M
def size (a M : ℕ) :=15*(words a M+2)
def program (floor a M w : ℕ) :=(mount (binary (gate G s Z op a) M) (a*M) w floor).seq
  (mount (binary (relay G s Z op) M) M w (middle floor a M))
def firstImage {w} (floor a M : ℕ) (m : Memory w) :=after (binary (gate G s Z op a) M) (a*M) floor m
def image {w} (floor a M : ℕ) (m : Memory w) :=after (binary (relay G s Z op) M) M (middle floor a M)
  (firstImage G s Z op floor a M m)
def expr (floor a M : ℕ) (old fresh self : Expr) :=Expr.op .add old (.op .add
  (DescentStaticUnary.query (gate G s Z op a) M floor fresh)
  (DescentStaticUnary.query (relay G s Z op) M (middle floor a M) self))

theorem any {w} (floor a M : ℕ) (m : Memory w) (room : endAddress floor a M<2^w) :
    (program G s Z op floor a M w).Exec m (image G s Z op floor a M m) (clock a M) ∧
    CheapCode (program G s Z op floor a M w) ∧
    ∀j,j<floor ∨ endAddress floor a M≤j→image G s Z op floor a M m j=m j :=by
  let p:=binary (gate G s Z op a) M
  let q:=binary (relay G s Z op) M
  have mid:=DescentOrdinaryAtomFieldRAM.ROM.run p (a*M) floor m ((Nat.le_add_right ..).trans_lt room)
  have fin:=DescentOrdinaryAtomFieldRAM.ROM.run q M (middle floor a M) (firstImage G s Z op floor a M m) room
  have ticks : 4+10*(2*2^(a*M))+(4+10*(2*2^M))=clock a M:=by simp [clock,words,Nat.mul_add];omega
  refine ⟨ticks ▸ Procedure.Exec.then mid.1 fin.1,cheap_seq (cheap p (a*M) w floor) (cheap q M w (middle floor a M)),?_⟩
  intro j away
  exact (frame q M (middle floor a M) (firstImage G s Z op floor a M m) j
    (away.imp (fun h=>h.trans_le (Nat.le_add_right ..)) id)).trans
    (frame p (a*M) floor m j (away.imp id (fun h=>(Nat.le_add_right ..).trans h)))

theorem tariff {w} (floor a M : ℕ) (m : Memory w) (room : endAddress floor a M<2^w) :
    DescentStaticWordColumn.names (program G s Z op floor a M w)=size a M :=by
  let p:=binary (gate G s Z op a) M
  let q:=binary (relay G s Z op) M
  have one:=DescentOrdinaryAtomFieldRAM.ROM.run p (a*M) floor m ((Nat.le_add_right ..).trans_lt room)
  have two:=DescentOrdinaryAtomFieldRAM.ROM.run q M (middle floor a M) m room
  change DescentStaticWordColumn.names ((mount p (a*M) w floor).seq (mount q M w (middle floor a M)))=_
  rw [DescentStaticWordColumn.names_seq,one.2,two.2]
  simp [size,words,Nat.mul_add]; omega

theorem fitted {w} (floor a M : ℕ) (old fresh self : Expr)
    (past : old.Fits w floor ∧ fresh.Fits w floor ∧ self.Fits w floor) (room : endAddress floor a M<2^w) :
    (expr G s Z op floor a M old fresh self).Fits w (endAddress floor a M) :=by
  let top:=endAddress floor a M
  have upto : floor≤top:=(Nat.le_add_right ..).trans (Nat.le_add_right ..)
  refine ⟨ProtocolRAMGeneratedWrite.fits_mono old upto past.1,
    DescentContactWidthPage.general_fits _ _ _ _ _ (ProtocolRAMGeneratedWrite.fits_mono fresh upto past.2.1)
      (Nat.le_add_right ..) room,?_⟩
  apply DescentContactWidthPage.general_fits _ _ _ _ _ (ProtocolRAMGeneratedWrite.fits_mono self upto past.2.2)
  · simp [top,endAddress]
  · exact room

def oldWord {b : ℕ} : PrintedInput b→Cell b
  | .retained r=>r
  | _=>0
def relayFlag {b : ℕ} : PrintedInput b→Cell 1
  | .relay=>1
  | _=>0
def localRole {b : ℕ} : PrintedInput b→ℕ
  | .bank r=>r
  | _=>0
def freshWord (p : PrintedInput t) : Cell t :=
  match p with
  | .bank r=>decoded G s Z op r
  | .relay=>relayToken G s Z op
  | _=>0

private theorem plus {H L w M b} (l r : Expr) (m : Memory w) (x y z : Fin H→Fin L→Cell b)
    (sum : ∀h j,(x h j).val+(y h j).val=(z h j).val)
    (left : Source l x M m) (right : Source r y M m) : Source (.op .add l r) z M m :=by
  intro i
  change l.eval m _+r.eval m _=_
  rw [left i,right i,←Nat.cast_add,DescentOperandFieldJoin.packed_add x y z sum i]

/-- Combine the earlier gated retained token, authentic raw birth register and
relay activation. Disjointness is physical per host and group and includes the
unoccupied lanes of the last word. -/
theorem posted {H L w} (floor a M : ℕ) (m : Memory w) (old fresh self : Expr)
    (x : Fin H→Fin L→PrintedInput t) (rawFits : ∀h j,localRole (x h j)<2^a)
    (past : old.Fits w floor ∧ fresh.Fits w floor ∧ self.Fits w floor)
    (stored : Source old (fun h j=>oldWord (x h j)) M m)
    (born : Source fresh (fun h j=>(localRole (x h j):Cell a)) M m)
    (relays : Source self (fun h j=>relayFlag (x h j)) M m) (room : endAddress floor a M<2^w) :
    Source (expr G s Z op floor a M old fresh self) (fun h j=>emit G s Z op (x h j)) M (image G s Z op floor a M m) :=by
  let mid:=middle floor a M
  let y:=firstImage G s Z op floor a M m
  let dst:=image G s Z op floor a M m
  have gatePage:=DescentStaticUnary.read (H:=H) (G:=L) (M:=M) (gate G s Z op a)
    (by simp [gate,decoded_zero]) floor m ((Nat.le_add_right ..).trans_lt room)
  have relayPage:=DescentStaticUnary.read (H:=H) (G:=L) (M:=M) (relay G s Z op)
    (by simp [relay]) mid y (by simpa [endAddress,mid] using room)
  simp only [Nat.one_mul] at relayPage
  have kept j (h:j<floor) : dst j=m j:=(any G s Z op floor a M m room).2.2 j (.inl h)
  have before j (h:j<floor) : y j=m j:=gatePage.2.2.1 j (.inl h)
  have end_ j (h:j< mid) : dst j=y j:=relayPage.2.2.1 j (.inl h)
  have raw:=gatePage.2.1 fresh _ past.2.1 born
  have after:=relayPage.2.1 self _ (ProtocolRAMGeneratedWrite.fits_mono self (Nat.le_add_right ..) past.2.2)
    (fun j=>(eval_below self _ m y past.2.2 before).trans (relays j))
  apply plus _ _ dst (fun h j=>oldWord (x h j)) (fun h j=>freshWord G s Z op (x h j))
  · intro h j
    cases hx:x h j <;> simp [freshWord,emit,oldWord]
  · exact fun i=>(eval_below old _ m dst past.1 kept).trans (stored i)
  · apply plus _ _ dst (fun h j=>gate G s Z op a (localRole (x h j)) 0)
      (fun h j=>relay G s Z op (relayFlag (x h j)) 0)
    · intro h j
      rw [gate,Fin.val_cast_of_lt (rawFits h j)]
      cases hx:x h j <;> simp [localRole,relayFlag,relay,freshWord,decoded_zero]
    · exact fun i=>(eval_below _ _ y dst raw.1 end_).trans (raw.2 i)
    · exact after.2

end
end Hierarchy.DescentResetPrimitivePage

end OAI
