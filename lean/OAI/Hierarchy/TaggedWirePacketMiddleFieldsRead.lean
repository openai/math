import OAI.Hierarchy.TaggedWirePacketMiddleFields
import OAI.Hierarchy.TaggedWideCalendarPacketMiddle

namespace OAI
/-! # Reading the signed party's actual chord and width fields from the packet program -/

noncomputable section
namespace Hierarchy.WireTelescope.PacketTurns.Operands
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat Routing Diagonal.MotifOuterTerms
open ProtocolRAM Tagged AdaptiveProbe Computability.VPVNP.BurstRAM PrivateRAM
open ChosenPackets.RowRouting
open scoped Classical BigOperators Fin.CommRing
set_option quotPrecheck false

variable {W S n m : ℕ} (ends : Fin n→Chord S) (edge : Fin m→Chord S) (route : Fin n→List (Fin m))
    (qty : Fin n→ℕ) (o : Operands fun u=>(route u).length) (mem : Memory W) (row : Word W)
    (reads : Reads ends edge route qty o mem row) (fit : S≤2^W)
    (party : Expr) (s : Fin S) (atSite : party.eval mem row=(s.val:Word W))

include reads fit in
theorem sameChord_read (i j : Fin n) (yes no : Expr) :
    (o.sameChord i j yes no).eval mem row=if ends i=ends j then yes.eval mem row else no.eval mem row := by
  rw [sameChord,PacketScan.eq_select mem row _ _ _ _ (reads.oldLo i) (reads.oldLo j)
    ((ends i).1.1.isLt.trans_le fit) ((ends j).1.1.isLt.trans_le fit),
    PacketScan.eq_select mem row _ _ _ _ (reads.oldHi i) (reads.oldHi j)
      ((ends i).1.2.isLt.trans_le fit) ((ends j).1.2.isLt.trans_le fit)]
  by_cases lo : (ends i).1.1.val=(ends j).1.1.val
  · by_cases hi : (ends i).1.2.val=(ends j).1.2.val
    · have same : ends i=ends j:=Subtype.ext (Prod.ext (Fin.ext lo) (Fin.ext hi));simp [same]
    · have diff : ends i≠ends j:=fun h=>hi (congrArg (fun e:Chord S=>e.1.2.val) h)
      simp [lo,hi,diff]
  · have diff : ends i≠ends j:=fun h=>lo (congrArg (fun e:Chord S=>e.1.1.val) h)
    simp [lo,diff]

include reads fit atSite in
theorem atParty_read (i : Fin n) (b : Bool) (yes no : Expr) :
    (o.atParty party i b yes no).eval mem row=
      if (portGraph S).vertex (ends i) b=s then yes.eval mem row else no.eval mem row := by
  have data : (o.oldSite i b).eval mem row=(((portGraph S).vertex (ends i) b).val:Word W) := by
    cases b <;>first | exact reads.oldLo i | exact reads.oldHi i
  rw [atParty,PacketScan.eq_select mem row _ _ _ _ data atSite
    (((portGraph S).vertex (ends i) b).isLt.trans_le fit) (s.isLt.trans_le fit)]
  by_cases eqn : (portGraph S).vertex (ends i) b=s
  · rw [ite_eq_left (congrArg Fin.val eqn), ite_eq_left eqn]
  · rw [ite_eq_right (fun h=>eqn (Fin.ext h)), ite_eq_right eqn]

include reads fit in
theorem middleSum_read (i : Fin n) (t : ℕ) :
    (o.middleSum i t).eval mem row=
      (TaggedShorterCommonScan.earlier (NamedAperture.key ends) qty t (NamedAperture.key ends i):Word W) := by
  induction t with
  | zero=>simp [middleSum,TaggedShorterCommonScan.earlier,Expr.eval]
  | succ t ih=>
    rw [middleSum,PacketScan.add_eval,ih]
    unfold TaggedShorterCommonScan.earlier
    rw [Finset.sum_range_succ,Nat.cast_add]
    congr 1
    by_cases present:t<n
    · rw [dite_eq_left present,dite_eq_left present,sameChord_read ends edge route qty o mem row reads fit]
      by_cases eqn : ends i=ends ⟨t,present⟩
      · simp [eqn,NamedAperture.key,reads.width]
      · have diff : NamedAperture.key ends ⟨t,present⟩≠NamedAperture.key ends i:=
          fun h=>eqn ((Fintype.equivFin _).injective h).symm
        simp [eqn,diff,Expr.eval]
    · simp [present,Expr.eval]

def middleValues (s : Fin S) : MiddleField n→ℕ
  | .inl (i,f)=>match f.val with
    | 0=>qty i
    | 1=>if (portGraph S).vertex (ends i) false=s then 1 else 0
    | 2=>if (portGraph S).vertex (ends i) true=s then 1 else 0
    | 3=>Middle.base ends qty (i,false)
    | 4=>if (portGraph S).vertex (ends i) false=s then installedWidths ends qty (ends i) else 0
    | _=>if (portGraph S).vertex (ends i) true=s then installedWidths ends qty (ends i) else 0
  | .inr ((i,b),(j,c))=>if (portGraph S).vertex (ends i) b=s ∧
      (portGraph S).vertex (ends j) c=s ∧ ends i=ends j then qty i else 0

include reads fit atSite in
theorem middleColsAt_read (f : MiddleField n) :
    (o.middleColsAt party f).eval mem row=(middleValues ends qty s f:Word W) := by
  have tt (i : Fin n) : TaggedShorterCommonScan.earlier (NamedAperture.key ends) qty n (NamedAperture.key ends i)=
      installedWidths ends qty (ends i) :=
    (NativeSlot.full (NamedAperture.key ends) qty _).trans (NamedAperture.measured ends qty (ends i))
  rcases f with ⟨i,k⟩|⟨⟨i,b⟩,⟨j,c⟩⟩
  · fin_cases k <;>simp only [middleColsAt,middleValues,Middle.base,reads.width,
      atParty_read ends edge route qty o mem row reads fit party s atSite,
      middleSum_read ends edge route qty o mem row reads fit,tt,Expr.eval] <;>split_ifs <;>rfl
  · simp only [middleColsAt,middleValues,
      atParty_read ends edge route qty o mem row reads fit party s atSite,
      sameChord_read ends edge route qty o mem row reads fit,reads.width,Expr.eval]
    have mask (a b c : Prop) [Decidable a] [Decidable b] [Decidable c] (q : ℕ) :
        (if a then (if b then (if c then (q : Word W) else 0) else 0) else 0) =
        ((if a ∧ b ∧ c then q else 0 : ℕ) : Word W) := by
      by_cases ha : a <;> by_cases hb : b <;> by_cases hc : c <;> simp [ha,hb,hc]
    exact mask _ _ _ _

def middleLift {M : ℕ} (le:n≤M) : MiddleField n→MiddleField M
  | .inl (i,f)=>.inl (i.castLE le,f)
  | .inr ((i,b),(j,c))=>.inr ((i.castLE le,b),(j.castLE le,c))

include reads fit atSite in
theorem middleFields_read (M : ℕ) (le : n≤M) (f : MiddleField n) :
    (o.middleFields M party (middleNumber M (middleLift le f))).eval mem row=(middleValues ends qty s f:Word W) := by
  rw [middleFields,Function.comp_apply,Equiv.symm_apply_apply]
  rcases f with ⟨i,k⟩|⟨⟨i,b⟩,⟨j,c⟩⟩ <;>
    simp only [middleLift,widenMiddle,Fin.val_castLE,dite_eq_left i.isLt] <;>
    first | exact middleColsAt_read ends edge route qty o mem row reads fit party s atSite _ |
      simpa only [dite_eq_left j.isLt] using middleColsAt_read ends edge route qty o mem row reads fit party s atSite
        (.inr ((i,b),(j,c)))

section TypedRows
open LinearAlgebra.SpectralBooks SiteTensor
open ChosenPackets
variable {F : Type} [Field F] {N H copies : ℕ} {rr : Row F S H copies} {phys : Fin N→Chord S}
    (R : RowRouting rr phys) (c : Histogram (Fin H) copies)
local notation "src" => Installs.starts (source:=R.source) R.order
local notation "w" => Installs.numbered R.order (R.bits c)
local notation "num" => Fintype.card R.Roles
local notation "I" => Fin num×Bool
variable {m : ℕ} (es : Fin m→Chord S) (walk : Fin (Fintype.card R.Roles)→List (Fin m)) (fields : Operands fun i=>(walk i).length)
    (receipt : Reads (Installs.starts (source:=R.source) R.order) es walk (Installs.numbered R.order (R.bits c)) fields mem row) (M : ℕ) (le : Fintype.card R.Roles≤M) (cap : ℕ)
    (fits : ∀a,Installs.numbered R.order (R.bits c) a≤cap) (allRoom : ∀a,installedWidths (Installs.starts (source:=R.source) R.order) (Installs.numbered R.order (R.bits c)) (Installs.starts (source:=R.source) R.order a)≤cap)
local notation "parts" => Middle.parts R c s cap fits
local notation "atField" => fun f => (fields.middleFields M party (middleNumber M (middleLift le f))).eval mem row

include fit atSite receipt allRoom in
theorem gather_field_read :
    (∀p q : I,atField (.inr (p,q))=((ChordAperture.sizeAt parts p q).val:Word W)) ∧
    (∀p : I,atField (.inl (p.1,3))=((ChordAperture.head parts p true).val:Word W)) ∧
    (∀p : I,atField (.inl (p.1,if p.2 then 5 else 4))=(ChordAperture.room parts p:Word W)) := by
  have data:=middleFields_read src es walk w fields mem row receipt fit party s atSite M le
  have width : installedWidths src w=rr.output c:=
    (Installs.packed (source:=R.source) R.order (R.bits c)).trans (R.shape c)
  refine ⟨fun p q=>?_,fun p=>?_,fun p=>?_⟩
  · refine (data (.inr (p,q))).trans ?_
    rw [Middle.sizeAt_fields]
    rcases p with ⟨i,b⟩;rcases q with ⟨j,f⟩;rfl
  · refine (data (.inl (p.1,3))).trans ?_
    rw [Middle.head_fields]
    have bound : Middle.base src w p≤cap :=
      (Nat.le_add_right _ (w p.1)).trans ((Middle.base_top src w p).trans (allRoom p.1))
    change (Middle.base src w p : Word W) = ((min cap (Middle.base src w p) : ℕ) : Word W)
    rw [Nat.min_eq_right bound]
  · refine (data (.inl (p.1,if p.2 then 5 else 4))).trans ?_
    rw [Middle.room_fields,←width]
    rcases p with ⟨i,_|_⟩ <;>rfl

end TypedRows

end Hierarchy.WireTelescope.PacketTurns.Operands
end

end OAI
