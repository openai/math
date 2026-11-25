import OAI.Hierarchy.TaggedWireLiveVisits
import OAI.Hierarchy.TaggedWireRoleTableROM

namespace OAI
/-! # Numeric local seat words for the terminal's native sparse write -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProbeStage.CoreBoard.WordSeats
open LinearAlgebra.SpectralBooks ChordGraph WireTelescope AdaptiveProbe ReportSockets
open scoped Classical

variable {h W k attempts edges : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
  (depth : ℕ) (marked : Marks h W k attempts) (unique : Exclusive marked)

theorem public_code (v : Site h (2^W) k) (p : Incident.Fiber (HistoryRoles.site S (attempts:=attempts)) v) :
    (publicOrdinal S v p).val = HistoryRoles.code S p.val := by
  rcases p with ⟨p,rfl⟩
  rfl

theorem allSeat_fixed (v : Site h (2^W) k) (x : Catalogue S π depth marked×Bool)
    (atSite : fixedSite S π depth marked x=v) :
    (allSeat S π depth marked unique v ⟨.inl x,atSite⟩).val =
      HistoryRoles.code S (.inl (HistoryRoles.paid S π depth marked unique x)) :=
  public_code S v (fixedRole S π depth marked unique v ⟨x,atSite⟩)

theorem allSeat_word (v : Site h (2^W) k) (x : Turn h (2^W) k) (atSite : site π x=v) :
    (allSeat S π depth marked unique v ⟨.inr x,atSite⟩).val =
      fixedRoom (k:=k) (attempts:=attempts) S + (ordinal (label x)).val := rfl

variable (B : Mount (S:=S) π (HistoryRoles.name (h:=h) (W:=W) (k:=k)) edges)
    (pad : Chord (siteLast h (2^W) k+1)) (fixed : Fin edges→ℕ)
    (ident : {i // 0<fixed i} ↪ Catalogue S π depth marked)

local notation "L" => B.matrixLayout (siteNumber h (2^W) k).injective pad
local notation "R" => fixedRoom (k:=k) (attempts:=attempts) S

def localSeat (x : LiveVisit S π B pad fixed) : Fin (room (k:=k) (attempts:=attempts) S) :=
  let u := liveVisit S π depth marked B pad fixed ident x
  allSeat S π depth marked unique (allSite S π depth marked u) ⟨u,rfl⟩

theorem fixed_code (e : {i // 0<fixed i}) (b : Bool) :
    (localSeat S π depth marked unique B pad fixed ident (.inl (e,b))).val =
      HistoryRoles.code S (.inl (HistoryRoles.paid S π depth marked unique
        (fixedVisit S π depth marked fixed ident (e,b)))) :=
  allSeat_fixed S π depth marked unique _ _ rfl

theorem payload_code (p : Fin (2^h)) (j : Fin (((L).steps (.inr (.inl (.inl p)))).length+1)) :
    (localSeat S π depth marked unique B pad fixed ident (.inr (.inl ⟨.inl p,j⟩))).val = R := by
  change R + 0 = R
  exact Nat.add_zero _

theorem alt_code (p : Fin (2^h)) (t : StageAt h (2^W)) (l : Fin k×Bool)
    (j : Fin (((L).steps (.inr (.inl (.inr ((p,t),l))))).length+1)) :
    let i := Sum.inr ((p,t),l)
    let phase := (boundaryIndex ((L).goods.tail i) ((L).goods.head i) (B.ordinary i) j).val
    (localSeat S π depth marked unique B pad fixed ident (.inr (.inl ⟨i,j⟩))).val =
      R + (1+3*(2*l.1.val+l.2.toNat)+phase) := by
  intro i phase
  have bound : phase≤2 := Nat.le_of_lt_succ (boundaryIndex ((L).goods.tail i)
    ((L).goods.head i) (B.ordinary i) j).isLt
  change R+(1+3*(2*l.1.val+l.2.toNat)+(clip 2 phase).val)=_
  rw [clip_val bound]

theorem reserve_code (c : Columns h (2^W)×Fin k)
    (j : Fin (((L).steps (.inr (.inr c))).length+1)) :
    let phase := (boundaryIndex ((L).reserve.tail c) ((L).reserve.head c) (B.centers c) j).val
    (localSeat S π depth marked unique B pad fixed ident (.inr (.inr ⟨c,j⟩))).val =
      R+(1+6*k+3*c.2.val+phase) := by
  intro phase
  have bound : phase≤2 := Nat.le_of_lt_succ (boundaryIndex ((L).reserve.tail c)
    ((L).reserve.head c) (B.centers c) j).isLt
  change R+(1+6*k+3*c.2.val+(clip 2 phase).val)=_
  rw [clip_val bound]

end Hierarchy.ProbeStage.CoreBoard.WordSeats

end
end OAI
