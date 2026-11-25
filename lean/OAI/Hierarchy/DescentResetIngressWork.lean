import OAI.Hierarchy.DescentResetCanvasIngressBill
import OAI.Hierarchy.DescentOriginalPitchPages
import OAI.Hierarchy.DescentGlobalControlRoom

namespace OAI
/-! Row work and shared lookup work of the charged reset ingress, with the two real pitches. -/
namespace Hierarchy.DescentResetCanvasIngress.Layout
open DescentSIMDLookup DescentSixParty Filter
noncomputable section
variable (s : DescentResetCanvasIngress.Layout)

def columns := 2^s.k+s.signed.slots

theorem source_chunk_room (G h unit : ℕ) (high : 4*unit ≤ h) (positive : 0 < unit) :
    chunks G (lanes (h/2) unit)*h ≤ h+8*G*unit := by
  let M:=lanes (h/2) unit
  have eq_:M=h/(4*unit):=by
    dsimp [M,lanes]
    rw [Nat.div_div_eq_div_mul,show 2*(2*unit)=4*unit by ring]
  have yes:0<M:=by rw [eq_];exact (Nat.div_pos high (by omega))
  have modh:=Nat.mod_lt h (by omega : 0<4*unit)
  have identity:=Nat.mod_add_div h (4*unit)
  rw [←eq_] at identity
  have rate:h≤8*M*unit:=by nlinarith only [identity,modh,Nat.mul_le_mul_right unit yes]
  have cut:=Nat.mul_le_mul_right h (Overlap.chunks_floor G M yes)
  rw [Nat.succ_mul] at cut
  have div:=Overlap.floor_bill G M h 8 unit rate
  calc
    chunks G M*h ≤ (G/M)*h+h := cut
    _ ≤ h+8*G*unit := by omega

private theorem venue_bill (a : DescentVenueSlabs.Shape) (half : ℕ)
    (shared : (Overlap.pieces a.groups a.sourceLanes a.targetLanes+1)*(a.sourceLanes+1)*
      2^(a.bits*a.sourceLanes) ≤ half) :
    DescentVenueSlabs.ExprInputs.tariff a 7 ≤
      4096*(1+a.pages*(1+a.hosts*chunks a.groups a.sourceLanes+a.hosts*chunks a.groups a.targetLanes)+half) := by
  dsimp [DescentVenueSlabs.ExprInputs.tariff,Overlap.rows]
  nlinarith only [Nat.mul_le_mul_left 2048 shared,Nat.zero_le a.pages,
    Nat.zero_le (a.pages*a.hosts*chunks a.groups a.sourceLanes),Nat.zero_le (a.pages*a.hosts*chunks a.groups a.targetLanes),
    Nat.zero_le half]

set_option maxRecDepth 4096 in
theorem work_of_books (half : ℕ)
    (books : ∀d∈[s.signed.bits,s.oldBits],
      (Overlap.pieces s.groups s.sourceLanes s.targetLanes+1)*(s.sourceLanes+1)*2^(d*s.sourceLanes) ≤ half)
    (raw : 2^(s.collector.unitBits*s.targetLanes) ≤ half) :
    let O:=s.hosts*chunks s.groups s.sourceLanes
    let N:=s.hosts*chunks s.groups s.targetLanes
    s.bill 7≤16384*((s.columns+1)*(1+O+N)+(s.columns+1)*half) := by
  intro O N
  let P:=2^s.k
  let slots:=s.signed.slots
  let cols:=P+slots
  let num:=P+slots*2
  have one:=venue_bill s.signed.venue half (books s.signed.bits (by simp))
  have two:=venue_bill s.amounts half (books s.oldBits (by simp))
  change DescentVenueSlabs.tariff s.signed.venue≤4096*(1+slots*(1+O+N)+half) at one
  change DescentVenueSlabs.ExprInputs.tariff s.amounts 7≤4096*(1+P*(1+O+N)+half) at two
  have fresh₁:2^(s.signed.bits*s.targetLanes) ≤ half := (Nat.pow_le_pow_right (by decide : 0<2)
    (Nat.mul_le_mul_right _ (le_max_right s.oldBits s.signed.bits))).trans raw
  have fresh₂:=Nat.mul_le_mul_left num raw
  change num*2^(s.collector.unitBits*s.targetLanes) ≤ num*half at fresh₂
  change DescentVenueSlabs.tariff s.signed.venue+(4+10*2^(s.signed.bits*s.targetLanes)+7*(15*(2^(s.signed.bits*s.targetLanes)+1)))+
    (4+slots*(4+N*28)+7*(15+slots*59))+DescentVenueSlabs.ExprInputs.tariff s.amounts 7+
    ((4+10*N+7*(15*(N+1)))+(4+10*(num*2^(s.collector.unitBits*s.targetLanes))+7*(15*(num*2^(s.collector.unitBits*s.targetLanes)+1)))+
      (4+N*(2*(1+num*28)+4)+7*(11+4*(1+num*28))))≤16384*((cols+1)*(1+O+N)+(cols+1)*half)
  dsimp only [num,cols] at *
  nlinarith only [one,two,fresh₁,fresh₂,Nat.zero_le P,Nat.zero_le slots,Nat.zero_le N,Nat.zero_le O,
    Nat.zero_le (P*N),Nat.zero_le (slots*N),Nat.zero_le (slots*O),Nat.zero_le (P*O),
    Nat.zero_le (slots*half),Nat.zero_le (P*half),Nat.zero_le half]

theorem work_bound (h : ℕ) (high : 64 ≤ h) (old : s.sourceLanes ≤ h) (next : s.targetLanes ≤ h)
    (signed : s.signed.bits*s.sourceLanes ≤ h/4) (paid : s.oldBits*s.sourceLanes ≤ h/4)
    (fresh : s.collector.unitBits*s.targetLanes ≤ h/2) :
    let O:=s.hosts*chunks s.groups s.sourceLanes
    let N:=s.hosts*chunks s.groups s.targetLanes
    s.bill 7≤16384*((s.columns+1)*(1+O+N)+(s.columns+1)*2^(h/2)) := by
  apply s.work_of_books
  · intro d hd
    rcases List.mem_cons.mp hd with rfl|hd
    · exact Overlap.original_pages _ _ _ _ _ high old next signed
    · have := List.mem_singleton.mp hd
      subst d
      exact Overlap.original_pages _ _ _ _ _ high old next paid
  · exact Nat.pow_le_pow_right (by decide) fresh

/-- Both old and new pitch are the physical Walsh pitch at the reset. The shared
repacking tables multiply their half-word entries by a polynomial in the word width. -/
theorem matching_bill (h w ratio : ℕ) (matchPitch : s.sourceLanes=s.targetLanes)
    (small : s.targetLanes ≤ h) (key : s.collector.unitBits*s.targetLanes ≤ h/2)
    (word : w ≤ ratio*h) (hosts : 0 < s.hosts) (unit : ℕ)
    (rows : chunks s.groups s.targetLanes*h ≤ h+s.groups*unit) :
    s.bill 7*w ≤ s.hosts*h*(65536*(s.columns+1)*ratio)+
      s.hosts*s.groups*(65536*(s.columns+1)*ratio*unit)+
      (65536*(s.columns+1)*ratio*(h+1)^3)*2^(h/2) := by
  let lut:=(2*h+3)*(h+1)*2^(h/2)
  have oldL:s.sourceLanes ≤ h:=matchPitch.trans_le small
  have table:2^(s.collector.unitBits*s.targetLanes)≤2^(h/2):=Nat.pow_le_pow_right (by decide) key
  have mult:0<(2*h+3)*(h+1):=Nat.mul_pos (by omega) (by omega)
  have last:2^(s.collector.unitBits*s.targetLanes) ≤ lut:=table.trans (Nat.le_mul_of_pos_left _ mult)
  have common (d : ℕ) (present : d∈[s.signed.bits,s.oldBits]) :
      (Overlap.pieces s.groups s.sourceLanes s.targetLanes+1)*(s.sourceLanes+1)*2^(d*s.sourceLanes) ≤ lut := by
    have pieces:Overlap.pieces s.groups s.sourceLanes s.targetLanes ≤ chunks s.targetLanes s.sourceLanes+1:=Nat.min_le_right ..
    have count:chunks s.targetLanes s.sourceLanes ≤ s.targetLanes+s.sourceLanes:=(Nat.div_le_self _ _).trans (Nat.sub_le ..)
    have width:d ≤ s.collector.unitBits:=by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at present
      rcases present with rfl|rfl
      · exact le_max_right ..
      · exact le_max_left ..
    exact Nat.mul_le_mul (Nat.mul_le_mul (by omega) (by omega))
      ((Nat.pow_le_pow_right (by decide : 0<2) ((Nat.mul_le_mul_right _ width).trans_eq (congrArg (s.collector.unitBits*·) matchPitch))).trans table)
  have fee:=Nat.mul_le_mul (s.work_of_books lut common last) word
  rw [matchPitch] at fee
  have traffic:=Nat.mul_le_mul_left (16384*(s.columns+1)*ratio*s.hosts) rows
  have old:=Nat.mul_le_mul_right (16384*(s.columns+1)*ratio*h) hosts
  dsimp only [lut] at fee
  nlinarith only [fee,traffic,old,Nat.zero_le (s.hosts*h*(s.columns+1)*ratio),
    Nat.zero_le (s.hosts*s.groups*(s.columns+1)*ratio*unit),
    Nat.zero_le ((s.columns+1)*ratio*2^(h/2)),Nat.zero_le ((s.columns+1)*ratio*h*2^(h/2)),
    Nat.zero_le ((s.columns+1)*ratio*h^2*2^(h/2)),Nat.zero_le ((s.columns+1)*ratio*h^3*2^(h/2))]

/-- The earlier stage and the Canvas may use different pitches; each pays its own
actual host/slab traffic. The tables are mounted once over all physical hosts. -/
theorem dated_bill (h w unit ratio : ℕ) (high : 64 ≤ h) (word : w ≤ ratio*h) (old : s.sourceLanes ≤ h)
    (next : s.targetLanes ≤ h) (signed : s.signed.bits*s.sourceLanes ≤ h/4)
    (paid : s.oldBits*s.sourceLanes ≤ h/4) (fresh : s.collector.unitBits*s.targetLanes ≤ h/2)
    (oldRows : chunks s.groups s.sourceLanes*h ≤ h+s.groups*unit)
    (newRows : chunks s.groups s.targetLanes*h ≤ h+s.groups*unit) (hosts : 0 < s.hosts) :
    s.bill 7*w≤ s.hosts*h*(65536*(s.columns+1)*ratio)+
      s.hosts*s.groups*(65536*(s.columns+1)*ratio*unit)+
      (16384*(s.columns+1)*ratio*h)*2^(h/2) := by
  have total:=Nat.mul_le_mul (s.work_bound h high old next signed paid fresh) word
  let C:=16384*(s.columns+1)*ratio
  have prev:=Nat.mul_le_mul_left (C*s.hosts) oldRows
  have last:=Nat.mul_le_mul_left (C*s.hosts) newRows
  have first:=Nat.mul_le_mul_right (h*C) hosts
  dsimp only [C] at prev last first
  nlinarith only [total,prev,last,first,Nat.zero_le (s.hosts*h*(s.columns+1)*ratio),
    Nat.zero_le (s.hosts*s.groups*(s.columns+1)*ratio*unit)]

end
end Hierarchy.DescentResetCanvasIngress.Layout

end OAI
