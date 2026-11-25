import OAI.Hierarchy.DescentResetStencilWork
import OAI.Hierarchy.DescentDatedResetArea
import OAI.Hierarchy.DescentResetStencilPrice

namespace OAI
/-! # The price of the installed lookup words and the reset stencil's actual scans -/
namespace Hierarchy.DescentPlainTerminal.Suffix.StencilBook
open DescentSixParty.PackedFlow DescentSIMDLookup DescentPackedColony DescentGLPacked.BankImage ProtocolRAM
noncomputable section

/-- These five exponents are exactly the addresses of the physical lookup pages. -/
structure Widths (S : StencilBook) (h : ℕ) : Prop where
  layers : unit S.r S.b*S.M≤h/2
  cutoff : S.levels+S.total≤h/2
  readers : Stencil.ReaderTables.largest S.r S.m S.n S.b S.M≤h/2
  planes : (2^S.r*S.m+2^S.r)*S.M≤h/2
  gather : (S.n*Stencil.count S.r (S.degree+S.degree)+S.n)*S.M≤h/2

def pageCount (S : StencilBook) :=
  40+2*(S.degree+4+5*S.r)+Fintype.card (Stencil.ReaderTables.Key S.r)+(S.m+1)+Stencil.count S.r (S.degree+S.degree)

def units (S : StencilBook) (h : ℕ) := 1+S.hosts+S.rows+2^(h/2)

private theorem unit_bounds (a b c : ℕ) :
    1+a ≤ 1+a+b+c ∧ 1+b ≤ 1+a+b+c ∧ c ≤ 1+a+b+c := by omega

theorem installed_span (S : StencilBook) (h base : ℕ) (rooms : Widths S h) :
    S.endAddress base≤base+S.pageCount*S.units h := by
  let Q:=S.units h
  let T:=2^(h/2)
  let u:=S.degree+4+5*S.r
  let z:=Stencil.count S.r (S.degree+S.degree)
  let e:=Stencil.ReaderTables.largest S.r S.m S.n S.b S.M
  let a:=S.n*z
  obtain ⟨hostPos, rowPos, top⟩ := unit_bounds S.hosts S.rows T
  change 1 + S.hosts ≤ Q at hostPos
  change 1 + S.rows ≤ Q at rowPos
  change T ≤ Q at top
  have row : S.rows ≤ Q := by omega
  have host : S.hosts ≤ Q := by omega
  have pow (n) (le:n≤h/2) : 2^n≤Q:=(Nat.pow_le_pow_right (by decide) le).trans top
  have rowPg:2^(Nat.clog 2 S.rows)≤2*Q:=(Dated.rounded _).trans (by omega)
  have hostPg:2^(Nat.clog 2 S.hosts)≤2*Q:=(Dated.rounded _).trans (by omega)
  have before:2^S.splitBits≤2*Q:=by
    change 2 ^ max ((max S.hosts S.rows).log2+1) (unit S.r S.b*S.M) ≤ 2*Q
    rcases le_total ((max S.hosts S.rows).log2+1) (unit S.r S.b*S.M) with le|le
    · rw [max_eq_right le];exact (pow _ rooms.layers).trans (by omega)
    · rw [max_eq_left le,Nat.pow_succ]
      by_cases hz:max S.hosts S.rows=0
      · rw [hz]; simp; omega
      · have limit:2^(max S.hosts S.rows).log2≤Q:=(Nat.log2_self_le hz).trans (max_le host row)
        omega
  have keys:=pow e rooms.readers
  have planes:=pow _ rooms.planes
  have cutoff:=pow _ rooms.cutoff
  have levels:=pow S.levels ((Nat.le_add_right ..).trans rooms.cutoff)
  have cast:=pow (S.b*2^S.r*S.M) (((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans rooms.readers)
  have gathers:=pow ((a+S.n)*S.M) rooms.gather
  have lookup:=pow (a*S.M) ((Nat.mul_le_mul_right _ (Nat.le_add_right ..)).trans rooms.gather)
  have bins:=Nat.mul_le_mul_left u before
  have menus:=Nat.mul_le_mul_left (Fintype.card (Stencil.ReaderTables.Key S.r)) keys
  have dirs:=Nat.mul_le_mul_left (S.m+1) planes
  have ins:=Nat.mul_le_mul_left (z+1) gathers
  rw [S.extent]
  change base+_+u*2^S.splitBits+_+(_+_*2^e+_)+((z+1)*2^((a+S.n)*S.M)+2^(a*S.M)+_+_)≤base+_*Q
  change _ ≤ base + (40 + 2*u + Fintype.card (Stencil.ReaderTables.Key S.r) + (S.m+1) + z)*Q
  nlinarith only [rowPg,hostPg,bins,menus,dirs,ins,levels,cutoff,cast,lookup,row,Nat.zero_le Q]

theorem literal_le_span (S : StencilBook) (X : Sources) (base out D cap : ℕ) :
    S.literalWords base out X D cap≤S.endAddress base-base := by
  let A:=S.layer base out X.roster
  let H:=S.header base
  let N:=S.narrow base
  let C:=S.readers base
  let F:=S.last base
  have a:base≤A.origin:=Nat.le_add_right ..
  have b:A.origin≤A.fresh S.degree S.r:=Nat.le_add_right ..
  have c:A.fresh S.degree S.r≤H.origin:=by
    have split:=S.split_end base X.roster (S.weightBank out)
    change A.fresh S.degree S.r+(S.r+1)*A.page=H.origin at split
    omega
  have d:H.origin≤N.base:=by
    change H.origin≤H.origin+H.pos.size+H.depth.size+H.lead.size+2^S.levels+2^(S.levels+S.total)
    simp only [Nat.add_assoc, Nat.le_add_right]
  have e:N.base+N.size=C.origin:=rfl
  have f:C.origin≤C.stop:=C.before_planes.trans C.plane_le
  have i:C.stop=F.base:=rfl
  have j:F.base≤F.scratch:=by
    change F.base≤F.base+_+_+_
    simp only [Nat.add_assoc, Nat.le_add_right]
  have k:F.scratch≤S.endAddress base:=by
    change F.scratch≤F.scratch+_+_
    simp only [Nat.add_assoc, Nat.le_add_right]
  change A.fresh S.degree S.r-A.origin+(N.base-H.origin)+(N.base+N.size-N.base)+(C.stop-C.origin)+(F.scratch-F.base)≤_
  omega

theorem tariff (S : StencilBook) (X : Sources) (h w K base out f B g shared : ℕ) (rooms : Widths S h)
    (positive : 0<shared) (wide : 4*shared≤h) (hardware : w≤K*h) (batch : S.M=2^Stencil.laneExponent S.c shared h) :
    Padded.paidTime S X base out f B g*w ≤
      K*(10*S.pageCount+S.operationCount X)*
        (h+2*S.hosts*h+8*S.hosts*2^S.c*shared+2^(h/2)*h) := by
  let T:=10*S.pageCount+S.operationCount X
  have front:=S.paid_time X base out f B g
  have words:=S.literal_le_span X base out (32*Nat.clog 2 (2*S.degree)) (2^(f+1)*B)
  have span:=S.installed_span h base rooms
  have qty:1+S.rows≤S.units h:=(unit_bounds S.hosts S.rows (2^(h/2))).2.1
  have total:Padded.paidTime S X base out f B g≤T*S.units h:=by
    have num:=Nat.mul_le_mul_left 10 (show S.literalWords base out X (32*Nat.clog 2 (2*S.degree)) (2^(f+1)*B)≤S.pageCount*S.units h by omega)
    have both:=Nat.mul_le_mul_right (S.operationCount X) qty
    dsimp [T]
    nlinarith only [front,num,both]
  have count:S.rows*h≤S.hosts*h+8*S.hosts*2^S.c*shared:=by
    have ee:=(Stencil.pitch S.c S.r shared h).2.2
    rw [rows,batch,ee]
    simpa only [Stencil.laneExponent,one_mul] using
      (DescentGLPacked.charged S.hosts S.c shared h h 1 positive wide (by omega))
  have world:S.units h*h≤h+2*S.hosts*h+8*S.hosts*2^S.c*shared+2^(h/2)*h:=by
    dsimp [units];nlinarith only [count]
  calc _≤(T*S.units h)*(K*h):=Nat.mul_le_mul total hardware
       _=(K*T)*(S.units h*h):=by ring
       _≤_:=Nat.mul_le_mul_left _ world

end
end Hierarchy.DescentPlainTerminal.Suffix.StencilBook

end OAI
