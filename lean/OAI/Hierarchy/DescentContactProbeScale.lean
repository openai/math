import OAI.Hierarchy.DescentContactCostUnit
import OAI.Hierarchy.DescentContactPreROMPrice

namespace OAI
/-! # Direct-contact probes from the original host and its finite installed shapes -/
namespace Hierarchy.DescentContactPreROM.Layout
open DescentSIMDLookup DescentContactCostUnit
variable (A : Layout)

/-- The fixed probe, its shared selectors and one rounded bank of rows. -/
def stepFactor (N shapes : ℕ) := 1+N*2+1+(2*shapes+1)

private theorem step_scale (N b H G M h T shapes : ℕ)
    (rows : H*chunks G M≤ shapes*T) (lut : 2^(h/2)≤T) (paid : (b*N+b)*M≤h/2) :
    DescentContactProbeBook.step N b H G M≤ stepFactor N shapes*T := by
  have pos : 0<T:=(Nat.two_pow_pos _).trans_le lut
  have key : 2^((b*N+b)*M)≤1*T:=by simpa using (Nat.pow_le_pow_right (by decide : 0<2) paid).trans lut
  have min : b*N*M≤h/2 :=(Nat.mul_le_mul_right _ (Nat.le_add_right ..)).trans paid
  have narrow : 2^((b*N)*M)≤1*T:=by simpa using (Nat.pow_le_pow_right (by decide : 0<2) min).trans lut
  simpa only [stepFactor,DescentContactProbeBook.step,Nat.mul_one] using
    sum (sum (sum (fixed 1 pos) (left N (left 2 key))) narrow) (DescentContactCostUnit.span rows pos)

def staticFactor := A.viewCount*stepFactor 1 1+5*(2*A.shapes+1)+A.sockets*stepFactor 8 A.shapes

def clockFactor (oldLimit marker : ℕ) := clock A.oldFields 1 oldLimit+(12+10*A.staticFactor)+
  (4+A.jobs*(4+A.shapes*(2*marker+4)+(4+44*A.shapes)))

def nameFactor (oldLimit marker : ℕ) := names A.oldFields 1 oldLimit+15*(A.staticFactor+3)+
  (15+A.jobs*(102+4*marker))

theorem contact_scale (oldLimit marker h T : ℕ) (host : A.hosts≤T)
    (rows : A.hosts*chunks A.groups A.batch≤T) (lut : 2^(h/2)≤T)
    (data : (A.fieldBits*A.oldFields+A.fieldBits)*A.batch≤h/2)
    (view : (A.viewBits+A.viewBits)*A.batch≤h/2)
    (select : (A.fieldBits*8+A.fieldBits)*A.batch≤h/2) :
    A.clockBound oldLimit marker+7*A.size oldLimit marker≤
      (A.clockFactor oldLimit marker+7*A.nameFactor oldLimit marker)*T := by
  have pos : 0<T:=(Nat.two_pow_pos _).trans_le lut
  have single : A.hosts*chunks A.groups A.batch≤1*T:=by simpa using rows
  have shapes : A.hosts*A.shapes≤A.shapes*T:=by
    simpa [Nat.mul_comm] using Nat.mul_le_mul_left A.shapes host
  have shapeRows : A.rows≤A.shapes*T:=by
    simpa only [Layout.rows,Nat.mul_assoc,Nat.mul_left_comm] using Nat.mul_le_mul_left A.shapes rows
  have panel : DescentContactProbePitch.count A.hosts A.shapes A.groups A.batch≤A.shapes*T:=
    max_le shapes shapeRows
  have pitch : DescentContactProbePitch.extent A.hosts A.shapes A.groups A.batch≤(5*(2*A.shapes+1))*T:=
    left 5 (DescentContactCostUnit.span panel pos)
  have views:=step_scale 1 A.viewBits A.hosts A.groups A.batch h T 1 single lut (by simpa using view)
  have picks:=step_scale 8 A.fieldBits (A.hosts*A.shapes) A.groups A.batch h T A.shapes shapeRows lut select
  have banks : A.staticLength≤A.staticFactor*T:=sum (sum (left A.viewCount views) pitch) (left A.sockets picks)
  obtain ⟨speed,text⟩:=scan A.old A.oldFields A.fieldBits oldLimit h T rows lut data
  have c : A.clockBound oldLimit marker≤A.clockFactor oldLimit marker*T:=
    sum (sum speed (sum (fixed 12 pos) (left 10 banks))) (sum (fixed 4 pos) (left A.jobs
      (sum (sum (fixed 4 pos) (right (2*marker+4) shapeRows)) (sum (fixed 4 pos) (left 44 shapeRows)))))
  have n : A.size oldLimit marker≤A.nameFactor oldLimit marker*T:=
    sum (sum text (left 15 (sum banks (fixed 3 pos)))) (sum (fixed 15 pos)
      (left A.jobs (fixed (102+4*marker) pos)))
  exact sum c (left 7 n)

end Hierarchy.DescentContactPreROM.Layout

end OAI
