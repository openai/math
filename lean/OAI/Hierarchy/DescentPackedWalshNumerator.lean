import OAI.Hierarchy.DescentPackedWalshSquare
import OAI.Hierarchy.DescentPackedWalshPrice

namespace OAI
/-! # Packed autocorrelation and the zero-frequency sum from the same original load bank -/
namespace Hierarchy.DescentPackedWalsh
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {H u l b w : ℕ}
local notation "stages" => axesList u l
local notation "axisROM" => List.map axis stages
local notation "m" => u+l

theorem mounted_outside (root z : ℕ) (a : List (Axis u l)) (mem : Memory w) (H b : ℕ)
    (away : z<root ∨ root+a.length*span H u l b≤z) : mounted H b root a mem z=mem z := by
  rcases away with before|later
  · simp [mounted,Nat.not_le_of_lt before]
  · have sz:=show 0<span H u l b by unfold span;positivity
    have t : a.length≤(z-root)/span H u l b := (Nat.le_div_iff_mul_le sz).2 (by omega)
    simp [mounted,show root≤z by omega,List.getElem?_eq_none t]

theorem header_id (root : ℕ) (axes : List (Axis u l)) (src cur : Memory w) (H b : ℕ)
    (block : ∀i,root≤ i→i<root+axes.length*span H u l b→cur i=mounted H b root axes src i) :
    ∀i,cur i=mounted H b root axes cur i := by
  intro i
  by_cases active : root≤ i ∧ i<root+axes.length*span H u l b
  · have sz:=show 0<span H u l b by unfold span;positivity
    have t : (i-root)/span H u l b<axes.length := (Nat.div_lt_iff_lt_mul sz).2 (by omega)
    rw [block _ active.1 active.2]
    simp [mounted,active.1,t]
  · exact (mounted_outside root i axes cur H b (by omega)).symm

def sqOffset (first H u l : ℕ) := first+(u+l+1)*page H u

def numeratorCode (root first table H u l b w : ℕ) :=
  let top:=sqOffset first H u l
  let src : Bank:=⟨location first H u (u+l),rowBits H u⟩
  let tab : Bank:=⟨table,smallKey l b⟩
  ((code w root first H u l b 0 (axesList u l)).seq (scan w top (H*2^u) (squareExpr src tab))).seq
    (code w root top H u l b 0 (axesList u l))

def numeratorTicks (H u l : ℕ) := duration H u (u+l)+(4+28*(H*2^u))+duration H u (u+l)

def numeratorMem (root first table H u l b : ℕ) (src : Memory w) :=
  let top:=sqOffset first H u l
  let one:=after root first H u l b 0 (axesList u l) src
  let B : Bank:=⟨location first H u (u+l),rowBits H u⟩
  let D : Bank:=⟨table,smallKey l b⟩
  after root top H u l b 0 (axesList u l) (image top (H*2^u) (squareExpr B D) one)

def initial (root table H u l b : ℕ) (src : Memory w) : Memory w :=
  mounted H b root ((axesList u l).map axis) (squareROM table src b l)

theorem both (root first table : ℕ) (src start : Memory w) (x : Fin H→Cube m→Cell b)
    (tables : root+m*span H u l b≤table) (shelfEnds : table+2^(smallKey l b)≤first)
    (limit : sqOffset first H u l+(m+1)*page H u<2^w)
    (fixed : ∀j<first,start j=initial root table H u l b src j)
    (old : Installed first (fun v=>shaped (x v)) start) :
    let dst:=numeratorMem root first table H u l b start
    (numeratorCode root first table H u l b w).Exec start dst (numeratorTicks H u l) ∧
      Installed (location first H u m) (fun v=>shaped (DescentWalshPhysical.transform (x v))) dst ∧
      Installed (location (sqOffset first H u l) H u m) (fun v=>shaped (DescentWalshPhysical.numerator (x v))) dst ∧
      (∀j<first,dst j=start j) := by
  let top:=sqOffset first H u l
  let B : Bank:=⟨location first H u m,rowBits H u⟩
  let D : Bank:=⟨table,smallKey l b⟩
  let one:=after root first H u l b 0 stages start
  let two:=image top (H*2^u) (squareExpr B D) one
  have P : 0<page H u := Nat.two_pow_pos (rowBits H u)
  have count:=rows_le H u
  have plus : (m+1)*page H u=m*page H u+page H u := Nat.succ_mul _ _
  have topEq : top=first+(m+1)*page H u:=rfl
  have prior : first≤top:=by omega
  have fit1 : first+(m+1)*page H u<2^w:=by omega
  have tableBefore : table≤first := (Nat.le_add_right table _).trans shelfEnds
  have headerBefore : root+m*span H u l b≤first := tables.trans tableBefore
  obtain ⟨r1,w1,lo1,hi1⟩:=full root first start (squareROM table src b l) x headerBefore fit1 fixed old
  have bf : B.Fits w top := by
    change 0<page H u ∧ page H u<2^w ∧ first+m*page H u+page H u≤top
    have low := Nat.zero_le (m*page H u)
    exact ⟨P,by omega,by omega⟩
  have df : D.Fits w top:=by
    change 0<2^(smallKey l b) ∧ 2^(smallKey l b)<2^w ∧ table+2^(smallKey l b)≤top
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  have sub : H*2^u≤B.size:=count
  have roomSq : top+H*2^u<2^w:=by
    have a:=Nat.mul_le_mul_right (page H u) (show 1≤ m+1 by omega)
    omega
  have tab (i : Cell (smallKey l b)) : one (table+i.val)=((square b l i).val:Word w) := by
    have under : table+i.val<first := (Nat.add_lt_add_left i.isLt _).trans_le shelfEnds
    dsimp only [one]
    rw [lo1 _ under,fixed _ under,initial,mounted_outside, squareROM_at]
    right
    simpa [axesList] using tables.trans (Nat.le_add_right table i.val)
  obtain ⟨r2,w2,lo2,hi2⟩:=squares B D top one (fun v=>shaped (DescentWalshPhysical.transform (x v))) bf df sub le_rfl roomSq w1 tab
  have staticTwo:=header_id root axisROM (squareROM table src b l) two H b (by
    intro j vlo vhi
    have under:j<first:=by simp [axesList] at vhi;omega
    exact (lo2 _ (under.trans_le prior)).trans ((lo1 _ under).trans (fixed _ under)))
  obtain ⟨r3,w3,lo3,hi3⟩:=full root top two two
    (fun v a=>(DescentWalshPhysical.transform (x v) a)*(DescentWalshPhysical.transform (x v) a)) (headerBefore.trans prior) limit
    (fun j _=>staticTwo j) w2
  refine ⟨Procedure.Exec.then (Procedure.Exec.then r1 r2) r3,?_,w3,?_⟩
  · intro v p
    have small : location first H u m+(row v p).val<top := by
      have bound:=(row v p).isLt.trans_le count
      unfold location;omega
    exact (lo3 _ small).trans ((lo2 _ small).trans (w1 v p))
  · intro j before
    exact (lo3 _ (before.trans_le prior)).trans ((lo2 _ (before.trans_le prior)).trans (lo1 _ before))

end
end Hierarchy.DescentPackedWalsh

end OAI
