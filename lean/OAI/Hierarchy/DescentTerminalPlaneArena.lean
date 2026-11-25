import OAI.Hierarchy.DescentTerminalAddressBanks
import OAI.Hierarchy.DescentTerminalDataPlane
import OAI.Hierarchy.DescentTerminalEmitterAllocation

namespace OAI
/-! # Compact real addresses for the terminal flights and the two width-header scans -/

namespace Hierarchy.DescentTerminalDataPlane.Arena
open DescentTerminalDataPlane DescentTerminalDenseHeaderRAM DescentExteriorShelf Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
noncomputable section

variable (s : Shape) (origin : ℕ)
local notation "N" => s.exteriors*2^(s.headBits+s.restBits)
local notation "H" => span s.headBits s.restBits s.bitLanes s.exteriors

theorem room (n : ℕ) : n<size n := Nat.lt_of_succ_le (Nat.le_pow_clog (by decide) _)
theorem cost (n : ℕ) : size n≤2*(n+1) := by
  cases h:Nat.clog 2 (n+1) with
  | zero=>simp [size,h];omega
  | succ k=>
    have prior : k<Nat.clog 2 (n+1):=by omega
    have prev:=Nat.pow_lt_of_lt_clog prior
    simp only [size,h,pow_succ];omega

theorem width_room {bw : ℕ} (base : ℕ) (src : Fin 5→Bank) (earlier : ∀i,(src i).base+(src i).size≤base)
    (end_ : base+4*size s.headerRows<2^bw) : Fits (header s base src) bw s.headerRows := by
  let n:=s.headerRows
  change base+4*size n<2^bw at end_
  have span : 0<size n:=Nat.two_pow_pos _
  have capacity:=room n
  have older (j:Fin 5) : (src j).Fits bw base := ⟨Nat.two_pow_pos _,by have:=earlier j;omega,earlier j⟩
  have next (i:ℕ) (ok:i<3) : (column base n i).Fits bw (column base n (i+1)).base := by
    change 0<size n ∧ size n<2^bw ∧ base+i*size n+size n≤base+(i+1)*size n
    rw [Nat.succ_mul];exact ⟨span,by omega,by omega⟩
  refine ⟨?_,next 0 (by decide),next 1 (by decide),next 2 (by decide),capacity.le,capacity.le,capacity.le,?_⟩
  · intro bank mem
    simp only [header,column,buy,Nat.zero_mul,Nat.add_zero,List.mem_cons,List.not_mem_nil,or_false] at mem ⊢
    rcases mem with rfl|rfl|rfl|rfl|rfl <;> exact older _
  · change (base+3*size n)+n<2^bw
    omega

theorem fits {bw : ℕ} (pub : Fin 6→Bank) (cable outside : Fin 5→Bank) (candidate : Bank)
    (oldPub : ∀i,(pub i).base+(pub i).size≤post s origin)
    (oldWire : ∀i,(cable i).base+(cable i).size≤headerBase s origin)
    (oldExt : ∀i,(outside i).base+(outside i).size≤ second s origin)
    (oldPay : candidate.base+candidate.size≤post s origin) (end_ : finish s origin<2^bw) :
    DescentTerminalDataPlane.Room s (plane s origin pub cable candidate) bw ∧
      Fits (header s (second s origin) outside) bw s.headerRows := by
  let P:=size (s.publicRows+2)
  let R:=size (s.rawRows+2+(s.publicRows+2))
  let Z:=size s.headerRows
  have clock : post s origin+P+R+4*Z+4*Z<2^bw:=end_
  have positive : 0<H:=Nat.two_pow_pos _
  have countN : N≤H:=row_room ..
  have publicN : s.publicRows+2<P:=room _
  have readable (i:Fin 6) : (pub i).Fits bw (post s origin) :=
    ⟨Nat.two_pow_pos _,by have:=oldPub i;omega,oldPub i⟩
  have actual : (publicTapes s origin pub).phase.Fits bw (post s origin) := by
    change 0<H ∧ H<2^bw ∧ (origin+18*H+2*N)+H≤origin+24*H
    dsimp [post] at clock
    omega
  have cableRoom : headerBase s origin+4*Z<2^bw := by
    change post s origin+P+R+4*Z<2^bw
    omega
  refine ⟨⟨?_,?_,?_,?_,?_,?_,width_room s _ cable oldWire cableRoom⟩,
    width_room s _ outside oldExt end_⟩
  · change post s origin<2^bw;omega
  · intro b mem
    simp only [plane,publicTapes,DescentTerminalPublicWordRAM.all,List.mem_cons,List.not_mem_nil,or_false] at mem
    rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals first | exact readable _ | exact actual
  · change post s origin+(s.publicRows+2)<2^bw;omega
  · change candidate.Fits bw (post s origin+P)
    exact ⟨Nat.two_pow_pos _,by omega,by omega⟩
  · change 0<P ∧ P<2^bw ∧ post s origin+P≤post s origin+P
    exact ⟨Nat.two_pow_pos _,by omega,le_rfl⟩
  · change post s origin+P+R<2^bw;omega

theorem price {h : ℕ} (half : tableBits s.headBits s.restBits s.bitLanes≤h/2) :
    finish s origin≤origin+64*(N+2^(h/2)+s.rawRows+s.publicRows+s.headerRows+1) := by
  have span:=span_price s.headBits s.restBits s.bitLanes s.exteriors half
  have pub:=cost (s.publicRows+2)
  have data:=cost (s.rawRows+2+(s.publicRows+2))
  have headers:=cost s.headerRows
  have tablePos : 0 < 2^(h/2) := Nat.two_pow_pos _
  change H≤2*N+1+2^(h/2) at span
  change origin+24*H+size (s.publicRows+2)+size (s.rawRows+2+(s.publicRows+2))+
    4*size s.headerRows+4*size s.headerRows≤_
  omega

end
end Hierarchy.DescentTerminalDataPlane.Arena

end OAI
