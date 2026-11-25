import OAI.Hierarchy.DescentPackedSingletonDepth
import OAI.Hierarchy.DescentPackedWalshRead

namespace OAI
/-! # Real one-way site transform and singleton depth on the same execution -/
namespace Hierarchy.DescentPackedSingletonDepth
open DescentSIMDLookup DescentPackedWalsh DescentGL DescentColonies DescentBaseProfile ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b w : ℕ}
local notation "k" => u+l
local notation "Q" => DescentWalshPhysical.coordinates

def transformBank (first H u l : ℕ) : Bank := ⟨location first H u (u+l),rowBits H u⟩

theorem input_frame (root first H u l b : ℕ) (seq : List (Fin (u+l))) (z : ℕ) (mem : Memory w)
    (a : ℕ) (low : a<first+page H u) : after root first H u l b z seq mem a=mem a := by
  induction seq generalizing z mem with
  | nil=>rfl
  | cons g gs ih=>
    unfold DescentPackedWalsh.after
    rw [ih]
    apply ProtocolRAMGeneratedWrite.frame_image
    apply Or.inl
    unfold outPage
    have pages : page H u ≤ (z+1)*page H u := by
      simpa only [Nat.one_mul] using Nat.mul_le_mul_right (page H u) (Nat.succ_le_succ (Nat.zero_le z))
    exact low.trans_le (Nat.add_le_add_left pages first)

theorem forward (root first : ℕ) (src mem : Memory w) (rows : Native.Rows H (2^k))
    (bound : ∀v,Native.totalWeight rows v<2^b) (payload : smallKey l b≤w)
    (space : root+k*span H u l b≤first) (room : first+(k+1)*page H u<2^w)
    (pins : ∀i<first,mem i=mounted H b root ((axesList u l).map axis) src i)
    (old : Installed first (fun v=>shaped (fun z=>((rows[v.val])[(address k ((Q _).symm z)).val]:Cell b))) mem) :
    let mid:=after root first H u l b 0 (axesList u l) mem
    (code w root first H u l b 0 (axesList u l)).Exec mem mid (duration H u k) ∧
      (∀v:Fin H,digit b (ordinal l (fun _=>false)).val
        (mid ((transformBank first H u l).base+(row v (fun _ : Fin u=>false)).val)).val=
          ∑i : Bits k,(rows[v.val])[(address k i).val]) ∧
      (∀z<first+page H u,mid z=mem z) ∧ ∀z,first+(k+1)*page H u≤z→mid z=mem z := by
  intro mid
  let x (v : Fin H) (z : Cube k):ℕ:=(rows[v.val])[(address k ((Q _).symm z)).val]
  obtain ⟨ran,reads,low,high⟩:=full root first mem src (fun v z=>(x v z:Cell b)) space room pins old
  refine ⟨ran,?_,input_frame root first H u l b _ _ mem,high⟩
  intro v
  change digit _ _ (mid (location first H u k+(row v (fun _ : Fin u=>false)).val)).val=_
  rw [reads.bitValue payload]
  have zero : addr (fun _ : Fin u=>false) (fun _ : Fin l=>false)=(fun _=>false) := by
    funext i
    change Sum.elim (fun _ : Fin u => false) (fun _ : Fin l => false) (finSumFinEquiv.symm i) = false
    cases finSumFinEquiv.symm i <;> rfl
  simp only [shaped,zero,DescentWalshPhysical.transform_zero]
  have total : (∑z:Cube k,x v z)=∑i:Bits k,(rows[v.val])[(address k i).val] := by
    rw [←(Q k).sum_comp];simp [x]
  have bounded : (∑z:Cube k,x v z)<2^b:=by
    rw [total]
    calc
      _ = ∑ j : Fin (2^k), (rows[v.val])[j.val] :=
        (address k).sum_comp (fun j : Fin (2^k) => (rows[v.val])[j.val])
      _ = Native.totalWeight rows v := (Native.totalWeight_eq rows v).symm
      _ < 2^b := bound v
  rw [←Nat.cast_sum,Fin.val_cast_of_lt bounded,total]

def clocks (H u l Δ r f B totals edges scratch w : ℕ) (smoothing : ℕ := Δ) :=
  let L:=layout H Δ (u+l) r f B totals edges scratch smoothing
  duration H u (u+l)+(4+H*32+L.clocks w L.M)

theorem time (H u l Δ r f B totals edges scratch w : ℕ) :
    let L:=layout H Δ (u+l) r f B totals edges scratch
    clocks H u l Δ r f B totals edges scratch w≤duration H u (u+l)+(4+H*32+L.baseBill+L.M*L.stepBill) := by
  intro L
  change duration H u (u+l) + (4+H*32+L.clocks w L.M) ≤ _
  have ht:=L.time w L.M
  omega

theorem depths_at (root first : ℕ) (ptr : Bank) (Δ smoothing r f B totals edges scratch : ℕ)
    (src mem : Memory w) (rows : Native.Rows H (2^k)) (ns : Native.Neighbors H)
    (bound : ∀v,Native.totalWeight rows v<2^b) (payload : smallKey l b≤w)
    (space : root+k*span H u l b≤first) (window : first+(k+1)*page H u≤totals) (endAddr : totals+H<2^w)
    (pins : ∀i<first,mem i=mounted H b root ((axesList u l).map axis) src i)
    (old : Installed first (fun v=>shaped (fun z=>((rows[v.val])[(address k ((Q _).symm z)).val]:Cell b))) mem)
    (safe : (layout H Δ k r f B totals edges scratch smoothing).Fits w) (pfit : ptr.Fits w totals)
    (dfit : (transformBank first H u l).Fits w totals) (pn : H≤ptr.size) (wide : b≤w)
    (ptrLow : ptr.base+H≤first) (edgeLow : edges+H*Δ≤first)
    (pointers : ∀v:Fin H,mem (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w))
    (neighbors : ∀v : Fin H,∀s : Fin Δ,mem (edges+v.val*Δ+s.val)=(DepthRAM.number ((ns[v.val])[s.val]?):Word w))
    (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) :
    let D:=transformBank first H u l
    let L:=layout H Δ k r f B totals edges scratch smoothing
    ∃out : Memory w,((code w root first H u l b 0 (axesList u l)).seq ((tap D ptr b totals H w).seq (L.cpu w L.M))).Exec
      mem out (clocks H u l Δ r f B totals edges scratch w smoothing) ∧
      (∀v : Fin H,out (L.base (L.M+1)+v.val)=(measuredDepth ns rows smoothing r f B v:Word w)) ∧ ∀a<first+page H u,out a=mem a := by
  intro D L
  have more : page H u ≤ (k+1)*page H u := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right (page H u) (Nat.succ_le_succ (Nat.zero_le (u+l)))
  have lower : first+page H u ≤ totals := (Nat.add_le_add_left more first).trans window
  have tiny:first≤first+page H u:=Nat.le_add_right ..
  let mid:=after root first H u l b 0 (axesList u l) mem
  obtain ⟨ran,mode,saved,_⟩:=forward root first src mem rows bound payload space (by omega) pins old
  have geo (v:Fin H):mid (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w):=
    (saved _ ((Nat.add_lt_add_left v.isLt _).trans_le (ptrLow.trans tiny))).trans (pointers v)
  have ends_ (v:Fin H) (s:Fin Δ):mid (edges+v.val*Δ+s.val)=(DepthRAM.number ((ns[v.val])[s.val]?):Word w):=by
    have toEnd:=Nat.mul_le_mul_right Δ v.isLt;rw [Nat.succ_mul] at toEnd
    exact (saved _ (by have:=s.isLt;omega)).trans (neighbors v s)
  obtain ⟨done,read,preserve⟩ :=from_mode_at (b:=b) D ptr Δ smoothing r f B totals edges scratch mid rows ns safe pfit dfit pn
    (show H*2^u≤D.size from rows_le H u) wide endAddr (edgeLow.trans (tiny.trans lower)) geo mode ends_
    (fun v=>(bound v).trans_le (Nat.pow_le_pow_right (by decide) wide)) degree
  exact ⟨_,Procedure.Exec.then ran done,read,fun a ha=>(preserve a (ha.trans_le lower)).trans (saved a ha)⟩

theorem depths (root first : ℕ) (ptr : Bank) (Δ r f B totals edges scratch : ℕ)
    (src mem : Memory w) (rows : Native.Rows H (2^k)) (ns : Native.Neighbors H)
    (bound : ∀v,Native.totalWeight rows v<2^b) (payload : smallKey l b≤w)
    (space : root+k*span H u l b≤first) (window : first+(k+1)*page H u≤totals) (endAddr : totals+H<2^w)
    (pins : ∀i<first,mem i=mounted H b root ((axesList u l).map axis) src i)
    (old : Installed first (fun v=>shaped (fun z=>((rows[v.val])[(address k ((Q _).symm z)).val]:Cell b))) mem)
    (safe : (layout H Δ k r f B totals edges scratch).Fits w) (pfit : ptr.Fits w totals)
    (dfit : (transformBank first H u l).Fits w totals) (pn : H≤ptr.size) (wide : b≤w)
    (ptrLow : ptr.base+H≤first) (edgeLow : edges+H*Δ≤first)
    (pointers : ∀v:Fin H,mem (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w))
    (neighbors : ∀v : Fin H,∀s : Fin Δ,mem (edges+v.val*Δ+s.val)=(DepthRAM.number ((ns[v.val])[s.val]?):Word w))
    (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) :
    let D:=transformBank first H u l
    let L:=layout H Δ k r f B totals edges scratch
    ∃out : Memory w,((code w root first H u l b 0 (axesList u l)).seq ((tap D ptr b totals H w).seq (L.cpu w L.M))).Exec
      mem out (clocks H u l Δ r f B totals edges scratch w) ∧
      (∀v : Fin H,out (L.base (L.M+1)+v.val)=(measuredDepth ns rows Δ r f B v:Word w)) ∧ ∀a<first+page H u,out a=mem a :=
  depths_at root first ptr Δ Δ r f B totals edges scratch src mem rows ns bound payload space window endAddr pins old safe pfit dfit pn wide ptrLow edgeLow pointers neighbors degree

end
end Hierarchy.DescentPackedSingletonDepth

end OAI
