import OAI.Hierarchy.DescentResetWalshCutoff
import OAI.Hierarchy.DescentBaseDepthRAM
import OAI.Hierarchy.DescentBaseDepthBill
import OAI.Hierarchy.DescentMeasuredBaseGeometry

namespace OAI
/-! # Feed the true zero Walsh mode to the native depth program using one weight word per site -/
namespace Hierarchy.DescentPackedSingletonDepth
open DescentSIMDLookup DescentGL DescentColonies DescentBaseProfile DescentPackedWalsh ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {H u l b w n : ℕ}

def singleton (total : Fin H→ℕ) : Native.Rows H 1 := Vector.ofFn fun v=>Vector.ofFn fun _=>total v

theorem total_one (total : Fin H→ℕ) (v : Fin H) : Native.totalWeight (singleton total) v=total v := by
  simp [Native.totalWeight_eq,singleton]

theorem same_profile (ns : Native.Neighbors H) (rows : Native.Rows H n) (S g lo M : ℕ) :
    Native.profile ns (singleton (Native.totalWeight rows)) S g lo M=Native.profile ns rows S g lo M := by
  simp only [Native.profile,Native.seeds,total_one]

def layout (H Δ k r f B totals edges scratch : ℕ) (smoothing : ℕ := Δ) : DepthRAM.Layout where
  H:=H
  N:=1
  Δ:=Δ
  hostBits:=Nat.clog 2 H
  degreeBits:=Nat.clog 2 Δ
  weights:=totals
  edges:=edges
  start:=scratch
  S:=2^f*B
  g:=decayExponent smoothing
  lo:=k-r
  M:=k-f

local notation "k" => u+l

def expr (data ptr : Bank) (b : ℕ) := firstTotal data (.lookup ptr .row) b

def tap (data ptr : Bank) (b start H w : ℕ) := scan w start H (expr data ptr b)

def runMem (data ptr : Bank) (b start H : ℕ) (mem : Memory w) := image start H (expr data ptr b) mem

theorem tap_cost (data ptr : Bank) (b : ℕ) : (expr data ptr b).work=14 := rfl

theorem tap_read (data ptr : Bank) (totals : ℕ) (mem : Memory w) (rows : Native.Rows H (2^k))
    (pfit : ptr.Fits w totals) (dfit : data.Fits w totals) (pn : H≤ptr.size) (dn : H*2^u≤data.size)
    (wide : b≤w) (pointers : ∀v:Fin H,mem (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w))
    (mode : ∀v:Fin H,digit b (ordinal l (fun _=>false)).val (mem (data.base+(row v (fun _ : Fin u=>false)).val)).val=
      ∑x : Bits k,(rows[v.val])[(address k x).val]) (v : Fin H) :
    runMem data ptr b totals H mem (totals+v.val)=(Native.totalWeight rows v:Word w) := by
  have addressRead : (Expr.lookup ptr .row).eval mem (v.val:Word w)=((row v (fun _ : Fin u=>false)).val:Word w) :=
    (DescentPackedZip.bank_read _ _ (v.isLt.trans_le pn) pfit).trans (pointers v)
  have get:=firstTotal_read data _ mem (v.val:Word w) v dfit dn wide addressRead
    (fun j=>(rows[v.val])[j.val]) (mode v)
  rw [runMem,ProtocolRAMGeneratedWrite.read_image,expr,get,Native.totalWeight_eq]

theorem from_mode_at (data ptr : Bank) (Δ smoothing r f B totals edges scratch : ℕ) (mem : Memory w)
    (rows : Native.Rows H (2^k)) (ns : Native.Neighbors H)
    (safe : (layout H Δ k r f B totals edges scratch smoothing).Fits w)
    (pfit : ptr.Fits w totals) (dfit : data.Fits w totals) (pn : H≤ptr.size) (dn : H*2^u≤data.size)
    (wide : b≤w) (output : totals+H<2^w) (earlier : edges+H*Δ≤totals)
    (pointers : ∀v:Fin H,mem (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w))
    (mode : ∀v:Fin H,digit b (ordinal l (fun _=>false)).val (mem (data.base+(row v (fun _ : Fin u=>false)).val)).val=
      ∑x : Bits k,(rows[v.val])[(address k x).val])
    (neighbors : ∀v : Fin H,∀s : Fin Δ,mem (edges+v.val*Δ+s.val)=(DepthRAM.number ((ns[v.val])[s.val]?):Word w))
    (fits : ∀v,Native.totalWeight rows v<2^w) (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) :
    let L:=layout H Δ k r f B totals edges scratch smoothing
    let init:=runMem data ptr b totals H mem
    let dst:=L.output init L.M
    ((tap data ptr b totals H w).seq (L.cpu w L.M)).Exec mem dst (4+H*32+L.clocks w L.M) ∧
      (∀v : Fin H,dst (L.base (L.M+1)+v.val)=(measuredDepth ns rows smoothing r f B v:Word w)) ∧
      ∀a<totals,dst a=mem a := by
  intro L init dst
  have first : (tap data ptr b totals H w).Exec mem init (4+H*32) := by
    have valid : (expr data ptr b).Fits w totals:=by simp [expr,firstTotal,Expr.Fits,dfit,pfit]
    change (scan w totals H (expr data ptr b)).Exec mem (image totals H (expr data ptr b) mem) (4+H*32)
    have ticks : 32=2*(expr data ptr b).work+4 := by rw [tap_cost]
    rw [ticks]
    intro programs registers slots
    exact @ProtocolRAM.scan_exec w totals H (expr data ptr b) mem valid output programs registers slots
  let one:=singleton (Native.totalWeight rows)
  have source : L.Source ns one init := by
    constructor
    · change ∀ v : Fin H, ∀ j : Fin 1, init (totals + v.val*1 + j.val) =
          (((singleton (Native.totalWeight rows))[v.val])[j.val] : Word w)
      intro v j
      obtain ⟨i, hi⟩ := v
      simpa [init, singleton, Fin.eq_zero j] using
        tap_read data ptr totals mem rows pfit dfit pn dn wide pointers mode (⟨i, hi⟩ : Fin H)
    · change ∀ v : Fin H, ∀ s : Fin Δ, init (edges + v.val*Δ + s.val) =
          (DepthRAM.number ((ns[v.val])[s.val]?) : Word w)
      intro v s
      have bound := Nat.mul_le_mul_right Δ v.isLt
      rw [Nat.succ_mul] at bound
      have lt : edges + v.val*Δ + s.val < totals := by have := s.isLt; omega
      exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl lt)).trans (neighbors v s)
  have singlesFit : ∀ v : Fin H, Native.totalWeight (singleton (Native.totalWeight rows)) v < 2^w := by
    intro v
    rw [total_one]
    exact fits v
  obtain ⟨ran,read⟩ := L.run ns one init safe source singlesFit degree
  refine ⟨Procedure.Exec.then first ran,?_,?_⟩
  · intro v
    simpa only [dst,one,same_profile,L,layout,measuredDepth] using read v
  · intro a ha
    have before : totals≤ scratch:=by have :=safe.weights;change totals+H*1≤ scratch at this;omega
    exact (L.static init L.M a (ha.trans_le before)).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl ha))

theorem from_mode (data ptr : Bank) (Δ r f B totals edges scratch : ℕ) (mem : Memory w)
    (rows : Native.Rows H (2^k)) (ns : Native.Neighbors H)
    (safe : (layout H Δ k r f B totals edges scratch).Fits w)
    (pfit : ptr.Fits w totals) (dfit : data.Fits w totals) (pn : H≤ptr.size) (dn : H*2^u≤data.size)
    (wide : b≤w) (output : totals+H<2^w) (earlier : edges+H*Δ≤totals)
    (pointers : ∀v:Fin H,mem (ptr.base+v.val)=((row v (fun _ : Fin u=>false)).val:Word w))
    (mode : ∀v:Fin H,digit b (ordinal l (fun _=>false)).val (mem (data.base+(row v (fun _ : Fin u=>false)).val)).val=
      ∑x : Bits k,(rows[v.val])[(address k x).val])
    (neighbors : ∀v : Fin H,∀s : Fin Δ,mem (edges+v.val*Δ+s.val)=(DepthRAM.number ((ns[v.val])[s.val]?):Word w))
    (fits : ∀v,Native.totalWeight rows v<2^w) (degree : ∀v : Fin H,(ns[v.val]).length≤Δ) :
    let L:=layout H Δ k r f B totals edges scratch
    let init:=runMem data ptr b totals H mem
    let dst:=L.output init L.M
    ((tap data ptr b totals H w).seq (L.cpu w L.M)).Exec mem dst (4+H*32+L.clocks w L.M) ∧
      (∀v : Fin H,dst (L.base (L.M+1)+v.val)=(measuredDepth ns rows Δ r f B v:Word w)) ∧
      ∀a<totals,dst a=mem a :=
  from_mode_at data ptr Δ Δ r f B totals edges scratch mem rows ns safe pfit dfit pn dn wide output earlier pointers mode neighbors fits degree

end
end Hierarchy.DescentPackedSingletonDepth

end OAI
