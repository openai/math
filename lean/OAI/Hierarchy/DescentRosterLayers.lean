import OAI.Hierarchy.DescentColonyDynamicSplit
import OAI.Hierarchy.DescentColonyLayerRAM
import OAI.Hierarchy.DescentColonyCandidateHardware

namespace OAI
/-! # Executing all split layers using stored neighbor ordinals -/

namespace Hierarchy.DescentColonies.RosterLayers
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM.PhysicalProcedure
open DescentGL
open scoped Fin.CommRing
variable {ℓ Δ k w : ℕ}

/-- Every directory cell lies before the next bank. This includes empty rows. -/
theorem slot_before {v : Fin (2^ℓ)} {s : Fin Δ} (adj : ℕ) :
    adj+v.val*Δ+s.val<adj+(2^ℓ)*Δ := by
  have h := Nat.mul_le_mul_right Δ v.isLt
  rw [Nat.succ_mul] at h
  omega

theorem saved {adj base : ℕ} {rs : DynamicSplit.Roster ℓ Δ} {m m' : Memory w}
    (read : DynamicSplit.Stored adj rs m) (sep : adj+(2^ℓ)*Δ≤base)
    (frame : ∀x<base,m' x=m x) : DynamicSplit.Stored adj rs m' :=
  fun v s=>(frame _ ((slot_before (v:=v) (s:=s) adj).trans_le sep)).trans (read v s)

private def siteOrder (N d : ℕ) : (i : ℕ)→i≤N→List (ℕ×Fin N)
  | 0,_=>[]
  | i+1,hi=>siteOrder N d i (by omega)++[(d,⟨i,hi⟩)]

private def order (N : ℕ) : ℕ→List (ℕ×Fin N)
  | 0=>[]
  | s+1=>order N s++siteOrder N s N le_rfl

private theorem site_map {N : ℕ} (c : LayerRAM.Layout N) (s i : ℕ) (hi : i≤N) :
    (siteOrder N s i hi).map (fun p=>c.pass p.1 p.2)=c.sites s i hi := by
  induction i with
  | zero=>rfl
  | succ i ih=>simp [siteOrder,LayerRAM.Layout.sites,ih]

private theorem all_map {N : ℕ} (c : LayerRAM.Layout N) (s : ℕ) :
    (order N s).map (fun p=>c.pass p.1 p.2)=c.stages s := by
  induction s with
  | zero=>rfl
  | succ s ih=>simp [order,LayerRAM.Layout.stages,ih,site_map]

private theorem site_mem {N s i : ℕ} {hi : i≤N} {p : ℕ×Fin N} (mem : p∈siteOrder N s i hi) :
    p.1=s := by
  induction i with
  | zero=>simp [siteOrder] at mem
  | succ i ih=>
    simp only [siteOrder,List.mem_append,List.mem_singleton] at mem
    rcases mem with before|rfl
    · exact ih before
    · rfl

private theorem order_mem {N s : ℕ} {p : ℕ×Fin N} (mem : p∈order N s) : p.1<s := by
  induction s with
  | zero=>simp [order] at mem
  | succ s ih=>
    rcases List.mem_append.mp mem with old|current
    · exact (ih old).trans (Nat.lt_succ_self _)
    · exact (site_mem current) ▸ Nat.lt_succ_self s

private theorem site_len (N s i : ℕ) (hi : i≤N) : (siteOrder N s i hi).length=i := by
  induction i with
  | zero=>rfl
  | succ i ih=>simp [siteOrder,ih]

private theorem order_len (N s : ℕ) : (order N s).length=s*N := by
  induction s with
  | zero=>simp [order]
  | succ s ih=>simp [order,ih,site_len,Nat.succ_mul]

def prev (ℓ k base stage depth : ℕ) : Option ℕ :=
  if depth<k ∧ k-1-depth<stage then some (base+(k-1-depth)*2^ℓ*2^k) else none

private theorem previous (c : LayerRAM.Layout (2^ℓ)) (s z : ℕ) (v : Fin (2^ℓ)) :
    DynamicSplit.virtualBase (prev ℓ c.k c.base s) c.k z v=c.previous s z v := by
  unfold DynamicSplit.virtualBase prev LayerRAM.Layout.previous
  split <;> simp [*,LayerRAM.address,Nat.add_mul,Nat.add_assoc]

def pass (ℓ Δ k adj base : ℕ) (loadBase : Fin (2^ℓ)→ℕ) (D cap : ℕ) (p : ℕ×Fin (2^ℓ)) : Pass :=
  ⟨base+(p.1*(2^ℓ)+p.2.val)*2^k,2^k,
    DynamicSplit.expr k ℓ Δ adj loadBase (prev ℓ k base p.1) D cap (k-1-p.1) p.2⟩

def passes (ℓ Δ k adj base : ℕ) (loadBase : Fin (2^ℓ)→ℕ) (D cap : ℕ) : List Pass :=
  (order (2^ℓ) k).map (pass ℓ Δ k adj base loadBase D cap)

private theorem pass_frame (c : LayerRAM.Layout (2^ℓ)) (p : ℕ×Fin (2^ℓ)) (m : Memory w) {x : ℕ} (lo : x<c.base) :
    (c.pass p.1 p.2).apply m x=m x :=
  ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl (lo.trans_le (Nat.le_add_right ..)))

private theorem same_image {out n : ℕ} {a b : Expr} {m : Memory w}
    (eqn : ∀i : Fin n,a.eval m (i.val:Word w)=b.eval m (i.val:Word w)) :
    image out n a m=image out n b m := by
  funext z
  by_cases hit : out≤z ∧ z<out+n
  · let i : Fin n := ⟨z-out,by omega⟩
    have zi : z=out+i.val := by dsimp [i];omega
    rw [zi,ProtocolRAMGeneratedWrite.read_image,ProtocolRAMGeneratedWrite.read_image,eqn]
  · have off : z<out ∨ out+n≤z := by omega
    exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ off).trans
      (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ off).symm

private theorem row_same (adj : ℕ) (rs : DynamicSplit.Roster ℓ Δ) (c : LayerRAM.Layout (2^ℓ))
    (inc : c.incoming=DynamicSplit.incoming rs) (p : ℕ×Fin (2^ℓ)) (m : Memory w)
    (data : DynamicSplit.Stored adj rs m) (room : 2^(ℓ+c.k)<2^w) :
    (pass ℓ Δ c.k adj c.base c.loadBase c.D c.cap p).apply m=(c.pass p.1 p.2).apply m := by
  apply same_image
  intro x
  have read := DynamicSplit.read_eq rs adj c.loadBase (prev ℓ c.k c.base p.1)
    c.D c.cap (c.k-1-p.1) p.2 m data room x
  simpa only [pass,LayerRAM.Layout.pass,inc,show
    DynamicSplit.virtualBase (prev ℓ c.k c.base p.1) c.k = c.previous p.1 from
      funext fun z=>funext fun v=>previous c p.1 z v] using read

private theorem list_same (adj : ℕ) (rs : DynamicSplit.Roster ℓ Δ) (c : LayerRAM.Layout (2^ℓ))
    (inc : c.incoming=DynamicSplit.incoming rs) (room : 2^(ℓ+c.k)<2^w)
    (sep : adj+(2^ℓ)*Δ≤c.base) (ps : List (ℕ×Fin (2^ℓ))) (m : Memory w) (data : DynamicSplit.Stored adj rs m) :
    result (ps.map (pass ℓ Δ c.k adj c.base c.loadBase c.D c.cap)) m =
    result (ps.map (fun p=>c.pass p.1 p.2)) m := by
  induction ps generalizing m with
  | nil=>rfl
  | cons p ps ih=>
    simp only [List.map_cons,result]
    rw [row_same adj rs c inc p m data room]
    exact ih _ (saved data sep (fun x hx=>pass_frame c p m hx))

theorem same (adj base D cap : ℕ) (rs : DynamicSplit.Roster ℓ Δ) (ptr : Fin (2^ℓ)→ℕ)
    (m : Memory w) (data : DynamicSplit.Stored adj rs m)
    (sep : adj+(2^ℓ)*Δ≤base) (room : 2^(ℓ+k)<2^w) :
    result (passes ℓ Δ k adj base ptr D cap) m =
      result (LayerRAM.passes k base (DynamicSplit.incoming rs) ptr D cap) m := by
  let c := LayerRAM.Layout.mk k base (DynamicSplit.incoming rs) ptr D cap
  unfold passes LayerRAM.passes
  rw [←all_map c k]
  exact list_same adj rs c rfl room sep _ m data

theorem fits (adj base D cap : ℕ) (ptr : Fin (2^ℓ)→ℕ) (old : ∀v,ptr v+2^k≤base)
    (sep : adj+(2^ℓ)*Δ≤base) (wide : 2^(ℓ+k)<2^w) (space : base+k*(2^ℓ)*2^k<2^w) :
    ∀p∈passes ℓ Δ k adj base ptr D cap,p.Fits w := by
  intro p hp
  obtain ⟨q,mem,rfl⟩ := List.mem_map.mp hp
  have depth := order_mem mem
  have start : base≤base+(q.1*(2^ℓ)+q.2.val)*2^k := Nat.le_add_right ..
  have rank : q.1*(2^ℓ)+q.2.val+1≤k*(2^ℓ) := calc
    _ ≤ q.1*(2^ℓ)+(2^ℓ) := by have := q.2.isLt;omega
    _ = (q.1+1)*(2^ℓ) := (Nat.succ_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ depth
  have endRow := Nat.mul_le_mul_right (2^k) rank
  rw [Nat.succ_mul] at endRow
  have small : 2^k<2^w := (Nat.pow_le_pow_right (by decide : 0<2) (Nat.le_add_left k ℓ)).trans_lt wide
  refine ⟨DynamicSplit.fits _ _ _ _ _ _ _ ⟨Nat.two_pow_pos _,small,(old _).trans start⟩ ?_ ?_,?_⟩
  · intro j
    exact ⟨Nat.two_pow_pos 0,(show 1≤2^k from Nat.two_pow_pos _).trans_lt small,
      Nat.succ_le_of_lt (((slot_before (v:=q.2) (s:=j) adj).trans_le sep).trans_le start)⟩
  · intro z b h
    unfold prev at h
    split at h
    next used =>
      obtain rfl := Option.some.inj h
      have stage := Nat.mul_le_mul_right (2^ℓ) used.2
      rw [Nat.succ_mul] at stage
      have before := Nat.mul_le_mul_right (2^k) stage
      rw [Nat.add_mul] at before
      refine ⟨Nat.two_pow_pos _,wide,?_⟩
      change base+(k-1-z)*(2^ℓ)*2^k+2^(ℓ+k)≤base+(q.1*(2^ℓ)+q.2.val)*2^k
      rw [pow_add,Nat.add_mul]
      omega
    next=>contradiction
  · change base+(q.1*(2^ℓ)+q.2.val)*2^k+2^k<2^w
    omega

theorem clock_le (ℓ Δ k adj base D cap : ℕ) (ptr : Fin (2^ℓ)→ℕ) :
    clock (passes ℓ Δ k adj base ptr D cap)≤4+k*(2^ℓ)*(4+2^k*(2*DynamicSplit.workBound k Δ+4)) := by
  have len : (passes ℓ Δ k adj base ptr D cap).length=k*(2^ℓ) := by simp [passes,order_len]
  rw [←len]
  apply ProtocolRAM.clock_le
  intro p hp
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  exact ⟨le_rfl,DynamicSplit.work ..⟩

theorem bounded (w ℓ Δ k adj base D cap : ℕ) (ptr : Fin (2^ℓ)→ℕ) :
    CandidateRAM.Bounded (ProtocolRAM.program w (passes ℓ Δ k adj base ptr D cap))
      (clock (passes ℓ Δ k adj base ptr D cap)) := by
  apply CandidateRAM.passes_bound
  intro p hp
  obtain ⟨q,_,rfl⟩ := List.mem_map.mp hp
  exact Nat.two_pow_pos _

end Hierarchy.DescentColonies.RosterLayers

end OAI
