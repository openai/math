import OAI.Hierarchy.DescentMatcherRateNumbers
import OAI.Hierarchy.DescentPackedPhase

namespace OAI
/-! # Shared literal ROM for the two score ledgers and the dynamic winner gather -/

namespace Hierarchy.DescentPackedColony.Phase.Menu
open DescentColonies DescentGL DescentSIMDLookup DescentBinaryField DescentAffineColors ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {k b M w : ℕ}

abbrev Tag (k : ℕ) := Unit ⊕ Candidate k ⊕ (Fin (2^k-1) × Bool)

def number : Tag k→ℕ
  | .inl _=>0
  | .inr (.inl j)=>1+j.val
  | .inr (.inr (i,y))=>1+2^(k+1)+2*i.val+y.toNat

theorem index_lt (t : Tag k) : number t<pages k := by
  rcases t with u|j|⟨i,y⟩
  · change 0<1+2^(k+1)+2*(2^k-1)
    exact (Nat.le_add_right 1 (2^(k+1))).trans (Nat.le_add_right _ _)
  · have bound : j.val<2^(k+1) := j.isLt
    change 1+j.val<1+2^(k+1)+2*(2^k-1)
    omega
  · have bound := i.isLt
    cases y <;> simp only [number,pages,Bool.toNat_false,Bool.toNat_true] <;> omega

theorem number_injective : Function.Injective (@number k) := by
  intro x y h
  rcases x with u|i|⟨i,z⟩ <;> rcases y with v|j|⟨j,t⟩
  · exact congrArg Sum.inl (Subsingleton.elim u v)
  · change 0=1+j.val at h
    omega
  · change 0=1+2^(k+1)+2*j.val+t.toNat at h
    omega
  · change 1+i.val=0 at h
    omega
  · change 1+i.val=1+j.val at h
    obtain rfl : i=j := Fin.ext (Nat.add_left_cancel h)
    rfl
  · have bound : i.val<2^(k+1) := i.isLt
    change 1+i.val=1+2^(k+1)+2*j.val+t.toNat at h
    omega
  · change 1+2^(k+1)+2*i.val+z.toNat=0 at h
    omega
  · have bound : j.val<2^(k+1) := j.isLt
    change 1+2^(k+1)+2*i.val+z.toNat=1+j.val at h
    omega
  · change 1+2^(k+1)+2*i.val+z.toNat=1+2^(k+1)+2*j.val+t.toNat at h
    cases z <;> cases t <;> simp only [Bool.toNat_false,Bool.toNat_true] at h
    all_goals first | omega | (obtain rfl : i=j := Fin.ext (by omega); rfl)

def addr (lo page : ℕ) (t : Tag k) (i : Fin page) := lo+number t*page+i.val

theorem addr_injective (lo page : ℕ) (hp : 0<page) :
    Function.Injective (fun p : Tag k×Fin page=>addr lo page p.1 p.2) := by
  rintro ⟨s,i⟩ ⟨t,j⟩ eqn
  have same : number s*page+i.val=number t*page+j.val := by simpa only [addr,Nat.add_assoc,Nat.add_left_cancel_iff] using eqn
  have rem : i.val=j.val := by
    simpa only [Nat.mul_comm (number s) page,Nat.mul_comm (number t) page,Nat.mul_add_mod,
      Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt j.isLt] using congrArg (fun n=>n%page) same
  have high : number s*page=number t*page := by omega
  have sel : number s=number t := (Nat.mul_left_inj (Nat.ne_of_gt hp)).mp high
  exact Prod.ext (number_injective sel) (Fin.ext rem)

def bits (k b M : ℕ) : Tag k→ℕ
  | .inl _=>(1+k*2^k)*M
  | .inr (.inl _)=>PackedContribution.width k b*M
  | .inr (.inr (_,false))=>(1+k*2^k)*M
  | .inr (.inr (_,true))=>(1+k*2^k+b*2^k)*M

def bank (lo page k b M : ℕ) (t : Tag k) : Bank := ⟨lo+number t*page,bits k b M t⟩
def split (lo page k b M : ℕ) := bank lo page k b M (.inl ())
def color (lo page k b M : ℕ) (j : Candidate k) := bank lo page k b M (.inr (.inl j))
def zip (lo page k b M : ℕ) (i : Fin (2^k-1)) : DescentPackedZip.Tables :=
  ⟨bank lo page k b M (.inr (.inr (i,false))),bank lo page k b M (.inr (.inr (i,true)))⟩

def word (hk : 0<k) (b M w : ℕ) (t : Tag k) (z : ℕ) : Word w :=
  match t with
  | .inl _=> (DescentPackedScore.chunkScore (M:=M) (@PackedSplit.value k) (z:Cell ((1+k*2^k)*M)):ℕ)
  | .inr (.inl j)=> (DescentPackedScore.chunkScore (M:=M) (PackedContribution.value (b:=b) j) (z:Cell (PackedContribution.width k b*M)):ℕ)
  | .inr (.inr (_,false))=> (2^((b*2^k)*M)*z:ℕ)
  | .inr (.inr (i,true))=>((DescentPackedZip.table (M:=M) (affine (b:=b) (modulus hk) (seedAt k i).val)
      (z:Cell ((1+k*2^k+b*2^k)*M))).val : ℕ)

def mount (lo page : ℕ) (hk : 0<k) (b M : ℕ) (old : Memory w) (z : ℕ) : Word w :=
  if found : ∃p : Tag k×Fin page,addr lo page p.1 p.2=z then word hk b M w found.choose.1 found.choose.2.val else old z

theorem read (lo page : ℕ) (hk : 0<k) (b M : ℕ) (old : Memory w) (t : Tag k) (i : Fin page) :
    mount lo page hk b M old (addr lo page t i)=word hk b M w t i.val := by
  have hit : ∃p : Tag k×Fin page,addr lo page p.1 p.2=addr lo page t i := ⟨(t,i),rfl⟩
  have located : hit.choose=(t,i) := addr_injective lo page (Nat.zero_lt_of_lt i.isLt) hit.choose_spec
  rw [mount,dite_eq_left hit,located]

theorem lower (lo page : ℕ) (hk : 0<k) (b M : ℕ) (old : Memory w) {z : ℕ} (lt:z<lo) :
    mount lo page hk b M old z=old z := by
  rw [mount,dite_eq_right];rintro ⟨p,hit⟩;unfold addr at hit;omega

theorem end_bank (lo page k b M : ℕ) (t : Tag k) (fits : (bank lo page k b M t).size≤page) :
    (bank lo page k b M t).base+(bank lo page k b M t).size≤lo+pages k*page :=
  (Nat.add_le_add_left fits _).trans (by
    have n:=Nat.mul_le_mul_right page (index_lt t);rw [Nat.succ_mul] at n;change lo+number t*page+page≤_;omega)

theorem bit_bound (k b w : ℕ) (t : Tag k) : bits k b (lanes w (unit k b)) t≤w/2 := by
  have scaled (width : ℕ) (fits : width≤unit k b) : width*lanes w (unit k b)≤w/2 := by
    exact (Nat.mul_le_mul_right _ fits).trans (by
      rw [Nat.mul_comm]
      exact lanes_fit w (unit k b))
  rcases t with u|j|⟨i,side⟩
  · exact scaled (1+k*2^k) (by unfold unit; omega)
  · exact scaled (PackedContribution.width k b) (by unfold PackedContribution.width unit; omega)
  · cases side
    · exact scaled (1+k*2^k) (by unfold unit; omega)
    · exact scaled (1+k*2^k+b*2^k) (by unfold unit; omega)

theorem size_at (k b w lo : ℕ) (t : Tag k) : (bank lo (2^(w/2)) k b (lanes w (unit k b)) t).size≤2^(w/2) :=
  Nat.pow_le_pow_right (by decide) (bit_bound k b w t)

theorem reads (lo page : ℕ) (hk : 0<k) (b M : ℕ) (m : Memory w)
    (room : ∀t : Tag k,(bank lo page k b M t).size≤page) :
    let n:=mount lo page hk b M m
    (∀t : Cell ((1+k*2^k)*M),n ((split lo page k b M).base+t.val)=(DescentPackedScore.chunkScore (@PackedSplit.value k) t:Word w)) ∧
    (∀j (t : Cell (PackedContribution.width k b*M)),n ((color lo page k b M j).base+t.val)=
        (DescentPackedScore.chunkScore (PackedContribution.value (b:=b) j) t:Word w)) ∧
    ∀i,DescentPackedZip.Static (zip lo page k b M i) (affine (b:=b) (modulus hk) (seedAt k i).val) M n := by
  let native:=read lo page hk b M m
  refine ⟨fun t=>?_,fun j t=>?_,fun i=>⟨fun t=>?_,fun t=>?_⟩⟩
  · simpa only [addr,word,split,bank,Fin.cast_val_eq_self] using
      native (.inl ()) ⟨t.val,t.isLt.trans_le (room (.inl ()))⟩
  · simpa only [addr,word,color,bank,Fin.cast_val_eq_self] using
      native (.inr (.inl j)) ⟨t.val,t.isLt.trans_le (room (.inr (.inl j)))⟩
  · exact native (.inr (.inr (i,false))) ⟨t.val,t.isLt.trans_le (room (.inr (.inr (i,false))))⟩
  · simpa only [addr,word,zip,bank,Fin.cast_val_eq_self] using
      native (.inr (.inr (i,true))) ⟨t.val,t.isLt.trans_le (room (.inr (.inr (i,true))))⟩

end
end Hierarchy.DescentPackedColony.Phase.Menu

end OAI
