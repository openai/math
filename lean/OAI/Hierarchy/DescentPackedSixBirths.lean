import OAI.Hierarchy.DescentMatchLaneNumbers
import OAI.Hierarchy.DescentPackedMatchChunk
import OAI.Hierarchy.DescentPackedZip

namespace OAI
/-! # Publish the six new party records from the matcher's actual two output words -/
namespace Hierarchy.DescentPacking.PackedMatch.SixBirths
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def profiles (s : Shape) (M : ℕ) := s.digit*(M*s.pairs)
def topology (s : Shape) (M : ℕ) := s.outputBits*M
def width (s : Shape) (M : ℕ) := (s.digit+1)*((M*s.pairs)*6)
def slot {n M : ℕ} (a : Fin M) (j : Fin n) (q : Fin 6) : Fin ((M*n)*6) :=
  finProdFinEquiv (finProdFinEquiv (a,j),q)

def mark {d : ℕ} (p : Cell d) : Cell (d+1) :=
  ⟨p.val+1,by rw [pow_succ];have:=p.isLt;have:=Nat.two_pow_pos d;omega⟩

def births (s : Shape) (M : ℕ) (keys : Cell (topology s M)) (tape : Cell (profiles s M)) : Cell (width s M) :=
  encode (s.digit+1) ((M*s.pairs)*6) (fun k=>
    let p : Fin (M*s.pairs)×Fin 6:=finProdFinEquiv.symm k
    let pair : Fin M×Fin s.pairs:=finProdFinEquiv.symm p.1
    if pair.2.val<(laneCounts s M keys pair.1).val then mark ((encode s.digit (M*s.pairs)).symm tape p.1) else 0)

private theorem digit_val {d n : ℕ} (p : Cell (d*n)) (i : Fin n) :
    ((encode d n).symm p i).val=digit d i.val p.val := by
  simpa only [Equiv.apply_symm_apply] using (digit_encode ((encode d n).symm p) i).symm

theorem births_at (s : Shape) (M : ℕ) (keys : Cell (topology s M)) (tape : Cell (profiles s M))
    (a : Fin M) (j : Fin s.pairs) (q : Fin 6) :
    digit (s.digit+1) (slot a j q).val (births s M keys tape).val=
      if j.val<(laneCounts s M keys a).val then digit s.digit (finProdFinEquiv (a,j)).val tape.val+1 else 0 := by
  unfold births
  rw [digit_encode]
  simp only [slot,Equiv.symm_apply_apply]
  by_cases live : j.val<(laneCounts s M keys a).val
  · simpa only [ite_eq_left live,mark] using congrArg (fun z : ℕ => z+1)
      (digit_val (d:=s.digit) (n:=M*s.pairs) tape (finProdFinEquiv (a,j)))
  · simp [live]

def key (s : Shape) (M : ℕ) : Cell (profiles s M)×Cell (topology s M)≃Cell (profiles s M+topology s M) :=
  finProdFinEquiv.trans (finCongr (pow_add ..).symm)

def controlWord (s : Shape) (M : ℕ) (v : Cell (profiles s M+topology s M)) : ℕ :=
  (births s M ((key s M).symm v).2 ((key s M).symm v).1).val

structure Banks where
  original : Bank
  normalized : Bank
  shift : Bank
  table : Bank

def expr (g : Banks) : Expr := .lookup g.table (.op .add (.lookup g.original .row) (.lookup g.shift (.lookup g.normalized .row)))

def program (g : Banks) (n out w : ℕ) := scan w out n (expr g)
def after {w : ℕ} (g : Banks) (n out : ℕ) (mem : Memory w) := image out n (expr g) mem

structure Room (s : Shape) (M n out w : ℕ) (g : Banks) : Prop where
  a : g.original.Fits w out
  b : g.normalized.Fits w out
  shift : g.shift.Fits w out
  table : g.table.Fits w out
  fitsA : n≤g.original.size
  fitsB : n≤g.normalized.size
  shiftBits : g.shift.bits=profiles s M
  tableBits : g.table.bits=profiles s M+topology s M
  published : width s M≤w
  output : out+n<2^w

def Static {w : ℕ} (s : Shape) (M : ℕ) (g : Banks) (mem : Memory w) : Prop :=
  (∀i : Cell (profiles s M),mem (g.shift.base+i.val)=((2^(topology s M)*i.val:ℕ):Word w)) ∧
   ∀i : Cell (profiles s M+topology s M),mem (g.table.base+i.val)=(controlWord s M i:Word w)

def cut (bits v : ℕ) : Cell bits := ⟨v%2^bits,Nat.mod_lt _ (Nat.two_pow_pos _)⟩

theorem digit_cut (s : Shape) (M : ℕ) (v : ℕ) (i : Fin (M*s.pairs)) :
    digit s.digit i.val (cut (profiles s M) v).val=digit s.digit i.val v := by
  have part : 2^(s.digit*(i.val+1))∣2^(profiles s M):=pow_dvd_pow _ (Nat.mul_le_mul_left _ i.isLt)
  simp only [cut,digit,Nat.mod_mod_of_dvd _ part]

theorem run (s : Shape) (M n out w : ℕ) (g : Banks) (fit : Room s M n out w g) (m : Memory w) :
    (program g n out w).Exec m (after g n out m) (4+54*n) ∧ CheapCode (program g n out w) := by
  have valid : (expr g).Fits w out := by simp [expr,Expr.Fits,fit.a,fit.b,fit.shift,fit.table]
  refine ⟨?_,@scan_cheap _ _ _ _⟩
  rw [show 4+54*n=4+n*(2*(expr g).work+4) by change 4+54*n=4+n*(2*25+4);omega]
  intro P R K machine
  exact scan_exec out n (expr g) m valid fit.output machine

theorem word_read (s : Shape) (M n out w : ℕ) (g : Banks) (fit : Room s M n out w g) (m : Memory w)
    (fixed : Static s M g m) (keys : Fin n→Cell (topology s M))
    (posted : ∀i : Fin n,m (g.original.base+i.val)=((keys i).val:ℕ)) (i : Fin n) :
    (after g n out m (out+i.val)).val=(births s M (keys i) (cut (profiles s M) (m (g.normalized.base+i.val)).val)).val := by
  let t:=cut (profiles s M) (m (g.normalized.base+i.val)).val
  let v:=key s M (t,keys i)
  have topRead:=DescentPackedZip.bank_read g.original m (i.isLt.trans_le fit.fitsA) fit.a
  have normRead:=DescentPackedZip.bank_read g.normalized m (i.isLt.trans_le fit.fitsB) fit.b
  have shift : g.shift.read m (m (g.normalized.base+i.val))=((2^(topology s M)*t.val:ℕ):Word w) := by
    simpa only [Bank.read,Bank.size,fit.shiftBits,t,cut] using fixed.1 t
  have small : v.val<g.table.size:=by simpa only [Bank.size,fit.tableBits] using v.isLt
  have got:=ProtocolRAMGeneratedWrite.read_image out n (expr g) m i
  change after g n out m (out+i.val)=g.table.read m (g.original.read m (i.val:Word w)+g.shift.read m (g.normalized.read m (i.val:Word w))) at got
  rw [topRead,normRead,posted i,shift,←Nat.cast_add] at got
  change after g n out m (out+i.val)=g.table.read m (v.val:Word w) at got
  rw [DescentPackedZip.bank_read g.table m small fit.table,fixed.2] at got
  have bounded : controlWord s M v<2^w:=(births s M _ _).isLt.trans_le (Nat.pow_le_pow_right (by decide) fit.published)
  rw [got,Fin.val_cast_of_lt bounded]
  simp only [controlWord,v,Equiv.symm_apply_apply,t]

theorem fields (s : Shape) (M n out w : ℕ) (g : Banks) (fit : Room s M n out w g)
    (m : Memory w) (fixed : Static s M g m) (keys : Fin n→Cell (topology s M))
    (posted : ∀i : Fin n,m (g.original.base+i.val)=((keys i).val:ℕ))
    (i : Fin n) (a : Fin M) (j : Fin s.pairs) (q : Fin 6) :
    digit (s.digit+1) (slot a j q).val (after g n out m (out+i.val)).val=
      if j.val<(laneCounts s M (keys i) a).val then digit s.digit (finProdFinEquiv (a,j)).val (m (g.normalized.base+i.val)).val+1 else 0 := by
  rw [word_read s M n out w g fit m fixed keys posted i,births_at,digit_cut]

theorem role {n M : ℕ} (a : Fin M) (j : Fin n) (q : Fin 6) : (slot a j q).val%6=q.val := by
  simp only [slot,finProdFinEquiv_apply_val]
  omega

theorem below (s : Shape) (M : ℕ) (g : Banks) {w cut : ℕ} {m n : Memory w}
    (old : Static s M g m) (shift : g.shift.Fits w cut) (dict : g.table.Fits w cut)
    (sb : g.shift.bits=profiles s M) (db : g.table.bits=profiles s M+topology s M)
    (kept : ∀a<cut,n a=m a) : Static s M g n := by
  constructor
  · intro i
    have hi : i.val<g.shift.size:=by simpa only [Bank.size,sb] using i.isLt
    exact (kept _ ((Nat.add_lt_add_left hi _).trans_le shift.2.2)).trans (old.1 i)
  · intro i
    have hi : i.val<g.table.size:=by simpa only [Bank.size,db] using i.isLt
    exact (kept _ ((Nat.add_lt_add_left hi _).trans_le dict.2.2)).trans (old.2 i)

/-- The physical role is the position modulo six. A zero word marks an empty
seat. Every live seat contains its normalized profile plus one. -/
def atom (z sent pos : ℕ) : Option (ℕ×ℕ×ℕ) :=
  if sent=0 then none else some (z,sent-1,pos%6)

abbrev Issued (s : Shape) (M : ℕ) (keys : Cell (topology s M)) :=
  Σa : Fin M,Fin (laneCounts s M keys a).val×Fin 6

def address (s : Shape) (M : ℕ) (keys : Cell (topology s M)) (p : Issued s M keys) :
    Fin ((M*s.pairs)*6) :=
  slot p.1 ⟨p.2.1.val,p.2.1.isLt.trans_le (Nat.le_of_lt_succ (laneCounts s M keys p.1).isLt)⟩ p.2.2

theorem address_injective (s : Shape) (M : ℕ) (keys : Cell (topology s M)) :
    Function.Injective (address s M keys) := by
  rintro ⟨a,j,q⟩ ⟨b,k,t⟩ equal
  have top:=finProdFinEquiv.injective equal
  have mid:=finProdFinEquiv.injective (congrArg Prod.fst top)
  have same : a=b:=congrArg Prod.fst mid
  subst b
  have index : j.val=k.val := congrArg (fun p : Fin M × Fin s.pairs => p.2.val) mid
  have row : j=k := Fin.ext index
  have role : q=t:=congrArg Prod.snd top
  cases row;cases role;rfl

theorem present (s : Shape) (M n out w : ℕ) (g : Banks) (fit : Room s M n out w g)
    (m : Memory w) (fixed : Static s M g m) (keys : Fin n→Cell (topology s M))
    (posted : ∀i : Fin n,m (g.original.base+i.val)=((keys i).val:ℕ))
    (i : Fin n) (a : Fin M) (j : Fin s.pairs) (q : Fin 6) :
    digit (s.digit+1) (slot a j q).val (after g n out m (out+i.val)).val≠0 ↔
      ∃p : Issued s M (keys i),address s M (keys i) p=slot a j q := by
  rw [fields s M n out w g fit m fixed keys posted i a j q]
  constructor
  · intro nz
    have active : j.val<(laneCounts s M (keys i) a).val:=by
      by_contra h
      exact nz (ite_eq_right h)
    exact ⟨⟨a,⟨j.val,active⟩,q⟩,rfl⟩
  · rintro ⟨⟨b,t,v⟩,same⟩
    have high:=finProdFinEquiv.injective same
    have mid:=finProdFinEquiv.injective (congrArg Prod.fst high)
    have lane : b=a:=congrArg Prod.fst mid
    subst a
    have index : t.val=j.val:=congrArg Fin.val (congrArg Prod.snd mid)
    rw [ite_eq_left (index ▸ t.isLt)]
    omega

theorem issued_count (s : Shape) (M : ℕ) (keys : Cell (topology s M)) :
    Fintype.card (Issued s M keys)=chunkCount s M keys*6 := by
  simp [Issued,Fintype.card_sigma,chunkCount,Finset.sum_mul]


theorem unit_bound (s : Shape) (pos : 0<s.digit) : unit s≤2*s.outputBits := by
  have room : s.pairs≤ s.digit*s.pairs:=by simpa using Nat.mul_le_mul_right s.pairs (show 1≤ s.digit from pos)
  unfold unit Shape.outputBits Shape.outFields
  apply max_le <;> nlinarith only [room,pos,Nat.zero_le (s.digit*s.pairs)]

theorem price (s : Shape) (w H G : ℕ) (pos : 0<s.digit) (wide : 2*unit s≤w) :
    let M:=lanes w (unit s)
    2^(profiles s M+topology s M)≤2^(w/2) ∧ width s M≤w/2 ∧
    (4+54*(H*chunks G M))*w≤4*w+54*(H*w+4*H*G*unit s) := by
  let M:=lanes w (unit s)
  have enough : 0 < unit s := by
    have hp : 0 < s.outputBits := Nat.mul_pos pos (by unfold Shape.outFields;omega)
    exact (hp.trans_le (Nat.le_add_left ..)).trans_le (le_max_left ..)
  have fit:=lanes_fit w (unit s)
  have q : profiles s M+topology s M=M*(s.digit*s.pairs+s.outputBits) := by unfold profiles topology;ring
  have b : width s M=M*((s.digit+1)*(s.pairs*6)) := by unfold width;ring
  have volume:=DescentSIMDLookup.volume H G w (unit s) enough wide
  dsimp only
  refine ⟨Nat.pow_le_pow_right (by decide) ?_,?_,?_⟩
  · rw [q];exact (Nat.mul_le_mul_left M (le_max_left ..)).trans fit
  · rw [b];exact (Nat.mul_le_mul_left M (le_max_right ..)).trans fit
  · nlinarith only [Nat.mul_le_mul_left 54 volume]

end
end Hierarchy.DescentPacking.PackedMatch.SixBirths

end OAI
