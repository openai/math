import OAI.Hierarchy.DescentResetSourcePullRAM
import OAI.Hierarchy.DescentResetFieldAssembler

namespace OAI
/-! # One shared address and selection book for the two source-end readbacks -/
noncomputable section
namespace Hierarchy.DescentResetSourceSeekRAM
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing

variable {H G M w b a t key Δ K : ℕ}
def keyBits (Δ K : ℕ) := Nat.clog 2 (Δ*K+1)
def addressEnd (base K b t M : ℕ) := base+K*2*2^((b*7+t)*M)
def endAddress (base Δ K b t a M : ℕ) := addressEnd base K b t M+(Δ*K)*2*2^((keyBits Δ K+a)*M)

def select (code : Fin K→ℕ→ℕ) (j : Fin K) (header : Cell (b*7)) (original : Cell t) : Cell (keyBits Δ K) :=
  let f:=DescentResetFieldAssembler.decode b header
  if f.live then ((f.src*K+code j original.val+1:ℕ):Cell (keyBits Δ K)) else 0

private theorem blank (code : Fin K→ℕ→ℕ) (j : Fin K) :
    select (Δ:=Δ) (b:=b) (t:=t) code j 0 0=0 := by
  have z : (DescentSIMDLookup.encode b 7).symm 0=(fun _=>0) := by
    apply (DescentSIMDLookup.encode b 7).symm_apply_eq.mpr
    apply Fin.ext; simp [DescentSIMDLookup.encode]
  simp [select,DescentResetFieldAssembler.decode,z]

def pages (Δ K b t M : ℕ) (code : Fin K→ℕ→ℕ) (i : Fin (K*2)) : Page :=
  let p : Fin K×Fin 2:=finProdFinEquiv.symm i
  binary (select (Δ:=Δ) (b:=b) (t:=t) code p.1) M p.2

def tables (base Δ K b t M : ℕ) (code : Fin K→ℕ→ℕ) (j : Fin K) :=
  joined (pages Δ K b t M code) ((b*7+t)*M) base (fun s=>finProdFinEquiv (j,s))

private theorem size (code : Fin K→ℕ→ℕ) (i : Fin (K*2)) :
    (pages Δ K b t M code i).bits≤(b*7+t)*M := by
  obtain ⟨⟨j,s⟩,rfl⟩:=finProdFinEquiv.surjective i
  fin_cases s <;> simp [pages,binary,Nat.mul_le_mul_right M (Nat.le_add_right (b*7) t)]

def program (base Δ K b t a M w : ℕ) (code : Fin K→ℕ→ℕ) :=
  (mount (pages Δ K b t M code) ((b*7+t)*M) w base).seq
    (mount (DescentResetSourcePullRAM.book (keyBits Δ K) a M Δ K) ((keyBits Δ K+a)*M) w (addressEnd base K b t M))

def memory (base Δ K b t a M : ℕ) (code : Fin K→ℕ→ℕ) (m : Memory w) :=
  after (DescentResetSourcePullRAM.book (keyBits Δ K) a M Δ K) ((keyBits Δ K+a)*M) (addressEnd base K b t M)
    (after (pages Δ K b t M code) ((b*7+t)*M) base m)

theorem mountBooks (base : ℕ) (code : Fin K→ℕ→ℕ) (m : Memory w)
    (room : endAddress base Δ K b t a M<2^w) :
    let mid:=addressEnd base K b t M
    let stop:=endAddress base Δ K b t a M
    let o:=memory base Δ K b t a M code m
    let p:=program base Δ K b t a M w code
    p.Exec m o ((4+10*(K*2*2^((b*7+t)*M)))+(4+10*((Δ*K)*2*2^((keyBits Δ K+a)*M)))) ∧
    CheapCode p ∧
    (∀j,Static (tables base Δ K b t M code j) (select (Δ:=Δ) (b:=b) (t:=t) code j) M o ∧
      WordRoom (tables base Δ K b t M code j) (b*7) t M w stop) ∧
    (∀i,Static (DescentResetSourcePullRAM.menus (keyBits Δ K) a M Δ K mid i)
      (DescentResetSourcePullRAM.take (b:=keyBits Δ K) (a:=a) (Δ:=Δ) (K:=K) i) M o ∧
      WordRoom (DescentResetSourcePullRAM.menus (keyBits Δ K) a M Δ K mid i) (keyBits Δ K) a M w stop) ∧
    ∀z,z<base ∨ stop≤z → o z=m z := by
  intro mid stop o p
  let left:=pages Δ K b t M code
  let right:=DescentResetSourcePullRAM.book (keyBits Δ K) a M Δ K
  let y:=after left ((b*7+t)*M) base m
  have early : mid≤ stop:=Nat.le_add_right ..
  have bounds : base ≤ mid:=Nat.le_add_right ..
  have run₁ : (mount left ((b*7+t)*M) w base).Exec m y
      (4+10*(K*2*2^((b*7+t)*M))) :=
    (ROM.run left ((b*7+t)*M) base m (early.trans_lt room)).1
  have run₂ : (mount right ((keyBits Δ K+a)*M) w mid).Exec y o
      (4+10*((Δ*K)*2*2^((keyBits Δ K+a)*M))) :=
    (ROM.run right ((keyBits Δ K+a)*M) mid y room).1
  have stable:=ROM.frame right ((keyBits Δ K+a)*M) mid y
  refine ⟨?_,cheap_seq (cheap left ((b*7+t)*M) w base) (cheap right ((keyBits Δ K+a)*M) w mid),?_,?_,?_⟩
  · intro P R L machine
    exact Procedure.Exec.then (@run₁) (@run₂) machine
  · intro j
    let idx:=fun s : Fin 2=>finProdFinEquiv (j,s)
    have room' s : (bank left ((b*7+t)*M) base (idx s)).Fits w mid:=
      bank_room _ _ _ _ _ (size code _) le_rfl (early.trans_lt room)
    have tab:=binary_mounted (select (Δ:=Δ) (b:=b) (t:=t) code j) M left ((b*7+t)*M) base m
      (size code) idx (fun _=>by simp [left,idx,pages])
    have keep (s : Fin 2) (a₀ : ℕ) (low : a₀<(bank left ((b*7+t)*M) base (idx s)).size) :
        o ((bank left ((b*7+t)*M) base (idx s)).base+a₀)=y ((bank left ((b*7+t)*M) base (idx s)).base+a₀) :=
      stable _ (.inl ((Nat.add_lt_add_left low _).trans_le (room' s).2.2))
    constructor
    · constructor
      · intro q;exact (keep 0 q.val (by simp [Bank.size,bank,left,idx,pages,binary])).trans (tab.1 q)
      · intro q;exact (keep 1 q.val (by simp [Bank.size,bank,left,idx,pages,binary])).trans (tab.2 q)
    · refine ⟨bank_room _ _ _ _ (idx 0) (size code _) early room,bank_room _ _ _ _ (idx 1) (size code _) early room,?_,?_⟩ <;>
        simp [tables,joined,bank,pages,binary]
  · intro i
    exact ⟨DescentResetSourcePullRAM.mounted mid y i,DescentResetSourcePullRAM.rooms mid stop i le_rfl room⟩
  · intro z away
    rcases away with h|h
    · exact (stable _ (.inl (h.trans_le bounds))).trans (ROM.frame _ _ _ m _ (.inl h))
    · exact (stable _ (.inr h)).trans (ROM.frame _ _ _ m _ (.inr (early.trans h)))

/-- The same number of public menu entries and labels pays for both uses. -/
theorem names (base Δ K b t a M w : ℕ) (code : Fin K→ℕ→ℕ) :
    DescentStaticWordColumn.names (program base Δ K b t a M w code)=
      15*(K*2*2^((b*7+t)*M)+1)+15*((Δ*K)*2*2^((keyBits Δ K+a)*M)+1) := by
  simp only [program,DescentStaticWordColumn.names_seq,mount,DescentStaticWordColumn.names_mount]

theorem source (code : Fin K→ℕ→ℕ) (j : Fin K) (tbl : Tables) (header original : Expr) (out : ℕ) (mem : Memory w)
    (info : Fin H→Fin G→DescentResetFieldAssembler.Meta) (words : Fin H→Fin G→Cell t)
    (ask : Fin H→Fin G→Option (DescentResetSourcePullRAM.Address Δ K))
    (fields : ∀v g i,DescentResetFieldAssembler.digits (info v g) i<2^b)
    (wanted : ∀h g, (if (info h g).live then (info h g).src*K+code j (words h g).val+1 else 0)=
      DescentResetSourcePullRAM.number (ask h g))
    (safe : WordRoom tbl (b*7) t M w out) (hFit : header.Fits w out) (oFit : original.Fits w out)
    (static : Static tbl (select (Δ:=Δ) (b:=b) (t:=t) code j) M mem)
    (hs : Source header (fun v g=>DescentResetFieldAssembler.raw b (info v g)) M mem)
    (os : Source original words M mem) :
    (tbl.read header original).Fits w out ∧
      Source (tbl.read header original) (DescentResetSourcePullRAM.query (b:=keyBits Δ K) ask) M mem := by
  refine ⟨safe.safe _ _ hFit oFit,?_⟩
  have read:=read_data tbl header original out (safe.issue _ _ hFit oFit) (select (Δ:=Δ) (b:=b) (t:=t) code j)
    (blank code j) mem static _ _ hs os
  have cells : (fun h g => select (Δ:=Δ) code j (DescentResetFieldAssembler.raw b (info h g)) (words h g)) =
      DescentResetSourcePullRAM.query (b:=keyBits Δ K) ask := by
    funext h g
    rw [select, DescentResetFieldAssembler.decode_raw _ (fields h g)]
    have same := congrArg (fun n : ℕ => (n : Cell (keyBits Δ K))) (wanted h g)
    cases act : (info h g).live <;> simpa [act, DescentResetSourcePullRAM.query] using same
  rw [← cells]
  exact read

end Hierarchy.DescentResetSourceSeekRAM
end

end OAI
