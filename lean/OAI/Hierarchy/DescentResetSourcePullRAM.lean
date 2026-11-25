import OAI.Hierarchy.DescentPackedSumWords
import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Reading an already computed ticket or incidence from its actual transmitting port -/
noncomputable section
namespace Hierarchy.DescentResetSourcePullRAM
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM DescentColonies.SplitRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open DescentPackedSumWords
open scoped Classical Fin.CommRing BigOperators

variable {H G M w b a Δ K : ℕ}
abbrev Address (Δ K : ℕ) := Fin Δ × Fin K

def number (x : Option (Address Δ K)) := x.elim 0 (fun s=>(finProdFinEquiv s).val+1)

def query (ask : Fin H→Fin G→Option (Address Δ K)) (h : Fin H) (g : Fin G) : Cell b :=
  (number (ask h g):ℕ)

def take (i : Fin (Δ*K)) (mark : Cell b) (payload : Cell a) : Cell a :=
  if mark.val=i.val+1 then payload else 0

def book (b a M Δ K : ℕ) (i : Fin ((Δ*K)*2)) : Page :=
  let p : Fin (Δ*K)×Fin 2:=finProdFinEquiv.symm i
  binary (take (b:=b) (a:=a) (Δ:=Δ) (K:=K) p.1) M p.2

def menus (b a M Δ K base : ℕ) (i : Fin (Δ*K)) :=
  joined (book b a M Δ K) ((b+a)*M) base (fun side=>finProdFinEquiv (i,side))

private theorem pageRoom (i : Fin ((Δ*K)*2)) : (book b a M Δ K i).bits≤(b+a)*M := by
  obtain ⟨⟨j,s⟩,rfl⟩:=finProdFinEquiv.surjective i
  fin_cases s <;> simp [book,binary,Nat.mul_le_mul_right M (Nat.le_add_right b a)]

theorem mounted (base : ℕ) (mem : Memory w) (i : Fin (Δ*K)) :
    Static (menus b a M Δ K base i) (take (b:=b) (a:=a) (Δ:=Δ) (K:=K) i) M
      (after (book b a M Δ K) ((b+a)*M) base mem) :=
  binary_mounted _ _ _ _ _ _ pageRoom (fun s=>finProdFinEquiv (i,s))
    (fun _=>by simp [book])

theorem rooms (base out : ℕ) (i : Fin (Δ*K)) (sep : base+((Δ*K)*2)*2^((b+a)*M)≤out)
    (room : out<2^w) : WordRoom (menus b a M Δ K base i) b a M w out := by
  let idx:=fun s : Fin 2=>finProdFinEquiv (i,s)
  have fit (s : Fin 2) : (bank (book b a M Δ K) ((b+a)*M) base (idx s)).Fits w out :=
    bank_room (book b a M Δ K) ((b+a)*M) base out (idx s) (pageRoom (idx s)) sep room
  refine ⟨fit 0,fit 1,?_,?_⟩ <;>
    simp only [menus,joined,bank,book,Equiv.symm_apply_apply,binary] <;> rfl

def picked (peer : Fin H→Fin Δ→Option (Fin H)) (old : Fin K→Fin H→Fin G→Cell a)
    (ask : Fin H→Fin G→Option (Address Δ K)) (h : Fin H) (g : Fin G) : Cell a :=
  (ask h g).elim 0 (fun s=>(peer h s.1).elim 0 (fun v=>old s.2 v g))

def get (p : Ports Δ) (old : Fin K→Bank) (H : ℕ) (i : Fin (Δ*K)) : Expr :=
  let s : Address Δ K:=finProdFinEquiv.symm i
  peerExpr p (old s.2) H s.1

def instruction (tbl : Fin (Δ*K)→Tables) (q : Expr) (p : Ports Δ) (old : Fin K→Bank) (H : ℕ) :=
  total (fun i=>(tbl i).read q (get p old H i)) (List.finRange (Δ*K))

private theorem sum_cell (small : Δ*K<2^b) (ask : Option (Address Δ K)) (load : Address Δ K→Cell a) :
    (∑i : Fin (Δ*K),(take (b:=b) (Δ:=Δ) (K:=K) i (number ask : Cell b) (load (finProdFinEquiv.symm i))).val)=
      (ask.elim 0 load).val := by
  cases ask with
  | none=>simp [take,number]
  | some s=>
    have fits : (finProdFinEquiv s).val+1<2^b:=lt_of_le_of_lt (finProdFinEquiv s).isLt small
    simp only [number,Option.elim_some,take,Fin.val_cast_of_lt fits,Nat.add_right_cancel_iff,Fin.val_inj]
    rw [Finset.sum_eq_single_of_mem (finProdFinEquiv s) (Finset.mem_univ _)]
    · simp [Equiv.symm_apply_apply]
    · intro i _ distinct
      simp [Ne.symm distinct]

private theorem sum_packed (small : Δ*K<2^b) (peer : Fin H→Fin Δ→Option (Fin H)) (old : Fin K→Fin H→Fin G→Cell a)
    (ask : Fin H→Fin G→Option (Address Δ K)) (p : Row H G M) :
    (∑i : Fin (Δ*K),(data (fun v g=>
      let s : Address Δ K:=finProdFinEquiv.symm i
      take (b:=b) (Δ:=Δ) (K:=K) i (query ask v g) ((peer v s.1).elim 0 (fun u=>old s.2 u g))) p).val)=
      (data (picked peer old ask) p).val := by
  simp_rw [lanes_val]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  by_cases live : p.2.val*M+j.val<G
  · simp only [dite_eq_left live,←Finset.sum_mul]
    exact congrArg (·*_) (sum_cell small (ask p.1 ⟨_,live⟩)
      (fun s=>(peer p.1 s.1).elim 0 (fun h=>old s.2 h ⟨_,live⟩)))
  · simp [live]

theorem source (tbl : Fin (Δ*K)→Tables) (q : Expr) (p : Ports Δ) (fields : Fin K→Bank)
    (out : Bank) (m : Memory w) (peer : Fin H→Fin Δ→Option (Fin H))
    (old : Fin K→Fin H→Fin G→Cell a) (ask : Fin H→Fin G→Option (Address Δ K))
    (small : Δ*K<2^b) (queryFit : q.Fits w out.base)
    (aperture : ∀j,Accessible p (fields j) H G M w out.base) (actual : Mounted p peer m G M)
    (issued : ∀j,Reads (fields j) (old j) M m) (selector : Source q (query (b:=b) ask) M m)
    (space : ∀i,WordRoom (tbl i) b a M w out.base)
    (pages : ∀i,Static (tbl i) (take (b:=b) (a:=a) (Δ:=Δ) (K:=K) i) M m)
    : (instruction tbl q p fields H).Fits w out.base ∧
      Source (instruction tbl q p fields H) (picked peer old ask) M m := by
  have fit i : (get p fields H i).Fits w out.base := peer_fits p _ _ (aperture _) _
  refine ⟨fits_total _ (fun i=>(space i).safe q _ queryFit (fit i)) _,?_⟩
  intro row
  have each (i : Fin (Δ*K)) :=
    read_data (tbl i) q (get p fields H i) out.base ((space i).issue _ _ queryFit (fit i))
      (take (b:=b) (a:=a) (Δ:=Δ) (K:=K) i) (by simp [take]) m (pages i) _ _ selector
      (peerSource p _ _ (aperture _) peer m actual _ (issued _) (finProdFinEquiv.symm i).1) row
  have allTerms:=eval_sum _ _ m _ each (List.finRange (Δ*K))
  rw [←List.ofFn_eq_map,List.sum_ofFn,sum_packed small peer old ask] at allTerms
  exact allTerms

/-- A single group-packed physical pass receives the chosen previously
published field. It covers empty selectors, ghost hosts and genuine loops. -/
theorem run (tbl : Fin (Δ*K)→Tables) (q : Expr) (p : Ports Δ) (fields : Fin K→Bank)
    (out : Bank) (m : Memory w) (peer : Fin H→Fin Δ→Option (Fin H))
    (old : Fin K→Fin H→Fin G→Cell a) (ask : Fin H→Fin G→Option (Address Δ K))
    (small : Δ*K<2^b) (queryFit : q.Fits w out.base)
    (aperture : ∀j,Accessible p (fields j) H G M w out.base) (actual : Mounted p peer m G M)
    (issued : ∀j,Reads (fields j) (old j) M m) (selector : Source q (query (b:=b) ask) M m)
    (space : ∀i,WordRoom (tbl i) b a M w out.base)
    (pages : ∀i,Static (tbl i) (take (b:=b) (a:=a) (Δ:=Δ) (K:=K) i) M m)
    (room : out.base+H*chunks G M<2^w) :
    let expr:=instruction tbl q p fields H
    let result:=image out.base (H*chunks G M) expr m
    (scan w out.base (H*chunks G M) expr).Exec m result (4+H*chunks G M*(2*expr.work+4)) ∧
      Reads out (picked peer old ask) M result ∧ CheapCode (scan w out.base (H*chunks G M) expr) ∧
      ∀i,i<out.base ∨ out.base+H*chunks G M≤ i → result i=m i := by
  intro expr result
  have src:=source tbl q p fields out m peer old ask small queryFit aperture actual issued selector space pages
  refine ⟨scan_exec _ _ _ _ src.1 room,?_,by apply scan_cheap,ProtocolRAMGeneratedWrite.frame_image _ _ _ _⟩
  intro row
  exact (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (src.2 row)

theorem work (tbl : Fin (Δ*K)→Tables) (q : Expr) (p : Ports Δ) (fields : Fin K→Bank) (H : ℕ) :
    (instruction tbl q p fields H).work≤1+(Δ*K)*(q.work+64) := by
  have each (i : Fin (Δ*K)) : ((tbl i).read q (get p fields H i)).work≤q.work+63 := by
    rw [DescentPackedZip.work]
    simp only [get,peerExpr,neighborID,Expr.work]
    omega
  simpa [instruction,List.length_finRange,Nat.add_assoc] using
    work_total (fun i=>(tbl i).read q (get p fields H i)) (q.work+63) each (List.finRange (Δ*K))

end Hierarchy.DescentResetSourcePullRAM
end

end OAI
