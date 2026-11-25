import OAI.Hierarchy.DescentResetFieldAssembler
import OAI.Hierarchy.DescentPackedColumnSum
import OAI.Hierarchy.DescentPackedSumWords

namespace OAI
/-! # One shared native bank tallies incoming reset stems for the trunk at each receiver -/
namespace Hierarchy.DescentResetTrunkIssue
open DescentSIMDLookup DescentPackedZip DescentResetFieldAssembler DescentOrdinaryAtomFieldRAM.ROM
open DescentPackedColumnSum DescentColonies.SplitRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {b X K H G M w : ℕ}

def scaled (b : ℕ) (word : Cell (b*7)) : ℕ:=(face false (decode b word)).toNat
def complete (shape : Meta) (count : ℕ) : Meta :=
  if shape.live && decide (0< count) then {shape with units:=count} else .blank
def fuse (b : ℕ) (shape : Cell (b*7)) (count : Cell b) :=raw b (complete (decode b shape) count.val)

theorem zero_raw (b : ℕ) : raw b .blank=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv _).val=0
  rw [finFunctionFinEquiv_apply]
  apply Finset.sum_eq_zero
  intro j _
  fin_cases j <;> simp [digits,Meta.blank]

theorem zero_decode (b : ℕ) : decode b 0=.blank := by
  rw [←zero_raw b,decode_raw]
  intro j;fin_cases j <;> exact Nat.two_pow_pos _

theorem zero_scale (b : ℕ) : scaled b 0=0:=by simp [scaled,zero_decode,face,Meta.blank]
theorem zero_fuse (b : ℕ) : fuse b 0 0=0 := by
  unfold fuse
  rw [zero_decode]
  exact zero_raw b

def width (b M : ℕ):=(b*7+b)*M
def endAddress (base b M : ℕ):=base+3*2^(width b M)
def pages (b M : ℕ) : Fin 3→Page:=Fin.cases ⟨b*7*M,fun a=>piece b (scaled b) a⟩ (binary (fuse b) M)
def tabs (base b M : ℕ):=joined (pages b M) (width b M) base Fin.succ
def unary (base b M : ℕ):=DescentOrdinaryAtomFieldRAM.ROM.bank (pages b M) (width b M) base 0
def payload (base b M : ℕ) (input : Fin K→Expr) :=
  total (fun j=>.lookup (unary base b M) (input j)) (List.finRange K)
def issue (base b M : ℕ) (shape : Expr) (input : Fin K→Expr):=(tabs base b M).read shape (payload base b M input)
def program (base b M w : ℕ):=mount (pages b M) (width b M) w base
def memory (base b M : ℕ) (m : Memory w):=DescentOrdinaryAtomFieldRAM.ROM.after (pages b M) (width b M) base m

theorem pageRoom (b M : ℕ) (j : Fin 3) : (pages b M j).bits≤width b M:=by
  fin_cases j <;> first | exact le_rfl | exact Nat.mul_le_mul_right M (Nat.le_add_right ..)

theorem issue_fits (base b M : ℕ) (head : Expr) (stem : Fin K→Expr)
    (headRoom : head.Fits w base) (stemRoom : ∀i,(stem i).Fits w base)
    (space : endAddress base b M<2^w) : (issue base b M head stem).Fits w (endAddress base b M) :=by
  let top:=endAddress base b M
  have early : base≤top:=Nat.le_add_right ..
  have bankFit : (unary base b M).Fits w top:=bank_room (pages b M) _ base _ _ (pageRoom b M 0) le_rfl space
  have slots (j : Fin K) : (Expr.lookup (unary base b M) (stem j)).Fits w top:=
    ⟨bankFit,ProtocolRAMGeneratedWrite.fits_mono _ early (stemRoom j)⟩
  have total : (payload base b M stem).Fits w top:=fits_total _ slots _
  have zip : DescentPackedZip.Fits (tabs base b M) head (payload base b M stem) (b*7) b M top w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ early headRoom,total,
     bank_room (pages b M) _ base _ _ (pageRoom b M _) le_rfl space,
     bank_room (pages b M) _ base _ _ (pageRoom b M _) le_rfl space,rfl,rfl⟩
  exact ⟨zip.apply,zip.right,zip.shift,zip.left⟩

theorem run (base : ℕ) (head : Fin X→Expr) (stem : Fin X→Fin K→Expr) (m : Memory w)
    (shape : Fin X→Fin H→Fin G→Meta) (inbound : Fin X→Fin K→Fin H→Fin G→Meta)
    (early : ∀x,(head x).Fits w base) (slots : ∀x j,(stem x j).Fits w base)
    (heads : ∀x,Source (head x) (fun h g=>raw b (shape x h g)) M m)
    (bits : ∀x j,Source (stem x j) (fun h g=>raw b (inbound x j h g)) M m)
    (bounded : ∀x h g,∀l,digits (shape x h g) l<2^b)
    (stemRoom : ∀x j h g l,digits (inbound x j h g) l<2^b)
    (limit : ∀x h g,(∑j,(face false (inbound x j h g)).toNat)<2^b)
    (space : endAddress base b M<2^w) :
    let top:=endAddress base b M
    let done:=memory base b M m
    (program base b M w).Exec m done (4+10*(3*2^(width b M))) ∧
      (∀x,(issue base b M (head x) (stem x)).Fits w top) ∧
      (∀x,Source (issue base b M (head x) (stem x))
        (fun h g=>raw b (complete (shape x h g) (∑j,(face false (inbound x j h g)).toNat))) M done) ∧
      (∀n,n<base ∨ top≤n→done n=m n) ∧
      DescentStaticWordColumn.names (program base b M w)=15*(3*2^(width b M)+1) ∧ CheapCode (program base b M w) := by
  intro top done
  let P:=pages b M
  let B₀:=unary base b M
  have earlyTop : base≤top:=Nat.le_add_right ..
  have cpu:=DescentOrdinaryAtomFieldRAM.ROM.run P (width b M) base m space
  have stay:=DescentOrdinaryAtomFieldRAM.ROM.frame P (width b M) base m
  have keep {c : ℕ} (e : Expr) (fit : e.Fits w base) (rows : Fin H→Fin G→Cell c) (old : Source e rows M m) :
      Source e rows M done:=fun r=>(ProtocolRAM.eval_below e _ m done fit (fun a ha=>stay a (.inl ha))).trans (old r)
  have bankFits : B₀.Fits w top:=bank_room P _ base _ _ (pageRoom b M 0) le_rfl space
  have live (x : Fin X) (j : Fin K) : (Expr.lookup B₀ (stem x j)).Fits w top:=
    ⟨bankFits,ProtocolRAMGeneratedWrite.fits_mono _ earlyTop (slots x j)⟩
  have payFit (x : Fin X) : (payload base b M (stem x)).Fits w top:=fits_total _ (live x) _
  let count (x : Fin X) (h : Fin H) (g : Fin G) : Cell b:=⟨_,limit x h g⟩
  have sums (x : Fin X) : Source (payload base b M (stem x)) (count x) M done:=by
    intro r
    have readRow (j : Fin K) : (Expr.lookup B₀ (stem x j)).eval done ((row H G M r).val:Word w)=
        (packed b (fun h g=>(face false (inbound x j h g)).toNat) r:Word w):=by
      let f:=fun h g=>raw b (inbound x j h g)
      change B₀.read done ((stem x j).eval done _)=_
      rw [keep _ (slots x j) f (bits x j) r,bank_read B₀ done (data f r).isLt bankFits]
      have actual:=DescentOrdinaryAtomFieldRAM.ROM.read P _ base m 0 (pageRoom b M 0) (data f r)
      change done (B₀.base+(data f r).val)=(piece b (scaled b) (data f r):Word w) at actual
      rw [actual,piece_data _ (zero_scale b)]
      have decodeStem (h : Fin H) (g : Fin G) :
          decode b (raw b (inbound x j h g)) = inbound x j h g :=
        decode_raw _ (stemRoom x j h g)
      simp only [f, scaled, decodeStem]
    have tot:=DescentPackedSumWords.eval_sum _ _ done _ readRow (List.finRange K)
    rw [←List.ofFn_eq_map,List.sum_ofFn,packed_sum] at tot
    change (payload base b M (stem x)).eval done _=_
    exact tot.trans (congrArg (fun n : ℕ=>(n:Word w)) (packed_data b (count x) r))
  have static:=binary_mounted (fuse b) M P (width b M) base m (pageRoom b M) Fin.succ (fun j=>rfl)
  have zip (x : Fin X) : DescentPackedZip.Fits (tabs base b M) (head x) (payload base b M (stem x)) (b*7) b M top w :=
    ⟨ProtocolRAMGeneratedWrite.fits_mono _ earlyTop (early x),payFit x,
     bank_room P _ base _ _ (pageRoom b M _) le_rfl space,bank_room P _ base _ _ (pageRoom b M _) le_rfl space,rfl,rfl⟩
  refine ⟨cpu.1,?_,?_,stay,cpu.2,?_⟩
  · intro x;have h:=zip x;simp [issue,Tables.read,Expr.Fits,h.left,h.right,h.shift,h.apply]
  · intro x
    have got:=read_data _ _ _ top (zip x) (fuse b) (zero_fuse b) done static _ _
      (keep _ (early x) _ (heads x)) (sums x)
    have decodeShape (h : Fin H) (g : Fin G) :
        decode b (raw b (shape x h g)) = shape x h g := decode_raw _ (bounded x h g)
    simpa only [issue, fuse, decodeShape, count] using got
  · exact DescentOrdinaryAtomFieldRAM.ROM.cheap _ _ _ _

theorem issue_work (base b M : ℕ) (q : Expr) (inputs : Fin K→Expr) (s : ℕ)
    (bound : ∀j,(inputs j).work≤ s) :
    (issue base b M q inputs).work≤q.work+(1+K*(s+6))+11:=by
  rw [issue,DescentPackedZip.work]
  apply Nat.add_le_add_right
  apply Nat.add_le_add_left
  have h:=work_total (fun j=>Expr.lookup (unary base b M) (inputs j)) (s+5)
    (fun j=>Nat.add_le_add_right (bound j) 5) (List.finRange K)
  simpa [payload,List.length_finRange,Nat.add_assoc] using h

end
end Hierarchy.DescentResetTrunkIssue

end OAI
