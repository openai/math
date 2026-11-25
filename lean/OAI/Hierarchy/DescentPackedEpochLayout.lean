import OAI.Hierarchy.DescentSeedHeaderFloorNumbers
import OAI.Hierarchy.DescentPackedEpochShelves

namespace OAI
/-! # A concrete output layout for all packed verdicts and their final bit -/
namespace Hierarchy.DescentPackedEpochShelves
open DescentTerminalEpochChart DescentPackedProfileTape DescentPackedProfileValidity DescentPackedProfileInstall DescentPackedEpochFold
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {A : Type} {w : ℕ}


def phases (head C r : ℕ) (count exterior : ℕ→ℕ) :
    ℕ→List (Shelf A)→List (Stage A)
  | _,[]=>[]
  | o,p::ps=>
    ⟨p.src,stageBanks head C r p (count p.ordinal),r,exterior p.ordinal,o,o+slots p.src.seats r+1⟩::
      phases head C r count exterior (o+stepRows r p) ps

theorem phase_sources (head C r : ℕ) (count exterior : ℕ→ℕ) (o : ℕ) (ps : List (Shelf A)) :
    (phases head C r count exterior o ps).map Stage.source=ps.map Shelf.src := by
  induction ps generalizing o with | nil=>rfl | cons p ps ih=>simp [phases,ih]

theorem phase_mem (head C r : ℕ) (count exterior : ℕ→ℕ) (o : ℕ) (ps : List (Shelf A))
    (s : Stage A) (present : s∈phases head C r count exterior o ps) :
    ∃p∈ps, s.source=p.src ∧ s.banks=stageBanks head C r p (count p.ordinal) ∧ s.grain=r ∧
      s.exterior=exterior p.ordinal ∧ o ≤ s.out ∧ s.dest=s.out+slots p.src.seats r+1 ∧
      s.dest < o+(ps.map (stepRows r)).sum := by
  induction ps generalizing o with
  | nil=>simp [phases] at present
  | cons p ps ih=>
    rcases List.mem_cons.mp present with rfl|after_
    · refine ⟨p,by simp,rfl,rfl,rfl,rfl,le_rfl,rfl,?_⟩
      change o+slots p.src.seats r+1 < o+((slots p.src.seats r+2)+(ps.map (stepRows r)).sum)
      omega
    · obtain ⟨a,in_,fields,bank,grain,ext,lo,eqn,h⟩:=ih _ after_
      refine ⟨a,by simp [in_],fields,bank,grain,ext,by omega,eqn,?_⟩
      simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using h

theorem order (head C r : ℕ) (count exterior : ℕ→ℕ) (low o prev : ℕ) (ps : List (Shelf A))
    (below : prev < o) (start : low ≤ o) (space : o+(ps.map (stepRows r)).sum+1 < 2^w) :
    Order w low prev (o+(ps.map (stepRows r)).sum) (phases head C r count exterior o ps) := by
  induction ps generalizing o prev with
  | nil=>exact ⟨by simpa using below,by simpa using start,by simpa using space⟩
  | cons p ps ih=>
    change prev < o ∧ _
    refine ⟨below,?_⟩
    have f:=ih (o+stepRows r p) (o+slots p.src.seats r+1)
      (by unfold stepRows;omega) (by omega) (by simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using space)
    simpa only [List.map_cons,List.sum_cons,Nat.add_assoc] using f

def controls (lo C r : ℕ) (ss : List (Source A)) (count exterior : ℕ→ℕ) :=
  let table:=lo+extent r ss
  let o:=end_ table C r
  phases table C r count exterior o (shelves r lo 0 ss)

def final (lo C r : ℕ) (ss : List (Source A)) :=
  end_ (lo+extent r ss) C r+((shelves r lo 0 ss).map (stepRows r)).sum

theorem ready (lo C r seed : ℕ) (ss : List (Source A)) (count exterior : ℕ→ℕ) (z : A→Bool) (old : Memory w)
    (same : DescentTerminalEpochDecoder.Uniform C ss) (pos : 0 < r) (first : seed < lo)
    (below : ∀p∈shelves r lo 0 ss,count p.ordinal < lo ∧ exterior p.ordinal < lo)
    (wide : ∀s∈ss, slots s.seats r*r < 2^w) (room : final lo C r ss+1 < 2^w) :
    let start:=end_ (lo+extent r ss) C r
    let ts:=controls lo C r ss count exterior
    let m:=header lo C r ss z old
    Order w start seed (final lo C r ss) ts ∧ (∀s∈ts,Paid w start s) ∧
      (∀s∈ts,Reads s.banks m s.source.pin z s.grain) ∧ ts.map Stage.source=ss := by
  let ps:=shelves r lo 0 ss
  let table:=lo+extent r ss
  let o:=end_ table C r
  let ts:=controls lo C r ss count exterior
  have tableTop : table ≤ o:=by change table ≤ (table+_)+_;omega
  have oldLo : lo ≤ table:=Nat.le_add_right _ _
  have outFit : o+(ps.map (stepRows r)).sum+1 < 2^w:=room
  have limits (p : Shelf A) (hp : p∈ps) : tablesBase p.base p.src.seats r ≤ table :=
    (next p.base r p.src).trans_le (placed r lo 0 ss p hp).2
  have in_ (p : Shelf A) (hp : p∈ps) : p.src∈ss :=
    sources r lo 0 ss ▸ List.mem_map_of_mem (f:=Shelf.src) hp
  refine ⟨order table C r count exterior o o seed ps (by omega) le_rfl outFit,?_,?_,
    (phase_sources table C r count exterior o ps).trans (sources r lo 0 ss)⟩
  · intro s hs
    obtain ⟨p,hp,src,bs,grain,ext,low,dest,ending⟩:=phase_mem table C r count exterior o ps s hs
    have pc:=below p hp
    have e:=limits p hp
    have uniform:=same _ (in_ p hp)
    have srcLo : lo ≤ p.base:=(placed r lo 0 ss p hp).1
    let S:=sourceBank p.base p.src.seats r
    let T:=startsBank p.base p.src.seats r
    let B:=shifts table r
    let D:=dict table C r
    have S₀ : S.base+S.size=T.base:=rfl
    have T₀ : T.base+T.size ≤ table:=e
    have B₀ : B.base=table:=rfl
    have B₁ : B.base+B.size=D.base:=rfl
    have D₀ : D.base+D.size=o:=rfl
    have fit (bank : Bank) (bounds : bank.base+bank.size ≤ o) : bank.Fits w s.out :=
      ⟨Nat.two_pow_pos _,by omega,by omega⟩
    have exteriorLow : s.exterior < o := by
      rw [ext]
      exact pc.2.trans_le (oldLo.trans tableTop)
    refine ⟨?_,grain.symm ▸ pos,low,exteriorLow,?_,by omega,?_⟩
    · rw [bs,src,grain,uniform]
      exact ⟨fit S (by omega),fit T (by omega),fit B (by omega),fit D (by omega),
        fit ⟨count p.ordinal,0⟩ (by change count p.ordinal+1 ≤ o;omega),Nat.le_pow_clog (by decide) _,
        Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,Nat.le_pow_clog (by decide) _,
        wide _ (in_ p hp),by omega⟩
    · rw [dest,rows,src,grain]
    · intro bank mem
      rw [bs] at mem
      simp only [List.mem_cons,List.not_mem_nil,or_false] at mem
      rcases mem with h|h|h|h|h <;> subst bank
      · change S.base+S.size ≤ o;omega
      · change T.base+T.size ≤ o;omega
      · change B.base+B.size ≤ o;omega
      · change D.base+D.size ≤ o;omega
      · change count p.ordinal+1 ≤ o;omega
  · intro s hs
    obtain ⟨p,hp,src,bs,grain,_⟩:=phase_mem table C r count exterior o ps s hs
    rw [src,bs,grain]
    exact stored lo C r ss z old same p hp (count p.ordinal)
theorem validate {P Z U : Type} {bits : Z→P→Bool} {ok : (P→Bool)→Prop} {src : U→Z}
    (b : Chart bits ok src) (z : b.Pin→Bool) (old : Memory w) (lo C r seed : ℕ) (count exterior : ℕ→ℕ)
    (same : DescentTerminalEpochDecoder.Uniform C b.layout) (pos : 0 < r) (seedLow : seed < lo)
    (below : ∀p∈shelves r lo 0 b.layout,count p.ordinal < lo ∧ exterior p.ordinal < lo)
    (wide : ∀s∈b.layout,slots s.seats r*r < 2^w) (room : final lo C r b.layout+1 < 2^w)
    (orig : old seed=0 ↔ ok (z∘b.seed))
    (counts : List.IsPrefix ((b.rows z).map Observation.count)
      ((controls lo C r b.layout count exterior).map fun s=>(old s.banks.count.base).val)) :
    let ts:=controls lo C r b.layout count exterior
    let m:=header lo C r b.layout z old
    let dst:=final lo C r b.layout
    (fold w seed dst ts).Spec (·=m) (fun _ o=>
      (o dst=if (∃t,b.read z=some t) ∧ ∀s∈ts,old s.exterior=0 then 0 else 1) ∧
      ∀i < end_ (lo+extent r b.layout) C r,o i=m i) (bill seed dst ts) ∧ CheapCode (fold w seed dst ts) := by
  let ts:=controls lo C r b.layout count exterior
  let m:=header lo C r b.layout z old
  let base:=lo+extent r b.layout
  let o:=end_ base C r
  obtain ⟨sp,pr,rd,is_⟩:=ready lo C r seed b.layout count exterior z old same pos seedLow below wide room
  have used (s : Stage b.Pin) (hs : s∈ts) : m s.banks.count.base=old s.banks.count.base ∧ m s.exterior=old s.exterior := by
    obtain ⟨p,hp,_,bs,_,ext,_⟩:=phase_mem base C r count exterior o (shelves r lo 0 b.layout) s hs
    have h:=below p hp
    rw [bs,ext]
    exact ⟨frame lo C r b.layout z old h.1,frame lo C r b.layout z old h.2⟩
  have sameCount : ts.map (fun s=>(m s.banks.count.base).val)=ts.map (fun s=>(old s.banks.count.base).val) :=
    List.map_congr_left fun s hs=>congrArg Fin.val (used s hs).1
  have sameExt : (∀s∈ts,m s.exterior=0) ↔ ∀s∈ts,old s.exterior=0 := by
    constructor <;> intro h s hs
    · exact ((used s hs).2.symm.trans (h s hs))
    · exact ((used s hs).2.trans (h s hs))
  have initial : m seed=0 ↔ ok (z∘b.seed):=by rw [show m seed=old seed from frame lo C r b.layout z old seedLow,orig]
  have real:=validated b z m ts o seed (final lo C r b.layout) sp pr rd initial is_ (sameCount.symm ▸ counts)
  simpa only [sameExt] using real


end
end Hierarchy.DescentPackedEpochShelves

end OAI
