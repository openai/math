import OAI.Hierarchy.DescentDonorNumericHeads
import OAI.Hierarchy.DescentPackedActorHeads
import OAI.Hierarchy.DescentPackedMatchedGather
import OAI.Hierarchy.DescentPackedMatchedAll

namespace OAI
/-! # Native gather of own and neighboring resolved actor registers -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Owners
open DescentSIMDLookup DescentPackedZip DescentPackedColony ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

variable {r D p d H G M w : ℕ}
theorem addressed_read (B n : ℕ) (l : Bool) (u : Panel r D p d) (x : Fin r) :
    addressed (render r D p d B n (register l u)) x=resolved B n u l x := by
  let q:=resolved B n u l x
  rw [render_register]
  simp only [addressed,Equiv.symm_apply_apply]
  refine Prod.ext ?_ (Prod.ext ?_ ?_)
  · exact read_cell u B n l x 0
  · exact read_cell u B n l x 1
  · exact read_cell u B n l x 2

def routeWord (bits : ℕ) (u : Walk) : Cell (bits*4) :=
  encode bits 4 ![word _ u.1,word _ u.2.1,word _ u.2.2.1,word _ u.2.2.2]
def headWord (bits : ℕ) (h : Heads) : Cell ((bits*4)*8) :=
  encode (bits*4) 8 (Fin.cases (h.born.isSome.toNat:Cell (bits*4)) (Fin.cases (routeWord bits h.old)
    (fun j=>(h.born.map (fun q=>routeWord bits (q j))).getD 0)))

def outputBits (r D p d : ℕ) := ((digits r D d*4)*8)*(r*p)

def report (r D p d B profile : ℕ) (raw : Cell (inputBits r D p d)) (directory : Cell (((digits r D d*3)*r)*(D+1))) :
    Cell (outputBits r D p d) :=
  if raw=0 then 0 else
    let b : Cell 1×Cell (d*fields r D p):=finProdFinEquiv.symm (finCongr (pow_add 2 1 (d*fields r D p)) raw)
    let u:=decodePanel b.2
    let rows:=(encode ((digits r D d*3)*r) (D+1)).symm directory
    encode ((digits r D d*4)*8) (r*p) (fun j=>
      let (block,slot):=finProdFinEquiv.symm j
      headWord (digits r D d) (actorHeads B profile u (decide (b.1.val=1)) (addressed (rows 0))
        (fun peer=>addressed (rows peer.succ)) block slot))

private theorem zero_encode (m n : ℕ) : encode m n (fun _=>0)=0 := by
  apply Fin.ext
  change (finFunctionFinEquiv (fun _ : Fin n=>(0:Cell m))).val=0
  simp []

theorem active_register (u : Panel r D p d) (l : Bool) (x : Fin r) (live : u.winner x≠0) :
    register l u≠0 := by
  intro z
  have num:=congrArg Fin.val z
  change (finProdFinEquiv ((l.toNat:Cell 1),encodePanel u)).val=0 at num
  rw [finProdFinEquiv_apply_val] at num
  dsimp only at num
  have sub:(encodePanel u).val=0:=by omega
  have empty:encodePanel u=0:=Fin.ext sub
  have full:=congrArg (fun c=>(decodePanel (r:=r) (D:=D) (p:=p) c).winner x) empty
  rw [decode_encode_panel] at full
  apply live
  rw [full]
  change (encode d (fields r D p)).symm 0 _=0
  rw [(encode d (fields r D p)).symm_apply_eq.mpr (zero_encode d (fields r D p)).symm]

theorem from_active (u : Panel r D p d) (l : Bool) (B n : ℕ) (x : Fin r) (t : Fin p) (live : u.winner x≠0)
    (rows : Fin (D+1)→Register r D d) :
    (encode ((digits r D d*4)*8) (r*p)).symm
      (report r D p d B n (register l u) (encode _ (D+1) rows)) (finProdFinEquiv (x,t))=
      headWord (digits r D d) (actorHeads B n u l (addressed (rows 0)) (fun v=>addressed (rows v.succ)) x t) := by
  have active_:=active_register u l x live
  have parts := finProdFinEquiv.symm_apply_apply (x,t)
  have block : (finProdFinEquiv (x,t)).divNat = x := congrArg Prod.fst parts
  have slot : (finProdFinEquiv (x,t)).modNat = t := congrArg Prod.snd parts
  cases l <;> simp_all [report,register,decode_encode_panel]

def registers (here : Fin H→Fin G→Register r D d) (roster : Fin H→Fin D→Option (Fin H)) (v : Fin H) (g : Fin G) :
    Fin (D+1)→Register r D d :=
  Fin.cases (here v g) (fun t=>(roster v t).elim 0 fun u=>here u g)

def expression (roster : Ports D) (own : Bank) (H : ℕ) : Fin (D+1)→Expr :=
  Fin.cases (.lookup own .row) (peerExpr roster own H)

theorem from_registers (ro : Ports D) (own : Bank) (tables : Fin (D+1)→Tables) (out : ℕ)
    (bounds : Gather.Bounds (w:=w) (d:=(digits r D d*3)*r) (M:=M) tables (expression ro own H) out)
    (access : Accessible ro own H G M w out) (extent : H*chunks G M≤own.size) (good : own.Fits w out)
    (roster : Fin H→Fin D→Option (Fin H)) (here : Fin H→Fin G→Register r D d) (m : Memory w)
    (mounted : Mounted ro roster m G M) (old : Reads own here M m)
    (static : ∀i,Static (tables i) (Gather.setField (d:=(digits r D d*3)*r) i) M m) :
    Source (Gather.assembly tables (expression ro own H))
      (fun v g=>encode ((digits r D d*3)*r) (D+1) (registers here roster v g)) M m := by
  have loaded (i : Fin (D+1)) : Source (expression ro own H i) (fun v g=>registers here roster v g i) M m := by
    induction i using Fin.cases with
    | zero=>simpa [expression,registers] using source_column own out good m here extent old
    | succ t=>simpa [expression,registers] using peerSource ro own out access roster m mounted here old t
  have full:=Gather.collected tables (expression ro own H) out bounds m static (registers here roster) loaded (List.finRange (D+1))
  simpa only [Gather.assembly,List.mem_finRange,ite_true] using full

def aggregate (tabs : Fin (D+1)→Tables) (ro : Ports D) (own : Bank) (H : ℕ) :=
  Gather.assembly tabs (expression ro own H)

theorem clock (tabs : Fin (D+1)→Tables) (ro : Ports D) (own : Bank) (H : ℕ) :
    (aggregate tabs ro own H).work≤1+(D+1)*(64+11) := by
  have each (i : Fin (D+1)) : (expression ro own H i).work≤64 := by
    induction i using Fin.cases with
    | zero=>simp only [expression,Fin.cases_zero,Expr.work]; decide
    | succ t=>simp only [expression,Fin.cases_succ,peerExpr,neighborID,Expr.work]; decide
  simpa only [aggregate,Gather.assembly,List.length_finRange] using Gather.collect_work tabs (expression ro own H) (List.finRange (D+1)) 64 each

/-- Both original terrain and the neighbor register gathering run on the same
public host-and-group chunk. The only dynamic peer keys are fetched from the
shared physical roster. -/
theorem run (ro : Ports D) (raw own : Bank) (tabs : Fin (D+1)→Tables) (result : Tables) (out B n : ℕ)
    (bounds : Gather.Bounds (w:=w) (d:=(digits r D d*3)*r) (M:=M) tabs (expression ro own H) out)
    (access : Accessible ro own H G M w out) (room : out+H*chunks G M<2^w)
    (space : H*chunks G M≤own.size) (fitOwn : own.Fits w out) (oldSpace : H*chunks G M≤raw.size)
    (limits : Fits result (.lookup raw .row) (aggregate tabs ro own H) (inputBits r D p d) (((digits r D d*3)*r)*(D+1)) M out w)
    (roster : Fin H→Fin D→Option (Fin H)) (live : Fin H→Fin G→Cell (inputBits r D p d)) (current : Fin H→Fin G→Register r D d) (m : Memory w)
    (mounted : Mounted ro roster m G M) (res : Reads own current M m) (src : Reads raw live M m)
    (stat : ∀i,Static (tabs i) (Gather.setField (d:=(digits r D d*3)*r) i) M m)
    (rom : Static result (report r D p d B n) M m) :
    let e:=result.read (.lookup raw .row) (aggregate tabs ro own H)
    let last:=image out (H*chunks G M) e m
    (scan w out (H*chunks G M) e).Exec m last (4+H*chunks G M*(2*e.work+4)) ∧
      ∀q : Row H G M,last (out+(row H G M q).val)=
        ((data (fun v g=>report r D p d B n (live v g) (encode _ (D+1) (registers current roster v g))) q).val:Word w) := by
  intro e last
  have data:=from_registers ro own tabs out bounds access space fitOwn roster current m mounted res stat
  have old:=source_column raw out (by simpa [Expr.Fits] using limits.left.1) m live oldSpace src
  have noPad : report r D p d B n 0 0=0 := by simp [report]
  have proof:=read_data result (.lookup raw .row) (aggregate tabs ro own H) out limits _ noPad m rom live _ old data
  refine ⟨scan_exec out _ _ m (by simp [e,Tables.read,Expr.Fits,limits.left.1,limits.right,limits.shift,limits.apply]) room,?_⟩
  intro q
  have ok:=(row H G M q).isLt
  simpa [last,image,fillSegment,Nat.cast_add,show out≤out+(row H G M q).val ∧ out+(row H G M q).val<out+H*chunks G M by omega] using proof q

end
end Hierarchy.DescentPacking.PackedMatch.Local.Owners

end OAI
