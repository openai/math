import OAI.Hierarchy.DescentSignedPrefix

namespace OAI
/-! The public tariffs count every emitted scan and actual native
instruction name, independently of memory contents. -/
namespace Hierarchy.DescentDatedAddressBook.SignedPrefix
open DescentSixParty.Chronology Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentStaticWordColumn (names names_seq names_scan names_mount)
noncomputable section

def Job.within (limit:ℕ):Job→Prop
  | .words _ _=>True
  | .columns n _ _ e=>∀i<n,(e i).work≤limit
def Job.clocks (limit:ℕ):Job→ℕ
  | .words n _=>4+10*n
  | .columns n rows _ _=>4+n*(4+rows*(2*limit+4))
def Job.textSize (limit:ℕ):Job→ℕ
  | .words n _=>15*(n+1)
  | .columns n _ _ _=>15+n*(11+4*limit)

private theorem column_text (w base n pitch limit start size:ℕ) (e:ℕ→Expr)
    (expr : ∀ i : ℕ, start ≤ i → i < start + size → (e i).work ≤ limit) :
    names (program w (DescentPackedFlowBatch.passes base n pitch e start size))≤15+size*(11+4*limit):=by
  induction size generalizing start with
  | zero=>simp [DescentPackedFlowBatch.passes,program,names_scan,Expr.work]
  | succ size ih=>
    have lo:=expr start le_rfl (by omega)
    have rest:=ih (start+1) (fun i low high=>expr i (by omega) (by omega))
    rw [DescentPackedFlowBatch.passes,program,names_seq,Pass.procedure,names_scan]
    change 11+4*(e start).work+_≤15+(size+1)*(11+4*limit)
    rw [Nat.add_mul,Nat.one_mul]
    omega

theorem Job.invoice (w base limit:ℕ) (j:Job) (fit:j.within limit):
    (j.atBase base w).ticks≤j.clocks limit ∧ names (j.atBase base w).program≤j.textSize limit:=by
  cases j with
  | words n v=>exact ⟨le_rfl,(names_mount w base v n).le⟩
  | columns n rows p e=>exact ⟨DescentPackedFlowBatch.tariff base rows p n e limit fit,
    column_text w base rows p limit 0 n e (fun i _ hi=>fit i (by simpa using hi))⟩

theorem invoice {w:ℕ} (tail:ℕ→NativePhase w) (jobs:List Job) (base limit:ℕ)
    (cost:∀j∈jobs,j.within limit):
    (build w tail jobs base).ticks≤(jobs.map (Job.clocks limit)).sum+(tail (finish jobs base)).ticks ∧
    names (build w tail jobs base).program≤(jobs.map (Job.textSize limit)).sum+names (tail (finish jobs base)).program:=by
  induction jobs generalizing base with
  | nil=>simp [build,finish]
  | cons j js ih=>
    have job:=j.invoice w base limit (cost _ (by simp))
    have next:=ih (base+j.width) (fun z member=>cost _ (by simp [member]))
    simp only [build,finish,NativePhase.seq,names_seq,List.map_cons,List.sum_cons]
    omega

def Job.pitched:Job→Prop
  | .words _ _=>True
  | .columns _ r p _=>r≤p ∧ 1≤p

theorem Job.budgets (j:Job) (lim:ℕ) (p:j.pitched):
    j.clocks lim≤20*(lim+1)*(1+j.width) ∧ j.textSize lim≤20*(lim+1)*(1+j.width):=by
  cases j with
  | words n v=>
    change 4+10*n≤20*(lim+1)*(1+n) ∧ 15*(n+1)≤20*(lim+1)*(1+n)
    constructor <;> nlinarith [Nat.zero_le (lim*n)]
  | columns n r pitch e=>
    obtain ⟨hr,hp⟩:=p
    change 4+n*(4+r*(2*lim+4))≤20*(lim+1)*(1+n*pitch) ∧ 15+n*(11+4*lim)≤20*(lim+1)*(1+n*pitch)
    have np:n≤n*pitch:=Nat.le_mul_of_pos_right n hp
    have nr:n*r≤n*pitch:=Nat.mul_le_mul_left n hr
    have nl:=Nat.mul_le_mul_right lim np
    have nrl:=Nat.mul_le_mul_right lim nr
    constructor <;> nlinarith [Nat.zero_le (n*pitch*lim)]

theorem width_sum (js:List Job) (base:ℕ):finish js base=base+(js.map Job.width).sum:=by
  induction js generalizing base with
  | nil=>simp [finish]
  | cons j js ih=>simp [finish,ih,Nat.add_assoc]

theorem budgets (js:List Job) (K:ℕ) (pos:∀j∈js,j.pitched):
    (js.map (Job.clocks K)).sum≤20*(K+1)*(js.length+(js.map Job.width).sum) ∧
    (js.map (Job.textSize K)).sum≤20*(K+1)*(js.length+(js.map Job.width).sum):=by
  induction js with
  | nil=>simp
  | cons j js ih=>
    have a:=j.budgets K (pos _ (by simp))
    have as:=ih (fun z mem=>pos _ (List.mem_cons_of_mem _ mem))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    constructor <;> nlinarith [a.1,a.2,as.1,as.2]

end
end Hierarchy.DescentDatedAddressBook.SignedPrefix

end OAI
