import OAI.Hierarchy.DescentFundedCensusRate
import OAI.Hierarchy.DescentFundedCensusInvoice
import OAI.Hierarchy.DescentFundedCensusRoles
import OAI.Hierarchy.DescentFundedArrivals

namespace OAI
/-! # Actual packed predecessor costs for both trunks and both root families -/
namespace Hierarchy.DescentFundedCensus
open DescentDatedAddressBook DescentSIMDLookup DescentPackedZip DescentCommonHost DescentCommonPalette
open DescentContacts DescentRelativeContacts DescentColonies.SplitRAM ProtocolRAM DescentStaticWordColumn
open LinearAlgebra.SpectralBooks ThreeFlat RouteUnits Expander NonlinearExpanders
open scoped Classical
noncomputable section

theorem Arrivals.work (base D cap b L M : ℕ) (signed : Fin (2*cap)→Bank) :
    (Arrivals.expr base D cap b L M (fun j=>.lookup (signed j) .row)).work=1+(2*cap)*13 :=by
  have every (js : List (Fin (2*cap))) :
      (total (fun j=>Expr.lookup (Arrivals.flags base D cap b L M) (.lookup (signed j) .row)) js).work=1+js.length*13 :=by
    induction js with
    | nil=>rfl
    | cons j js ih=>simp only [total,Expr.work,ih,List.length_cons,Nat.succ_mul];omega
  simpa only [Arrivals.expr,List.length_finRange] using every (List.finRange (2*cap))

def roleWork (cap : ℕ) := 7+(2*cap)*13

theorem job_work {n d r : ℕ} (board : NonlinearExpanders.Graph n d)
    (Ht C packet batch bits oldCap f D cap field header inputBits L M base : ℕ)
    (old stencil present : Bank) (signed : Fin (2*cap)→Bank) (root : Bool→DescentResetHostSize.Code r×Option (Fin (2^n))→Bank)
    (actor : Node Unit (Unit×Endpoint (2^n)) (rotor board).Site) :
    let io : Ports r n:=⟨.lookup old .row,Arrivals.expr base D cap inputBits L M (fun j=>.lookup (signed j) .row),
      .lookup stencil .row,fun side label=>.lookup (root side label) .row⟩
    let j:=compile (Ht:=Ht) board C packet batch bits oldCap f D cap field header io (.lookup present .row) actor
    j.first.work≤roleWork cap ∧ j.second.work≤roleWork cap ∧ j.present.work≤roleWork cap :=by
  intro io j
  let K:=roleWork cap
  have read (B : Bank) : (Expr.lookup B .row).work≤K:=Nat.le_add_right ..
  have one : (Expr.lit 0).work≤K:=(show 1≤7 by decide).trans (Nat.le_add_right ..)
  have relay : io.relay.work≤K :=by
    dsimp only [io]
    rw [Arrivals.work]
    dsimp [K,roleWork]
    omega
  rcases actor with ⟨side,⟨_,label⟩⟩|⟨side,t,role⟩|⟨side,⟨_,label⟩,path⟩
  · cases side <;> exact ⟨read _,by first | exact read _ | exact relay,read _⟩
  · exact ⟨read _,one,read _⟩
  · by_cases legal : label.1.1≤r ∧ label.1.2<2^label.1.1 ∧ path.length≤Ht
    · simp only [j,compile,legal]
      exact ⟨read _,read _,read _⟩
    · simp only [j,compile,legal,dite_false]
      exact ⟨one,one,read _⟩

namespace Shape
variable {ι : ℕ→Type*} (s : ∀h,ι h→Shape)
theorem role_time_rate_add (extra : ℕ) (r : ScalarRoom s) (base w cap : ∀h,ι h→ℕ) (capacity : Bounded cap)
    (job : ∀h i,Fin (s h i).jobs→Job (s h i).bits)
    (inputs : ∀h i j,let x:=job h i j;x.first.work≤roleWork (cap h i)+extra ∧
      x.second.work≤roleWork (cap h i)+extra ∧ x.present.work≤roleWork (cap h i)+extra) :
    Bounded (fun h i=>ticks (s:=s h i) (job h i) (base h i)+7*names (program (s:=s h i) (job h i) (w h i) (base h i))) :=by
  obtain ⟨A,hw⟩:=r.lookup
  let c n:=Bounded.const (ι:=ι) n
  have K₀ : Bounded (fun h i=>roleWork (cap h i)):=(c 7).add (((c 2).mul capacity).mul (c 13))
  have K:=K₀.add (c extra)
  have lim:=((c 3).mul K).add (c 22)
  have offsets : Bounded (fun h i=>2^(s h i).width):=Bounded.pow_of_linear (K:=A) hw
  have cols:=((c 2).mul (r.jobs.add (c 1))).mul offsets
  have groups : Bounded (fun h i=>chunks (s h i).groups (s h i).lanes) :=
    (r.groups.add r.lanes).of_le fun _ _=>(Nat.div_le_self ..).trans (Nat.sub_le ..)
  have rows:=r.hosts.mul groups
  have t:=((c 4).add ((c 10).mul cols)).add ((c 4).add (r.jobs.mul ((c 4).add (rows.mul (((c 2).mul lim).add (c 4))))))
  have n:=((c 15).mul (cols.add (c 1))).add ((c 15).add (r.jobs.mul ((c 11).add ((c 4).mul lim))))
  apply (t.add ((c 7).mul n)).of_le
  intro h i
  have out:=invoice (s:=s h i) (job h i) (base h i) (w h i) (roleWork (cap h i)+extra)
    (fun j=>(inputs h i j).1) (fun j=>(inputs h i j).2.1) (fun j=>(inputs h i j).2.2)
  exact Nat.add_le_add out.1 (Nat.mul_le_mul_left 7 out.2)

theorem role_time_rate (r : ScalarRoom s) (base w cap : ∀h,ι h→ℕ) (capacity : Bounded cap)
    (job : ∀h i,Fin (s h i).jobs→Job (s h i).bits)
    (inputs : ∀h i j,let x:=job h i j;x.first.work≤roleWork (cap h i) ∧
      x.second.work≤roleWork (cap h i) ∧ x.present.work≤roleWork (cap h i)) :
    Bounded (fun h i=>ticks (s:=s h i) (job h i) (base h i)+7*names (program (s:=s h i) (job h i) (w h i) (base h i))) :=by
  apply role_time_rate_add s 0 r base w cap capacity job
  simpa using inputs

end Shape
end
end Hierarchy.DescentFundedCensus

end OAI
