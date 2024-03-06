(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From HB Require Import structures.
From mathcomp Require Import all_ssreflect ssralg ssrint ssrnum finmap matrix.
From mathcomp Require Import rat interval zmodp vector fieldext falgebra.
From mathcomp Require Import mathcomp_extra boolp classical_sets functions.
From mathcomp Require Import cardinality set_interval Rstruct.
Require Import ereal reals signed topology prodnormedzmodule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Import numFieldTopology.Exports.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.

HB.structure Definition PointedNmodule := {M of Pointed M & GRing.Nmodule M}. 
HB.structure Definition PointedZmodule := {M of Pointed M & GRing.Zmodule M}. 
HB.structure Definition FilteredNmodule := {M of Filtered M M & GRing.Nmodule M}.
HB.structure Definition FilteredZmodule := {M of Filtered M M & GRing.Zmodule M}.
HB.structure Definition NbhsNmodule := {M of Nbhs M & GRing.Nmodule M}.
HB.structure Definition NbhsZmodule := {M of Nbhs M & GRing.Zmodule M}.
HB.structure Definition TopologicalNmodule := {M of Topological M & GRing.Nmodule M}.
HB.structure Definition TopologicalZmodule := {M of Uniform M & GRing.Zmodule M}.

(* TODO: put this notation in classical_sets.v
   and clean in topology.v cantor.v *)
Local Notation "A ^-1" := ([set xy | A (xy.2, xy.1)]) : classical_set_scope.

Definition convex (R : ringType) (M : lmodType R) (A : set M) :=
  forall x y lambda, lambda *: x + (1 - lambda) *: y \in A. 
 
HB.mixin Record Uniform_isEvt (R : numDomainType) E of Uniform E & GRing.Lmodule R E := {
    add_continuous : continuous (fun x : E*E => x.1 + x.2); (*continuous (uncurry (@GRing.add E))*)
    scale_continuous : continuous (fun z: R^o * E => z.1 *: z.2);
    (* continuous (uncurry (@GRing.scale R E) : R^o * E -> E) *)
    locally_convex : exists B : set (set E), (forall b, b \in B -> convex b) /\ (basis B)
  }.

HB.structure Definition Evt (R : numDomainType) :=
  {E of Uniform_isEvt R E & Uniform E & GRing.Lmodule R E}. 

HB.factory Record TopologicalLmod_isEvt (R : numFieldType) E
      of Topological E & GRing.Lmodule R E := {
    add_continuous : continuous (uncurry (@GRing.add E));
    scale_continuous : continuous (uncurry (@GRing.scale R E) : R^o * E -> E);
    locally_convex : exists B : set (set E), (forall b, b \in B -> convex b) /\ (basis B)     
  }.

HB.builders Context R E of TopologicalLmod_isEvt R E.

  Definition entourage : set_system (E * E):=
  fun P=> exists U, nbhs 0 U /\ (forall xy : E * E, (xy.1 - xy.2) \in U -> xy \in P).

  Lemma entourage_filter : Filter entourage.
  Proof.
    split.
      exists [set: E]; split; first by apply: filter_nbhsT.
        by move => xy //=. 
        move => P Q; rewrite /entourage nbhsE //=.
        move => [U [[B B0] BU Bxy]]  [V [[C C0] CV Cxy]]. 
        exists (U`&`V); split.
          exists (B`&`C); first by apply/open_nbhsI.
          by apply:setISS.
       move => xy; rewrite !in_setI.
       move/andP => [xyU xyV]; apply/andP;split; first by apply:Bxy.
       by apply: Cxy.
    move => P Q PQ; rewrite /entourage /= => [[U [HU Hxy]]]; exists U; split => //.
    by move => xy /Hxy /[!inE] /PQ. 
  Qed.
  
  Lemma entourage_refl_subproof :
    forall A : set (E * E), entourage A -> [set xy | xy.1 = xy.2] `<=` A.
  Proof. (*why bother with \in ?*)
    rewrite /entourage => A [/=U [U0 Uxy]] xy //= /eqP; rewrite -subr_eq0 => /eqP xyE. 
    by rewrite -in_setE; apply: Uxy; rewrite xyE in_setE; apply: nbhs_singleton.
  Qed.   
 
  Lemma nbhs0N: forall (U : set E), nbhs 0 U -> nbhs 0 (-%R @` U).
  Proof.
    move => U U0. move: (@scale_continuous ((-1,0)) U); rewrite /= scaler0 => /(_ U0).
    move => [] //= [B] B12  [B1 B2] BU.  
    near=> x; move =>  //=; exists (-x); last by rewrite opprK.
    rewrite -scaleN1r; apply: (BU (-1,x)); split => //=; last first.
      by near:x; rewrite nearE.                            
    move: B1 => [] //= ? ?; apply => [] /=;  first by rewrite subrr normr0 //. 
      Unshelve. all: by end_near.
  Qed.

  Lemma nbhs0_scaler: forall (U : set E) (r : R),  (r != 0) -> nbhs 0 U -> nbhs 0 ( *:%R r @` U).
  Proof.
    move => U r r0 U0; move: (@scale_continuous ((r^-1,0)) U); rewrite /= scaler0 => /(_ U0).
    case=>//= [B] [B1 B2] BU. 
    near=> x => //=; exists (r^-1*:x); last by rewrite scalerA divrr ?scale1r ?unitfE //=.  
    apply: (BU (r^-1,x)); split => //=; last by near: x.
    by apply: nbhs_singleton.                        
    Unshelve. all: by end_near.
  Qed.

  
  Lemma nbhsT: forall (U : set E), forall (x : E), nbhs 0 U -> nbhs x (+%R x @`U).
  Proof.
  move => U x U0. 
  move: (@add_continuous (x,-x) U) => /=; rewrite subrr => /(_ U0) //=.
  case=> //= [B] [B1 B2] BU. near=> x0.
  exists (x0-x); last by rewrite //= addrCA subrr addr0.
  apply: (BU (x0,-x)); split => //=; last by apply: nbhs_singleton. 
  by near: x0; rewrite nearE.  
  Unshelve. all: by end_near.
  Qed.

  Lemma entourage_inv_subproof :
    forall A : set (E * E), entourage A -> entourage A^-1%classic.
  Proof.
  move => A [/=U [U0 Uxy]]; rewrite /entourage /=.
  exists (-%R@`U); split; first by apply: nbhs0N.
  move => xy; rewrite in_setE -opprB => [[yx] Uyx] => /oppr_inj H.
  by apply: Uxy; rewrite in_setE /= -H.
  Qed.


  Lemma entourage_split_ex_subproof :
        forall A : set (E * E),
        entourage A -> exists2 B : set (E * E), entourage B & B \; B `<=` A.
  Admitted.

Lemma nbhsE_subproof : nbhs = nbhs_ entourage.
  Admitted.

  HB.instance Definition _ := Nbhs_isUniform_mixin.Build E
    entourage_filter entourage_refl_subproof
    entourage_inv_subproof entourage_split_ex_subproof
    nbhsE_subproof.
HB.end.
  
Definition dual {R : ringType} (E : lmodType R) := {scalar E}. 
