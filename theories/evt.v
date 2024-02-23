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
    add_continuous : continuous (uncurry (@GRing.add E));
    scale_continuous : continuous (uncurry (@GRing.scale R E) : R^o * E -> E);
    locally_convex : exists B : set (set E), (forall b, b \in B -> convex b) /\ (basis B)
  }.

HB.structure Definition Evt (R : numDomainType) :=
  {E of Uniform_isEvt R E & Uniform E & GRing.Lmodule R E}. 

HB.factory Record TopologicalLmod_isEvt (R : numDomainType) E
      of Topological E & GRing.Lmodule R E := {
    add_continuous : continuous (uncurry (@GRing.add E));
    scale_continuous : continuous (uncurry (@GRing.scale R E) : R^o * E -> E);
    locally_convex : exists B : set (set E), (forall b, b \in B -> convex b) /\ (basis B)     
  }.
HB.builders Context R E of TopologicalLmod_isEvt R E.

  Definition entourage : set_system (E * E):=
  fun P=> exists U, nbhs 0 U-> forall xy : E*E, (xy.1 -xy.2) \in U -> xy \in P.

  Lemma entourage_filter : Filter entourage.
  Proof.
    split; first by exists [set: E] => _ xy _ //.
      move => P Q [/= U HP] [/=V HQ]; rewrite /entourage.
      exists (U`&`V); rewrite nbhsE //= => //= [[B HB]]; rewrite subsetI => [[BU BV]] xy.
      rewrite !in_setI => /andP[H1 H2]; apply/andP; split.
      apply: HP; last by [].
        rewrite nbhsE //=; exists B; last by [].
        by apply: HB.
     apply: HQ; last by [].
        rewrite nbhsE //=; exists B; last by [].
        by apply: HB. 
    move => P Q PQ; rewrite /entourage /= => [[U H]]; exists U.
    by move => N xy Hxy; rewrite in_setE; apply: PQ; rewrite -in_setE; apply:H.
  Qed.
  
  Lemma entourage_refl_subproof :
        forall A : set (E * E), entourage A -> [set xy | xy.1 = xy.2] `<=` A.
  Admitted.
  Locate "^-1".
  Lemma entourage_inv_subproof :
        forall A : set (E * E), entourage A -> entourage A^-1%classic.
  Admitted.
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
