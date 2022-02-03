(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice seq fintype order bigop.
From mathcomp Require Import ssralg ssrnum.
From mathcomp Require Import finmap.
Require Import boolp reals mathcomp_extra ereal classical_sets posnum topology.
Require Import sequences functions cardinality.

(******************************************************************************)
(*                     Summations over classical sets                         *)
(*                                                                            *)
(* This file provides a definition of sum over classical sets and a few       *)
(* lemmas in particular for the case of sums of non-negative terms.           *)
(*                                                                            *)
(* The contents of this file should not be considered as definitive because   *)
(* it supports on-going developments (such as the Lebesgue measure) and we    *)
(* anticipate revisions.                                                      *)
(*                                                                            *)
(* \csum_(i in I) f i == summation of non-negative extended real numbers over *)
(*            classical sets; I is a classical set and f is a function whose  *)
(*            codomain is included in the extended reals; it is 0 if I = set0 *)
(*            and sup(\sum_F a) where F is a finite set included in I o.w.    *)
(*                                                                            *)
(******************************************************************************)

Reserved Notation "\csum_ ( i 'in' P ) F"
  (at level 41, F at level 41, format "\csum_ ( i  'in'  P )  F").

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Local Open Scope classical_set_scope.
Local Open Scope ring_scope.
Local Open Scope ereal_scope.

Section set_of_fset_in_a_set.
Variable (T : choiceType).
Implicit Type S : set T.

Definition fsets S : set {fset T} := [set F | [set` F] `<=` S].

Lemma fsets_set0 S : fsets S fset0. Proof. by []. Qed.

Lemma fsets_self (F : {fset T}) : fsets [set x | x \in F] F.
Proof. by []. Qed.

Lemma fsetsP S (F : {fset T}) : [set` F] `<=` S <-> fsets S F.
Proof. by []. Qed.

Lemma fsets0 : fsets set0 = [set fset0].
Proof.
rewrite predeqE => A; split => [|->]; last exact: fsets_set0.
by rewrite /fsets /= subset0 => /eqP; rewrite set_fset_eq0 => /eqP.
Qed.

End set_of_fset_in_a_set.


Definition fsets_ord (P : pred nat) n := [fset i in 'I_n | P i]%fset.

Lemma fsets_ord_nat (P : pred nat) n :
  fsets P (@nat_of_ord _ @` fsets_ord P n)%fset.
Proof. by move=> /= i /imfsetP[/= a] /imfsetP[/= b Pb] ->{a} ->{i}. Qed.
Section csum.
Variables (R : realFieldType) (T : choiceType).
Implicit Types (S : set T) (a : T -> \bar R).

Definition csum S a :=
  ereal_sup [set \sum_(i <- F) a i | F in fsets S].

Local Notation "\csum_ ( i 'in' P ) F" := (csum P (fun i => F)).

Lemma csum_set0 a : \csum_(i in set0) a i = 0.
Proof.
rewrite /csum fsets0 [X in ereal_sup X](_ : _ = [set 0%E]) ?ereal_sup1//.
rewrite predeqE => x; split; first by move=> [_ /= ->]; rewrite big_seq_fset0.
by move=> -> /=; exists fset0 => //; rewrite big_seq_fset0.
Qed.

End csum.

Notation "\csum_ ( i 'in' P ) F" := (csum P (fun i => F)) : ring_scope.

Section csum_realType.
Variables (R : realType) (T : choiceType).
Implicit Types (a : T -> \bar R).

Lemma csum_ge0 (S : set T) a : (forall x, 0 <= a x) -> 0 <= \csum_(i in S) a i.
Proof.
move=> a0.
by apply: ereal_sup_ub; exists fset0; [exact: fsets_set0|rewrite big_nil].
Qed.

Lemma csum_fset (F : {fset T}) a : (forall i, i \in F -> 0 <= a i) ->
  \csum_(i in [set x | x \in F]) a i = \sum_(i <- F) a i.
Proof.
move=> f0; apply/eqP; rewrite eq_le; apply/andP; split; last first.
  by apply ereal_sup_ub; exists F => //; exact: fsets_self.
apply ub_ereal_sup => /= ? -[F' F'F <-]; apply/lee_sum_nneg_subfset.
  exact/fsetsP.
by move=> t; rewrite inE => /andP[_ /f0].
Qed.

End csum_realType.

Lemma csum_ge [R : realType] [T : choiceType] (I : set T) (a : T -> \bar R) x :
  (exists2 X : {fset T}, fsets I X & x <= \sum_(i <- X) a i) ->
  x <= \csum_(i in I) a i.
Proof. by move=> [X IX /le_trans->//]; apply: ereal_sup_ub => /=; exists X. Qed.

Lemma csum0 [R : realFieldType] [I : choiceType] (D : set I) (a : I -> \bar R) :
  (forall i, D i -> a i = 0) -> \csum_(i in D) a i = 0.
Proof.
move=> a0; rewrite /csum (_ : [set _ | _ in _] = [set 0]) ?ereal_sup1//.
apply/seteqP; split=> x //= => [[X XI] <-|->].
  by rewrite big_seq_cond big1// => i /andP[Xi _]; rewrite a0//; apply: XI.
by exists fset0; rewrite ?big_seq_fset0.
Qed.

Lemma le_csum [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> a i <= b i) ->
  \csum_(i in I) a i <= \csum_(i in I) b i.
Proof.
move=> le_ab; rewrite ub_ereal_sup => //= _ [X XI] <-; rewrite csum_ge//.
exists X => //; rewrite big_seq_cond [x in _ <= x]big_seq_cond lee_sum => // i.
by rewrite andbT => /XI /le_ab.
Qed.

Lemma eq_csum [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> a i = b i) ->
  \csum_(i in I) a i = \csum_(i in I) b i.
Proof. by move=> e; apply/eqP; rewrite eq_le !le_csum// => i Ii; rewrite e. Qed.

Lemma csum_add [R : realType] [T : choiceType] (I : set T) (a b : T -> \bar R) :
  (forall i, I i -> 0 <= a i) -> (forall i, I i -> 0 <= b i) ->
  \csum_(i in I) (a i + b i) = \csum_(i in I) a i + \csum_(i in I) b i.
Proof.
move=> ag0 bg0; apply/eqP; rewrite eq_le; apply/andP; split.
  rewrite ub_ereal_sup//= => x [X XI] <-; rewrite big_split/=.
  by rewrite lee_add// ereal_sup_ub//=; exists X.
wlog : a b ag0 bg0 / \csum_(i in I) a i \isn't a fin_num => [saoo|]; last first.
  move=> /fin_numPn[->|/[dup] aoo ->]; first by rewrite /adde/= lee_ninfty.
  rewrite (@le_trans _ _ +oo)//; first by rewrite /adde/=; case: csum.
  rewrite lee_pinfty_eq; apply/eqP/eq_infty => y; rewrite csum_ge//.
  have : y%:E < \csum_(i in I) a i by rewrite aoo// lte_pinfty.
  move=> /ereal_sup_gt[_ [X XI] <-] /ltW yle; exists X => //=.
  rewrite (le_trans yle)// big_split lee_addl// big_seq_cond sume_ge0 => // i.
  by rewrite andbT => /XI; apply: bg0.
  case: (boolP (\csum_(i in I) a i \is a fin_num)) => sa; last exact: saoo.
case: (boolP (\csum_(i in I) b i \is a fin_num)) => sb; last first.
  by rewrite addeC (eq_csum (fun _ _ => addeC _ _)) saoo.
rewrite -lee_subr_addr// ub_ereal_sup//= => _ [X XI] <-.
have saX : \sum_(i <- X) a i \is a fin_num.
  apply: contraTT sa => /fin_numPn[] sa.
    suff : \sum_(i <- X) a i >= 0 by rewrite sa.
    by rewrite big_seq_cond sume_ge0 => // i; rewrite ?andbT => /XI/ag0.
  apply/fin_numPn; right; apply/eqP; rewrite -lee_pinfty_eq csum_ge//.
  by exists X; rewrite // sa.
rewrite lee_subr_addr// addeC -lee_subr_addr// ub_ereal_sup//= => _ [Y YI] <-.
rewrite lee_subr_addr// addeC csum_ge//; exists (X `|` Y)%fset.
  by move=> i/=; rewrite inE => /orP[/XI|/YI].
rewrite big_split/= lee_add//=.
  rewrite lee_sum_nneg_subfset//=; first exact/fsubsetP/fsubsetUl.
  by move=> x; rewrite !inE/= => /andP[/negPf->]/= => /YI/ag0.
rewrite lee_sum_nneg_subfset//=; first exact/fsubsetP/fsubsetUr.
by move=> x; rewrite !inE/= => /andP[/negPf->]/orP[]// => /XI/bg0.
Qed.

Lemma csum_mkcond [R : realType] [T : choiceType] (I : set T) (a : T -> \bar R) :
  \csum_(i in I) a i = \csum_(i in [set: T]) if i \in I then a i else 0.
Proof.
apply/eqP; rewrite eq_le !ub_ereal_sup//= => _ [X XI] <-; rewrite -?big_mkcond//=.
  rewrite big_fset_condE/=; set Y := [fset _ | _ in X & _]%fset.
  rewrite ereal_sup_ub//; exists Y => //= i /=.
  by rewrite 2!inE/= => /andP[_]; rewrite inE.
rewrite ereal_sup_ub//; exists X => //; rewrite -big_mkcond/=.
rewrite big_seq_cond [RHS]big_seq_cond; apply: eq_bigl => i.
by case: (boolP (i \in X)) => //= /XI Ii; apply/mem_set.
Qed.

Lemma csum_sum [R : realType] [T1 T2 : choiceType]
    (I : set T1) (r : seq T2) (P : pred T2) (a : T1 -> T2 -> \bar R) :
  (forall i j, I i -> P j -> 0 <= a i j) ->
  \csum_(i in I) \sum_(j <- r | P j) a i j =
  \sum_(j <- r | P j) \csum_(i in I) a i j.
Proof.
move=> a_ge0; elim: r => [|j r IHr]; rewrite ?(big_nil, big_cons)// -?IHr.
  by rewrite csum0// => i; rewrite big_nil.
case: (boolP (P j)) => Pj; last first.
  by apply: eq_csum => i Ii; rewrite big_cons (negPf Pj).
have aj_ge0 i : I i -> a i j >= 0 by move=> ?; apply: a_ge0.
rewrite -csum_add//; last by move=> i Ii; apply: sume_ge0 => *; apply: a_ge0.
by apply: eq_csum => i Ii; rewrite big_cons Pj.
Qed.

Lemma csum_csum [R : realType] [T1 T2 : choiceType]
    (I : set T1) (J : T1 -> set T2) (a : T1 -> T2 -> \bar R) :
  (forall i j, 0 <= a i j) ->
  \csum_(i in I) \csum_(j in J i) a i j = \csum_(k in I `*`` J) a k.1 k.2.
Proof.
move=> a_ge0; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: ub_ereal_sup => /= _ [X IX] <-.
  under eq_bigr do rewrite csum_mkcond.
  rewrite -csum_sum; last by move=> i j _ _; case: ifP.
  under eq_csum do rewrite -big_mkcond/=.
  apply: ub_ereal_sup => /= _ [Y _ <-]; apply: ereal_sup_ub => /=.
  exists [fset z | z in X `*` Y & z.2 \in J z.1]%fset => //=.
    move=> z/=; rewrite !inE/= -andbA => /and3P[Xz1 Yz2 zJ].
    by split; [exact: IX | rewrite inE in zJ].
  rewrite (exchange_big_dep xpredT)//= pair_big_dep_cond/=.
  apply: eq_fbigl => -[/= k1 k2]; rewrite !inE -andbA.
  apply/idP/imfset2P => /= [/and3P[kX kY kJ]|].
    exists k1; rewrite ?(andbT, inE)//=.
    by exists k2; rewrite ?(andbT, inE)//= kY kJ.
  by move=> [{}k1 + [{}k2 + [-> ->]]]; rewrite !inE andbT => -> /andP[-> ->].
apply: ub_ereal_sup => _ /= [X/= XIJ] <-; apply: csum_ge.
pose X1 := [fset x.1 | x in X]%fset.
pose X2 := [fset x.2 | x in X]%fset.
exists X1; first by move=> x/= /imfsetP[z /= zX ->]; have [] := XIJ z.
apply: (@le_trans _ _ (\sum_(i <- X1) \sum_(j <- X2 | j \in J i) a i j)).
  rewrite pair_big_dep_cond//=; set Y := Imfset.imfset2 _ _ _ _.
  rewrite [X in _ <= X](big_fsetID _ (mem X))/=.
  rewrite (_ : [fset x | x in Y & x \in X] = Y `&` X)%fset; last first.
     by apply/fsetP => x; rewrite 2!inE.
  rewrite (fsetIidPr _); first by rewrite lee_addl// sume_ge0.
  apply/fsubsetP => -[i j] Xij; apply/imfset2P.
    exists i => //=; rewrite ?inE ?andbT//=.
    by apply/imfsetP; exists (i, j).
  exists j => //; rewrite !inE/=; have /XIJ[/= _ Jij] := Xij.
  by apply/andP; split; rewrite ?inE//; apply/imfsetP; exists (i, j).
rewrite big_mkcond [X in _ <= X]big_mkcond.
apply: lee_sum => i Xi; rewrite ereal_sup_ub => //=.
exists [fset j in X2 | j \in J i]%fset; last by rewrite -big_fset_condE.
by move=> j/=; rewrite !inE => /andP[_]; rewrite inE.
Qed.

Lemma ereal_pseries_csum (R : realType) (a : nat -> \bar R) (P : pred nat) :
  (forall n, P n -> 0 <= a n) ->
  \sum_(i <oo | P i) a i = \csum_(i in [set x | P x]) a i.
Proof.
move=> a0; apply/eqP; rewrite eq_le; apply/andP; split.
  apply: (ereal_lim_le (is_cvg_ereal_nneg_series_cond a0)).
  near=> n; apply: ereal_sup_ub => /=.
  exists [fset val i | i in 'I_n & P i]%fset.
    by move=> /= k /imfsetP[/= i]; rewrite inE => + ->.
  rewrite -[in RHS]big_filter; apply: perm_big.
  rewrite uniq_perm// ?filter_uniq /index_iota/= ?iota_uniq ?fset_uniq// subn0.
  set s := [seq x <- iota 0 n | P x].
  move=> i; apply/imfsetP/(nthP 0%N) => /= [[{}i + ->]|[k ks <-]].
    rewrite inE => Pi; have si : val i \in s.
      by rewrite mem_filter ?Pi ?mem_iota ?add0n ?leq0n//=.
    by exists (index (val i) s); rewrite ?index_mem ?nth_index.
  have skn : (nth 0 s k < n)%N.
    rewrite (@all_nthP _ (fun i => i < n)%N _ _ _)//=.
    by apply/allP => j; rewrite mem_filter mem_iota add0n => /and3P[].
  by exists (Ordinal skn); rewrite //= inE/= (all_nthP _ _)// ?filter_all.
apply: ub_ereal_sup => _ [/= F /fsetsP PF <-]; pose n := (\max_(k <- F) k).+1.
rewrite (le_trans _ (ereal_nneg_series_lim_ge n _))//.
rewrite [X in _ <= X](bigID (mem F))/=.
suff -> : \sum_(0 <= i < n | P i && (i \in F)) a i = \sum_(i <- F) a i.
  by rewrite lee_addl ?sume_ge0// => i /andP[/a0].
rewrite -big_filter; apply: perm_big.
rewrite uniq_perm ?fset_uniq ?filter_uniq ?index_iota ?iota_uniq//.
move=> i; rewrite mem_filter -andbA andbCA; case: (boolP (i \in F)) => //= Fi.
apply/andP; split; first exact: PF.
rewrite mem_iota leq0n add0n subn0 /n/=.
by rewrite big_seq_fsetE/= -[i]/(val [` Fi ]%fset) ltnS leq_bigmax.
Unshelve. all: by end_near. Qed.

Lemma sum_fset_nat_ub (R : realDomainType) (f : (\bar R)^nat) (F : {fset nat})
    (P : pred nat) n :
  (forall i, P i -> 0%E <= f i) ->
  (F `<=` @nat_of_ord _ @` fsets_ord xpredT n)%fset ->
  \sum_(i <- F | P i) f i <= \sum_(i < n | P i) f i.
Proof.
move=> f0 /fsubsetP F_fsets_ord; apply (@le_trans _ _
    (\sum_(i <- @nat_of_ord _ @` [fset j : 'I_n | P j]) f i)%fset); last first.
  rewrite big_imfset /=; last by move=> i j _ _; apply: ord_inj.
  by rewrite big_fset /= big_enum_cond.
apply (@le_trans _ _
    (\sum_(i <- [fset nat_of_ord j | j in 'I_n]%fset | P i) f i)); last first.
  rewrite big_imfset /=; last by move=> i j _ _; apply/ord_inj.
  rewrite big_fset big_enum_cond /= big_mkcond /=.
  rewrite big_imfset /=; last by move=> i j _ _; apply/ord_inj.
  by rewrite -big_mkcond /= big_enum_cond.
apply/(lee_sum_nneg_subfset _ (fun m _ => f0 m)) => t /F_fsets_ord.
by move=> /imfsetP[/= j _ ->{t}]; apply/imfsetP; exists j.
Qed.

Lemma lee_sum_lim (R : realType) (f : (\bar R)^nat) (F : {fset nat})
    (P : pred nat) :
  (forall i, P i -> 0%E <= f i) ->
  \sum_(i <- F | P i) f i <= \sum_(i <oo | P i) f i.
Proof.
move=> f0; have [->|F0] := eqVneq F fset0.
  by rewrite big_mkcond big_seq_fset0 ereal_nneg_series_lim_ge0.
have [n FnS] : exists n, (F `<=` @nat_of_ord _ @` fsets_ord xpredT n)%fset.
  move/(fset_nat_maximum id) : F0 => [i [iF Fi]]; exists i.+1.
  apply/fsubsetP => j jF; apply/imfsetP => /=.
  by move/Fi : jF; rewrite -ltnS => jF; exists (Ordinal jF) => //; rewrite inE.
apply/(le_trans _ (ereal_nneg_series_lim_ge n f0)).
by rewrite big_mkord sum_fset_nat_ub.
Qed.

Lemma reindex_csum (R : realType) (T T' : choiceType)
    (P : set T) (Q : set T') (e : T -> T') (a : T' -> \bar R) :
    set_bij P Q e ->
    (forall i, P i -> 0 <= a (e i)) ->
  \csum_(j in Q) a j = \csum_(i in P) a (e i).
Proof.
elim/choicePpointed: T => T in e P *.
  rewrite !emptyE => /Pbij[{}e ->] _.
  by rewrite -[in LHS](image_eq e) image_set0 !csum_set0.
elim/choicePpointed: T' => T' in a e Q *; first by have := no (e point).
move=> /(@pPbij _ _ _)[{}e ->] a_ge0.
gen have le_csum : T T' a P Q e a_ge0 /
    \csum_(j in Q) a j <= \csum_(i in P) a (e i); last first.
  apply/eqP; rewrite eq_le le_csum//=.
  rewrite [X in _ <= X](_ : _ = \csum_(j in Q) a (e (e^-1%FUN j))); last first.
    by apply: eq_csum => i Qi; rewrite invK ?inE.
  by rewrite le_csum => //= i Qi; rewrite a_ge0//; apply: funS.
rewrite ub_ereal_sup => //= _ [X XQ <-]; rewrite ereal_sup_ub => //=.
exists (e^-1 @` X)%fset; first by move=> _ /imfsetP[t' /= /XQ Qt' ->]; apply: funS.
rewrite big_imfset => //=; last first.
  by move=> x y /XQ Qx /XQ Qy /(congr1 e); rewrite !invK ?inE.
by apply: eq_big_seq => i /XQ Qi; rewrite invK ?inE.
Qed.
Arguments reindex_csum {R T T'} P Q e a.

Lemma csum_pred_image (R : realType) (T : pointedType) (a : T -> \bar R)
    (e : nat -> T) (P : pred nat) :
    (forall n, P n -> 0 <= a (e n)) ->
    set_inj P e ->
  \csum_(i in e @` P) a i = \sum_(i <oo | P i) a (e i).
Proof.
move=> ae_ge0 einj; rewrite ereal_pseries_csum//; apply: reindex_csum => //=.
exact: inj_bij.
Qed.
Arguments csum_pred_image {R T} a e P.

Lemma csum_set_image  [R : realType] [T : pointedType] [a : T -> \bar R]
    [e : nat -> T] [P : set nat] :
    (forall n : nat, P n -> 0 <= a (e n)) ->
  set_inj P e ->
  \csum_(i in [set e x | x in P]) a i = \sum_(i <oo | i \in P) a (e i).
Proof.
move=> a_ge0 e_injg; rewrite -csum_pred_image//.
- by congr csum; congr image; apply/predeqP; split; rewrite ?inE.
- by move=> n; rewrite inE; apply: a_ge0.
- by move=> i j; rewrite inE => Pi; rewrite inE; apply: e_injg.
Qed.
Arguments csum_set_image {R T} a e P.

Section csum_bigcup.
Variables (R : realType) (T : pointedType) (K : set nat).
Implicit Types (J : nat -> set T) (a : T -> \bar R).

Lemma csum_bigcupT J a : trivIset setT J -> (forall x, 0 <= a x) ->
  \csum_(i in \bigcup_(k in K) (J k)) a i =
  \csum_(i in K) \csum_(j in J i) a j.
Proof.
move=> tJ a0; rewrite csum_csum//; apply: reindex_csum => //; split.
- by move=> [/= i j] [Ki Jij]; exists i.
- move=> [/= i1 j1] [/= i2 j2]; rewrite ?inE/=.
  move=> [K1 J1] [K2 J2] j12; congr (_, _) => //.
  by apply: (@tJ i1 i2) => //; exists j1; split=> //; rewrite j12.
- by move=> j [i Ki Jij]/=; exists (i, j).
Qed.

Lemma csum_bigcup J a : trivIset [set i | a @` J i != [set 0]] J ->
    (forall x : T, (\bigcup_(k in K) J k) x -> 0 <= a x) ->
  \csum_(i in \bigcup_(k in K) J k) a i = \csum_(i in K) \csum_(j in J i) a j.
Proof.
move=> Jtriv a_ge0.
pose J' i := if a @` J i == [set 0] then set0 else J i.
pose a' x := if x \in \bigcup_(k in K) J k then a x else 0.
have a'E k x : K k -> J k x -> a' x = a x.
  move=> Kk Jkx; rewrite /a'; case: ifPn; rewrite ?(inE, notin_set)//=.
  by case; exists k.
have a'_ge0 x : a' x >= 0 by rewrite /a'; case: ifPn; rewrite // ?inE => /a_ge0.
transitivity (\csum_(i in \bigcup_(k in K) J' k) a' i).
  rewrite csum_mkcond [RHS]csum_mkcond /a'; apply: eq_csum => x _.
  do 2!case: ifPn; rewrite ?(inE, notin_set)//= => J'x Jx.
  apply: contra_not_eq J'x => Nax.
  move: Jx => [k kK Jkx]; exists k=> //; rewrite /J'/=; case: ifPn=> //=.
  move=> /eqP/(congr1 (@^~ (a x)))/=; rewrite propeqE => -[+ _].
  by apply: contra_neq_not Nax; apply; exists x.
rewrite csum_bigcupT//; last first.
  move=> i j _ _ [x []]; rewrite /J'/=.
  case: eqVneq => //= Ai0 Jix; case: eqVneq => //= Aj0 Jjx.
  by have := Jtriv i j Ai0 Aj0; apply; exists x.
apply: eq_csum => i Ki.
rewrite csum_mkcond [RHS]csum_mkcond; apply: eq_csum => x _.
do 2!case: ifPn; rewrite ?(inE, notin_set)//=.
- by move=> /a'E->//.
- by rewrite /J'; case: ifPn => //.
move=> Jix; rewrite /J'; case: ifPn=> //=.
by move=> /eqP/(congr1 (@^~ (a x)))/=; rewrite propeqE => -[->]//; exists x.
Qed.

End csum_bigcup.

Arguments csum_bigcupT {R T K} J a.
Arguments csum_bigcup {R T K} J a.
