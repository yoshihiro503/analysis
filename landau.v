(* mathcomp analysis (c) 2017 Inria and AIST. License: CeCILL-C.              *)
Require Import Reals.
From Coq Require Import ssreflect ssrfun ssrbool.
From mathcomp Require Import ssrnat eqtype choice fintype bigop ssralg ssrnum.
Require Import boolp reals Rstruct Rbar.
Require Import classical_sets posnum topology hierarchy.

(******************************************************************************)
(*              BACHMANN-LANDAU NOTATIONS : BIG AND LITTLE O                  *)
(******************************************************************************)
(******************************************************************************)
(* F is a filter, K is an absRingType and V W X Y Z are normed spaces over K  *)
(* alternatively, K can be equal to the reals R (from the standard library    *)
(* for now)                                                                   *)
(* This library is very asymmetric, in multiple respects:                     *)
(* - most rewrite rules can only be rewritten from left to right.             *)
(*   e.g. an equation 'o_F f = 'O_G g can be used only from LEFT TO RIGHT     *)
(* - conversely most small 'o_F f in your goal are very specific,             *)
(*   only 'a_F f is mutable                                                   *)
(*                                                                            *)
(* - most notations are either parse only or print only.                      *)
(*   Indeed all the 'O_F notations contain a function which is NOT displayed. *)
(*   This might be confusing as sometimes you might get 'O_F g = 'O_F g       *)
(*   and not be able to solve by reflexivity.                                 *)
(*   - In order to have a look at the hidden function, rewrite showo.         *)
(*   - Do not use showo during a normal proof.                                *)
(*   - All theorems should be stated so that when an impossible reflexivity   *)
(*     is encountered, it is of the form 'O_F g = 'O_F g so that you          *)
(*     know you should use eqOE in order to generalize your 'O_F g            *)
(*     to an arbitrary 'O_F g                                                 *)
(*                                                                            *)
(* To prove that f is a bigO of g near F, you should go back to filter        *)
(* reasoning only as a last resort. To do so, use the view eqOP. Similarly,   *)
(* you can use eqaddOP to prove that f is equal to g plus a bigO of e near F  *)
(* using filter reasoning.                                                    *)
(*                                                                            *)
(* Parsable notations:                                                        *)
(*    [bigO of f] == recovers the canonical structure of big-o of f           *)
(*                   expands to itself                                        *)
(*       f =O_F h == f is a bigO of h near F,                                 *)
(*                   this is the preferred way for statements.                *)
(*                   expands to the equation (f = 'O_F h)                     *)
(*                   rewrite from LEFT to RIGHT only                          *)
(*   f = g +O_F h == f is equal to g plus a bigO near F,                      *)
(*                   this is the preferred way for statements.                *)
(*                   expands to the equation (f = g + 'O_F h)                 *)
(*                   rewrite from LEFT to RIGHT only                          *)
(*                   /!\ When you have to prove                               *)
(*                   (f =O_F h) or (f = g +O_F h).                            *)
(*                   you must (apply: eqOE) as soon as possible in a proof    *)
(*                   in order to turn it into 'a_O_F f with a shelved content *)
(*                   /!\ under rare circumstances, a hint may do that for you *)
(*   [O_F h of f] == returns a function with a bigO canonical structure       *)
(*                   provably equal to f if f is indeed a bigO of h           *)
(*                   provably equal to 0 otherwise                            *)
(*                   expands to ('O_F h)                                      *)
(*           'O_F == pattern to match a bigO with a specific F                *)
(*             'O == pattern to match a bigO with a generic F                 *)
(*                                                                            *)
(* Printing only notations:                                                   *)
(*        {O_F f} == the type of functions that are a bigO of f near F        *)
(*       'a_O_F f == an existential bigO, must come from (apply: eqOE)        *)
(*         'O_F f == a generic bigO, with a function you should not rely on,  *)
(*                   but there is no way you can use eqOE on it.              *)
(*                                                                            *)
(* The former works exactly the same by with littleo instead of bigO.         *)
(*                                                                            *)
(* Asymptotic equivalence:                                                    *)
(*       f ~_ F g == function f is asymptotically equivalent to               *)
(*                   function g for filter F, i.e., f = g +o_ F g             *)
(*      f ~~_ F g == f == g +o_ F g (i.e., as a boolean relation)             *)
(* --> asymptotic equivalence proved to be an equivalence relation            *)
(*                                                                            *)
(* Big-Omega and big-Theta notations on the model of bigO and littleo:        *)
(* {Omega_F f}      == the type of functions that are a big Omega of f near F *)
(* [bigOmega of f]  == recovers the canonical structure of big-Omega of f     *)
(* [Omega_F e of f] == returns a function with a bigOmega canonical structure *)
(*                     provably equal to f if f is indeed a bigOmega of e     *)
(*                     or e otherwise                                         *)
(* f \is 'Omega_F(e) == f : T -> V is a bigOmega of e : T -> W near F         *)
(* f =Omega_F h      == f : T -> V is a bigOmega of h : T -> V near F         *)
(* --> lemmas: relation with big-O, transitivity, product of functions, etc.  *)
(*                                                                            *)
(* Similar notations available for big-Theta.                                 *)
(* --> lemmas: relations with big-O and big-Omega, reflexivity, symmetry,     *)
(*     transitivity, product of functions, etc.                               *)
(*                                                                            *)
(******************************************************************************)

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
Import GRing.Theory Num.Def Num.Theory.

Reserved Notation "{o_ F f }" (at level 0, F at level 0, format "{o_ F  f }").
Reserved Notation "[littleo 'of' f 'for' fT ]" (at level 0, f at level 0,
  format "[littleo  'of'  f  'for'  fT ]").
Reserved Notation "[littleo 'of' f ]" (at level 0, f at level 0,
  format "[littleo  'of'  f ]").

Reserved Notation "'o_ x" (at level 200, x at level 0, only parsing).
Reserved Notation "'o" (at level 200, only parsing).
(* Parsing *)
Reserved Notation "[o_ x e 'of' f ]" (at level 0, x, e at level 0, only parsing).
(*Printing*)
Reserved Notation "[o '_' x e 'of' f ]"
  (at level 0, x, e at level 0, format "[o '_' x  e  'of'  f ]").
(* These notations are printing only in order to display 'o
   without looking at the contents, use showo to display *)
Reserved Notation "''o_' x e "
  (at level 0, x, e at level 0, format "''o_' x  e ").
Reserved Notation "''a_o_' x e "
  (at level 0, x, e at level 0, format "''a_o_' x  e ").
Reserved Notation "''o' '_' x"
  (at level 0, x at level 0, format "''o' '_' x").

Reserved Notation "f = g '+o_' F h"
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+o_' F  h").
Reserved Notation "f '=o_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=o_' F  h").
Reserved Notation "f == g '+o_' F h"
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  ==  g  '+o_' F  h").
Reserved Notation "f '==o_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '==o_' F  h").

Reserved Notation "[o_( x \near F ) ex 'of' fx ]"
  (at level 0, x, ex at level 0, only parsing).
(*Printing*)
Reserved Notation "[o '_(' x \near F ')' ex 'of' fx ]"
  (at level 0, x, ex at level 0,
   format "[o '_(' x  \near  F ')'  ex  'of'  fx ]").
(* These notations are printing only in order to display 'o
   without looking at the contents, use showo to display *)
Reserved Notation "''o_(' x \near F ')' ex"
  (at level 0, x, ex at level 0, format "''o_(' x  \near  F ')'  ex").
Reserved Notation "''a_o_(' x \near F ')' ex"
  (at level 0, x, ex at level 0, format "''a_o_(' x  \near  F ')'  ex").
Reserved Notation "''o' '_(' x \near F ')' ex"
  (at level 0, x, ex at level 0, format "''o' '_(' x  \near  F ')'  ex").

Reserved Notation "fx = gx '+o_(' x \near F ')' hx"
  (at level 70, no associativity,
   gx at next level, F at level 0, hx at next level,
   format "fx  =  gx  '+o_(' x  \near  F ')'  hx").
Reserved Notation "fx '=o_(' x \near F ')' hx"
  (at level 70, no associativity,
   F at level 0, hx at next level,
   format "fx  '=o_(' x  \near  F ')'  hx").
Reserved Notation "fx == gx '+o_(' x \near F ')' hx"
  (at level 70, no associativity,
   gx at next level, F at level 0, hx at next level,
   format "fx  ==  gx  '+o_(' x  \near  F ')'  hx").
Reserved Notation "fx '==o_(' x \near F ')' hx"
  (at level 70, no associativity,
   F at level 0, hx at next level,
   format "fx  '==o_(' x  \near  F ')'  hx").

Reserved Notation "{O_ F f }" (at level 0, F at level 0, format "{O_ F  f }").
Reserved Notation "[bigO 'of' f 'for' fT ]" (at level 0, f at level 0,
  format "[bigO  'of'  f  'for'  fT ]").
Reserved Notation "[bigO 'of' f ]" (at level 0, f at level 0,
  format "[bigO  'of'  f ]").

Reserved Notation "'O_ x" (at level 200, x at level 0, only parsing).
Reserved Notation "'O" (at level 200, only parsing).
(* Parsing *)
Reserved Notation "[O_ x e 'of' f ]" (at level 0, x, e at level 0, only parsing).
(*Printing*)
Reserved Notation "[O '_' x e 'of' f ]"
  (at level 0, x, e at level 0, format "[O '_' x  e  'of'  f ]").
(* These notations are printing only in order to display 'O
   without looking at the contents, use showo to display *)
Reserved Notation "''O_' x e "
  (at level 0, x, e at level 0, format "''O_' x  e ").
Reserved Notation "''a_O_' x e "
  (at level 0, x, e at level 0, format "''a_O_' x  e ").
Reserved Notation "''O' '_' x"
  (at level 0, x at level 0, format "''O' '_' x").

Reserved Notation "f = g '+O_' F h"
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  =  g  '+O_' F  h").
Reserved Notation "f '=O_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=O_' F  h").
Reserved Notation "f == g '+O_' F h"
  (at level 70, no associativity,
   g at next level, F at level 0, h at next level,
   format "f  ==  g  '+O_' F  h").
Reserved Notation "f '==O_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '==O_' F  h").

Reserved Notation "[O_( x \near F ) ex 'of' fx ]"
  (at level 0, x, ex at level 0, only parsing).
(*Printing*)
Reserved Notation "[O '_(' x \near F ')' ex 'of' fx ]"
  (at level 0, x, ex at level 0,
   format "[O '_(' x  \near  F ')'  ex  'of'  fx ]").
(* These notations are printing only in order to display 'o
   without looking at the contents, use showo to display *)
Reserved Notation "''O_(' x \near F ')' ex"
  (at level 0, x, ex at level 0, format "''O_(' x  \near  F ')'  ex").
Reserved Notation "''a_O_(' x \near F ')' ex"
  (at level 0, x, ex at level 0, format "''a_O_(' x  \near  F ')'  ex").
Reserved Notation "''O' '_(' x \near F ')' ex"
  (at level 0, x, ex at level 0, format "''O' '_(' x  \near  F ')'  ex").

Reserved Notation "fx = gx '+O_(' x \near F ')' hx"
  (at level 70, no associativity,
   gx at next level, F at level 0, hx at next level,
   format "fx  =  gx  '+O_(' x  \near  F ')'  hx").
Reserved Notation "fx '=O_(' x \near F ')' hx"
  (at level 70, no associativity,
   F at level 0, hx at next level,
   format "fx  '=O_(' x  \near  F ')'  hx").
Reserved Notation "fx == gx '+O_(' x \near F ')' hx"
  (at level 70, no associativity,
   gx at next level, F at level 0, hx at next level,
   format "fx  ==  gx  '+O_(' x  \near  F ')'  hx").
Reserved Notation "fx '==O_(' x \near F ')' hx"
  (at level 70, no associativity,
   F at level 0, hx at next level,
   format "fx  '==O_(' x  \near  F ')'  hx").

Reserved Notation "f '~_' F g"
  (at level 70, F at level 0, g at next level, format "f  '~_' F  g").
Reserved Notation "f '~~_' F g"
  (at level 70, F at level 0, g at next level, format "f  '~~_' F  g").

Reserved Notation "{Omega_ F f }"
  (at level 0, F at level 0, format "{Omega_ F  f }").
Reserved Notation "[bigOmega 'of' f 'for' fT ]"
  (at level 0, f at level 0, format "[bigOmega  'of'  f  'for'  fT ]").
Reserved Notation "[bigOmega 'of' f ]"
  (at level 0, f at level 0, format "[bigOmega  'of'  f ]").
Reserved Notation "[Omega_ x e 'of' f ]"
  (at level 0, x, e at level 0, only parsing).
(* Printing *)
Reserved Notation "[Omega '_' x e 'of' f ]"
  (at level 0, x, e at level 0, format "[Omega '_' x  e  'of'  f ]").
Reserved Notation "'Omega_ F g"
  (at level 0, F at level 0, format "''Omega_' F g").
Reserved Notation "f '=Omega_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=Omega_' F  h").

Reserved Notation "{Theta_ F g }"
  (at level 0, F at level 0, format "{Theta_  F  g }").
Reserved Notation "[bigTheta 'of' f 'for' fT ]"
  (at level 0, f at level 0, format "[bigTheta  'of'  f  'for'  fT ]").
Reserved Notation "[bigTheta 'of' f ]"
  (at level 0, f at level 0, format "[bigTheta  'of'  f ]").
Reserved Notation "[Theta_ x e 'of' f ]"
  (at level 0, x, e at level 0, only parsing).
(*Printing*)
Reserved Notation "[Theta '_' x e 'of' f ]"
  (at level 0, x, e at level 0, format "[Theta '_' x  e  'of'  f ]").
Reserved Notation "'Theta_ F g"
  (at level 0, F at level 0, format "''Theta_' F g").
Reserved Notation "f '=Theta_' F h"
  (at level 70, no associativity,
   F at level 0, h at next level,
   format "f  '=Theta_' F  h").

Delimit Scope R_scope with coqR.
Delimit Scope real_scope with real.
Local Close Scope R_scope.
Local Open Scope ring_scope.
Local Open Scope real_scope.
Local Open Scope classical_set_scope.

Section function_space.

Definition cst {T T' : Type} (x : T') : T -> T' := fun=> x.

Program Definition fct_zmodMixin (T : Type) (M : zmodType) :=
  @ZmodMixin (T -> M) \0 (fun f x => - f x) (fun f g => f \+ g) _ _ _ _.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite addrA. Qed.
Next Obligation. by move=> f g; rewrite funeqE=> x /=; rewrite addrC. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite add0r. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite addNr. Qed.
Canonical fct_zmodType T (M : zmodType) := ZmodType (T -> M) (fct_zmodMixin T M).

Program Definition fct_ringMixin (T : pointedType) (M : ringType) :=
  @RingMixin [zmodType of T -> M] (cst 1) (fun f g x => f x * g x)
             _ _ _ _ _ _.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrA. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite mul1r. Qed.
Next Obligation. by move=> f; rewrite funeqE=> x /=; rewrite mulr1. Qed.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrDl. Qed.
Next Obligation. by move=> f g h; rewrite funeqE=> x /=; rewrite mulrDr. Qed.
Next Obligation.
by apply/eqP; rewrite funeqE => /(_ point) /eqP; rewrite oner_eq0.
Qed.
Canonical fct_ringType (T : pointedType) (M : ringType) :=
  RingType (T -> M) (fct_ringMixin T M).

Program Canonical fct_comRingType (T : pointedType) (M : comRingType) :=
  ComRingType (T -> M) _.
Next Obligation. by move=> f g; rewrite funeqE => x; rewrite mulrC. Qed.

Program Definition fct_lmodMixin (U : Type) (R : ringType) (V : lmodType R)
  := @LmodMixin R [zmodType of U -> V] (fun k f => k \*: f) _ _ _ _.
Next Obligation. rewrite funeqE => x; exact: scalerA. Qed.
Next Obligation. by move=> f; rewrite funeqE => x /=; rewrite scale1r. Qed.
Next Obligation. by move=> f g h; rewrite funeqE => x /=; rewrite scalerDr. Qed.
Next Obligation. by move=> f g; rewrite funeqE => x /=; rewrite scalerDl. Qed.
Canonical fct_lmodType U (R : ringType) (V : lmodType R) :=
  LmodType _ (U -> V) (fct_lmodMixin U V).

Lemma fct_sumE (T : Type) (M : zmodType) n (f : 'I_n -> T -> M) (x : T) :
  (\sum_(i < n) f i) x = \sum_(i < n) f i x.
Proof.
elim: n f => [|n H] f;
  by rewrite !(big_ord0,big_ord_recr) //= -[LHS]/(_ x + _ x) H.
Qed.

End function_space.

Section Linear1.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V).
Canonical linear_eqType := EqType {linear U -> V | s} gen_eqMixin.
Canonical linear_choiceType := ChoiceType {linear U -> V | s} gen_choiceMixin.
End Linear1.
Section Linear2.
Context (R : ringType) (U : lmodType R) (V : zmodType) (s : R -> V -> V)
        (s_law : GRing.Scale.law s).
Canonical linear_pointedType := PointedType {linear U -> V | GRing.Scale.op s_law}
                                            (@GRing.null_fun_linear R U V s s_law).
End Linear2.

(* tags for littleo and bigO notations *)
Definition the_tag : unit := tt.
Definition gen_tag : unit := tt.
Definition a_tag : unit := tt.
Lemma showo : (gen_tag = tt) * (the_tag = tt) * (a_tag = tt). Proof. by []. Qed.

(* Tentative to handle small o and big O notations *)
Section Domination.

Context {K : absRingType} {T : Type} {V W : normedModType K}.

Let littleo_def (F : set (set T)) (f : T -> V) (g : T -> W) :=
  forall eps : R, 0 < eps -> \forall x \near F, `|[f x]| <= eps * `|[g x]|.

Structure littleo_type (F : set (set T)) (g : T -> W) := Littleo {
  littleo_fun :> T -> V;
  _ : `[< littleo_def F littleo_fun g >]
}.
Notation "{o_ F f }" := (littleo_type F f).

Canonical littleo_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@littleo_fun F g)].

Lemma littleo_class (F : set (set T)) (g : T -> W) (f : {o_F g}) :
  `[< littleo_def F f g >].
Proof. by case: f => ?. Qed.
Hint Resolve littleo_class : core.

Definition littleo_clone (F : set (set T)) (g : T -> W) (f : T -> V) (fT : {o_F g}) c
  of phant_id (littleo_class fT) c := @Littleo F g f c.
Notation "[littleo 'of' f 'for' fT ]" := (@littleo_clone _ _ f fT _ idfun).
Notation "[littleo 'of' f ]" := (@littleo_clone _ _ f _ _ idfun).

Lemma littleo0_subproof F (g : T -> W) :
  Filter F -> littleo_def F (0 : T -> V) g.
Proof.
move=> FF _/posnumP[eps] /=; apply: filterE => x; rewrite normm0.
by rewrite mulr_ge0 // ltrW.
Qed.

Canonical littleo0 (F : filter_on T) g :=
  Littleo (asboolT (@littleo0_subproof F g _)).

Definition the_littleo (_ : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := littleo_fun (insubd (littleo0 F h) f).
Notation PhantomF := (Phantom (set (set T))).
Arguments the_littleo : simpl never, clear implicits.

Notation mklittleo tag x := (the_littleo tag _ (PhantomF x)).
(* Parsing *)
Notation "[o_ x e 'of' f ]" := (mklittleo gen_tag x f e).
(*Printing*)
Notation "[o '_' x e 'of' f ]" := (the_littleo _ _ (PhantomF x) f e).
(* These notations are printing only in order to display 'o
   without looking at the contents, use showo to display *)
Notation "''o_' x e " := (the_littleo the_tag _ (PhantomF x) _ e).
Notation "''a_o_' x e " := (the_littleo a_tag _ (PhantomF x) _ e).
Notation "''o' '_' x" := (the_littleo gen_tag _ (PhantomF x) _).

Notation "f = g '+o_' F h" :=
  (f%function = g%function + mklittleo the_tag F (f \- g) h).
Notation "f '=o_' F h" := (f%function = (mklittleo the_tag F f h)).
Notation "f == g '+o_' F h" :=
  (f%function == g%function + mklittleo the_tag F (f \- g) h).
Notation "f '==o_' F h" := (f%function == (mklittleo the_tag F f h)).

Notation "[o_( x \near F ) ex 'of' f ]" :=
  (mklittleo gen_tag F (fun x => f) (fun x => ex) x).
Notation "[o '_(' x \near F ')' ex 'of' f ]" :=
  (the_littleo _ _ (PhantomF F) (fun x => f) (fun x => ex) x).
Notation "''o_(' x \near F ')' ex" :=
  (the_littleo the_tag _ (PhantomF F) _ (fun x => ex) x).
Notation "''a_o_(' x \near F ')' ex" :=
  (the_littleo a_tag _ (PhantomF F) _ (fun x => ex) x).
Notation "''o' '_(' x \near F ')' ex" :=
  (the_littleo gen_tag _ (PhantomF F) _ (fun x => ex) x).

Notation "fx = gx '+o_(' x \near F ')' hx" :=
  (fx = gx + mklittleo the_tag F
                  ((fun x => fx) \- (fun x => gx%R)) (fun x => hx) x).
Notation "fx '=o_(' x \near F ')' hx" :=
  (fx = (mklittleo the_tag F (fun x => fx) (fun x => hx) x)).
Notation "fx == gx '+o_(' x \near F ')' hx" :=
  (fx == gx + mklittleo the_tag F
                  ((fun x => fx) \- (fun x => gx%R)) (fun x => hx) x).
Notation "fx '==o_(' x \near F ')' hx" :=
  (fx == (mklittleo the_tag F (fun x => fx) (fun x => hx) x)).

Lemma littleoP (F : set (set T)) (g : T -> W) (f : {o_F g}) : littleo_def F f g.
Proof. exact/asboolP. Qed.
Hint Extern 0 (littleo_def _ _ _) => solve[apply: littleoP] : core.
Hint Extern 0 (locally _ _) => solve[apply: littleoP] : core.
Hint Extern 0 (prop_near1 _) => solve[apply: littleoP] : core.
Hint Extern 0 (prop_near2 _) => solve[apply: littleoP] : core.

Lemma littleoE (tag : unit) (F : filter_on T)
   (phF : phantom (set (set T)) F) f h :
   littleo_def F f h -> the_littleo tag F phF f h = f.
Proof. by move=> /asboolP?; rewrite /the_littleo /insubd insubT. Qed.

Canonical the_littleo_littleo (tag : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := [littleo of the_littleo tag F phF f h].

Variant littleo_spec (F : set (set T)) (g : T -> W) : (T -> V) -> Type :=
  LittleoSpec f of littleo_def F f g : littleo_spec F g f.

Lemma littleo (F : set (set T)) (g : T -> W) (f : {o_F g}) : littleo_spec F g f.
Proof. by constructor; apply/(@littleoP F). Qed.

Lemma opp_littleo_subproof (F : filter_on T) e (df : {o_F e}) :
   littleo_def F (- (df : _ -> _)) e.
Proof.
by move=> _/posnumP[eps]; near=> x; rewrite normmN; near: x; apply: littleoP.
Grab Existential Variables. all: end_near. Qed.

Canonical opp_littleo (F : filter_on T) e (df : {o_F e}) :=
  Littleo (asboolT (opp_littleo_subproof df)).

Lemma oppo (F : filter_on T) (f : T -> V) e : - [o_F e of f] =o_F e.
Proof. by rewrite [RHS]littleoE. Qed.

Lemma oppox (F : filter_on T) (f : T -> V) e x :
  - [o_F e of f] x = [o_F e of - [o_F e of f]] x.
Proof. by move: x; rewrite -/(- _ =1 _) {1}oppo. Qed.

Lemma add_littleo_subproof (F : filter_on T) e (df dg : {o_F e}) :
  littleo_def F (df \+ dg) e.
Proof.
move=> _/posnumP[eps]; near=> x => /=.
rewrite [eps%:num]splitr mulrDl (ler_trans (ler_normm_add _ _)) // ler_add //;
by near: x; apply: littleoP.
Grab Existential Variables. all: end_near. Qed.

Canonical add_littleo (F : filter_on T) e (df dg : {o_F e}) :=
  @Littleo _ _ (_ + _) (asboolT (add_littleo_subproof df dg)).
Canonical addfun_littleo (F : filter_on T) e (df dg : {o_F e}) :=
  @Littleo _ _ (_ \+ _) (asboolT (add_littleo_subproof df dg)).

Lemma addo (F : filter_on T) (f g: T -> V) e :
  [o_F e of f] + [o_F e of g] =o_F e.
Proof. by rewrite [RHS]littleoE. Qed.

Lemma addox (F : filter_on T) (f g: T -> V) e x :
  [o_F e of f] x + [o_F e of g] x =
  [o_F e of [o_F e of f] + [o_F e of g]] x.
Proof. by move: x; rewrite -/(_ + _ =1 _) {1}addo. Qed.

Lemma eqadd_some_oP (F : filter_on T) (f g : T -> V) (e : T -> W) h :
  f = g + [o_F e of h] -> littleo_def F (f - g) e.
Proof.
rewrite /the_littleo /insubd=> ->.
case: insubP => /= [u /asboolP fg_o_e ->|_] eps  /=.
  by rewrite addrAC subrr add0r; apply: fg_o_e.
by rewrite addrC addKr; apply: littleoP.
Qed.

Lemma eqaddoP (F : filter_on T) (f g : T -> V) (e : T -> W) :
   (f = g +o_ F e) <-> (littleo_def F (f - g) e).
Proof.
by split=> [/eqadd_some_oP|fg_o_e]; rewrite ?littleoE // addrC addrNK.
Qed.

Lemma eqoP (F : filter_on T) (e : T -> W) (f : T -> V) :
   (f =o_ F e) <-> (littleo_def F f e).
Proof. by rewrite -[f]subr0 -eqaddoP -[f \- 0]/(f - 0) subr0 add0r. Qed.

Lemma eq_some_oP (F : filter_on T) (e : T -> W) (f : T -> V) h :
   f = [o_F e of h] -> littleo_def F f e.
Proof. by have := @eqadd_some_oP F f 0 e h; rewrite add0r subr0. Qed.

(* replaces a 'o_F e by a "canonical one" *)
(* mostly to prevent problems with dependent types *)
Lemma eqaddoE (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  f = g + mklittleo a_tag F h e -> f = g +o_ F e.
Proof. by move=> /eqadd_some_oP /eqaddoP. Qed.

Lemma eqoE (F : filter_on T) (f : T -> V) h (e : T -> W) :
  f = mklittleo a_tag F h e -> f =o_F e.
Proof. by move=> /eq_some_oP /eqoP. Qed.

Lemma eqoEx (F : filter_on T) (f : T -> V) h (e : T -> W) :
  (forall x, f x = mklittleo a_tag F h e x) ->
  (forall x, f x =o_(x \near F) e x).
Proof. by have := @eqoE F f h e; rewrite !funeqE. Qed.

Lemma eqaddoEx (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  (forall x, f x = g x + mklittleo a_tag F h e x) ->
  (forall x, f x = g x +o_(x \near F) (e x)).
Proof. by have := @eqaddoE F f g h e; rewrite !funeqE. Qed.

Lemma littleo_eqo (F : filter_on T) (g : T -> W) (f : {o_F g}) :
   (f : _ -> _) =o_F g.
Proof. by apply/eqoP. Qed.

Lemma scale_littleo_subproof (F : filter_on T) e (df : {o_F e}) a :
  littleo_def F (a *: (df : _ -> _)) e.
Proof.
have [->|a0] := eqVneq a 0; first by rewrite scale0r.
move=> _ /posnumP[eps]; have aa := absr_eq0 a; near=> x => /=.
rewrite normmZ -ler_pdivl_mull ?ltr_def ?aa ?a0 //= mulrA; near: x.
by apply: littleoP; rewrite mulr_gt0 // invr_gt0 ?ltr_def ?aa ?a0 /=.
Grab Existential Variables. all: end_near. Qed.

Canonical scale_littleo (F : filter_on T) e a (df : {o_F e}) :=
  Littleo (asboolT (scale_littleo_subproof df a)).

Lemma scaleo (F : filter_on T) a (f : T -> V) e :
  a *: [o_F e of f] = [o_F e of a *: [o_F e of f]].
Proof. by rewrite [RHS]littleoE. Qed.

Lemma scaleox (F : filter_on T) a (f : T -> V) e x :
  a *: ([o_F e of f] x) = [o_F e of a *: [o_F e of f]] x.
Proof. by move: x; rewrite -/(_ *: _ =1 _) {1}scaleo. Qed.

Let bigO_def (F : set (set T)) (f : T -> V) (g : T -> W) :=
  \forall k \near +oo, \forall x \near F, `|[f x]| <= k * `|[g x]|.

Let bigO_ex_def (F : set (set T)) (f : T -> V) (g : T -> W) :=
  exists2 k, k > 0 & \forall x \near F, `|[f x]| <= k * `|[g x]|.

Lemma bigO_exP (F : set (set T)) (f : T -> V) (g : T -> W) :
  Filter F -> bigO_ex_def F f g <-> bigO_def F f g.
Proof.
split=> [[k _ fOg] | [k fOg]].
  exists k => l ltkl; move: fOg; apply: filter_app; near=> x.
  by move/ler_trans; apply; rewrite ler_wpmul2r // ltrW.
exists (maxr 1 (k + 1)); first by rewrite ltr_maxr ltr01.
by apply: fOg; rewrite ltr_maxr orbC ltr_addl ltr01.
Unshelve. end_near. Qed.

Structure bigO_type (F : set (set T)) (g : T -> W) := BigO {
  bigO_fun :> T -> V;
  _ : `[< bigO_def F bigO_fun g >]
}.
Notation "{O_ F f }" := (bigO_type F f).

Canonical bigO_subtype (F : set (set T)) (g : T -> W) :=
  [subType for (@bigO_fun F g)].

Lemma bigO_class (F : set (set T)) (g : T -> W) (f : {O_F g}) :
  `[< bigO_def F f g >].
Proof. by case: f => ?. Qed.
Hint Resolve bigO_class : core.

Definition bigO_clone (F : set (set T)) (g : T -> W) (f : T -> V) (fT : {O_F g}) c
  of phant_id (bigO_class fT) c := @BigO F g f c.
Notation "[bigO 'of' f 'for' fT ]" := (@bigO_clone _ _ f fT _ idfun).
Notation "[bigO 'of' f ]" := (@bigO_clone _ _ f _ _ idfun).

Lemma bigO0_subproof F (g : T -> W) : Filter F -> bigO_def F (0 : T -> V) g.
Proof.
by move=> FF; near=> k; apply: filterE => x; rewrite normm0 pmulr_rge0.
Grab Existential Variables. end_near. Qed.

Canonical bigO0 (F : filter_on T) g := BigO (asboolT (@bigO0_subproof F g _)).

Definition the_bigO (u : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := bigO_fun (insubd (bigO0 F h) f).
Arguments the_bigO : simpl never, clear implicits.

Notation mkbigO tag x := (the_bigO tag _ (PhantomF x)).
(* Parsing *)
Notation "[O_ x e 'of' f ]" := (mkbigO gen_tag x f e).
(*Printing*)
Notation "[O '_' x e 'of' f ]" := (the_bigO _ _ (PhantomF x) f e).
(* These notations are printing only in order to display 'o
   without looking at the contents, use showo to display *)
Notation "''O_' x e " := (the_bigO the_tag _ (PhantomF x) _ e).
Notation "''a_O_' x e " := (the_bigO a_tag _ (PhantomF x) _ e).
Notation "''O' '_' x" := (the_bigO gen_tag _ (PhantomF x) _).

Notation "[O_( x \near F ) e 'of' f ]" :=
  (mkbigO gen_tag F (fun x => f) (fun x => e) x).
Notation "[O '_(' x \near F ')' e 'of' f ]" :=
  (the_bigO _ _ (PhantomF F) (fun x => f) (fun x => e) x).
Notation "''O_(' x \near F ')' e" :=
  (the_bigO the_tag _ (PhantomF F) _ (fun x => e) x).
Notation "''a_O_(' x \near F ')' e" :=
  (the_bigO a_tag _ (PhantomF F) _ (fun x => e) x).
Notation "''O' '_(' x \near F ')' e" :=
  (the_bigO gen_tag _ (PhantomF F) _ (fun x => e) x).

Notation "f = g '+O_' F h" :=
  (f%function = g%function + mkbigO the_tag F (f \- g) h).
Notation "f '=O_' F h" := (f%function = mkbigO the_tag F f h).
Notation "f == g '+O_' F h" :=
  (f%function == g%function + mkbigO the_tag F (f \- g) h).
Notation "f '==O_' F h" := (f%function == mkbigO the_tag F f h).

Notation "fx = gx '+O_(' x \near F ')' hx" :=
  (fx = gx + mkbigO the_tag F
                  ((fun x => fx) \- (fun x => gx%R)) (fun x => hx) x).
Notation "fx '=O_(' x \near F ')' hx" :=
  (fx = (mkbigO the_tag F (fun x => fx) (fun x => hx) x)).
Notation "fx == gx '+O_(' x \near F ')' hx" :=
  (fx == gx + mkbigO the_tag F
                  ((fun x => fx) \- (fun x => gx%R)) (fun x => hx) x).
Notation "fx '==O_(' x \near F ')' hx" :=
  (fx == (mkbigO the_tag F (fun x => fx) (fun x => hx) x)).

Lemma bigOP (F : set (set T)) (g : T -> W) (f : {O_F g}) : bigO_def F f g.
Proof. exact/asboolP. Qed.
Hint Extern 0 (bigO_def _ _ _) => solve[apply: bigOP] : core.
Hint Extern 0 (locally _ _) => solve[apply: bigOP] : core.
Hint Extern 0 (prop_near1 _) => solve[apply: bigOP] : core.
Hint Extern 0 (prop_near2 _) => solve[apply: bigOP] : core.

Lemma bigOE (tag : unit) (F : filter_on T) (phF : phantom (set (set T)) F) f h :
   bigO_def F f h -> the_bigO tag F phF f h = f.
Proof. by move=> /asboolP?; rewrite /the_bigO /insubd insubT. Qed.

Canonical the_bigO_bigO (tag : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := [bigO of the_bigO tag F phF f h].

Variant bigO_spec (F : set (set T)) (g : T -> W) : (T -> V) -> Prop :=
  BigOSpec f (k : posreal)
    of (\forall x \near F, `|[f x]| <= k%:num * `|[g x]|) :
      bigO_spec F g f.

Lemma bigO (F : filter_on T) (g : T -> W) (f : {O_F g}) : bigO_spec F g f.
Proof. by have /bigO_exP [_/posnumP[k] kP] := bigOP f; exists k. Qed.

Lemma opp_bigO_subproof (F : filter_on T) e (df : {O_F e}) :
   bigO_def F (- (df : _ -> _)) e.
Proof.
have := bigOP [bigO of df]; apply: filter_app; near=> k.
by apply: filter_app; near=> x; rewrite normmN.
Grab Existential Variables. all: end_near. Qed.

Canonical Opp_bigO (F : filter_on T) e (df : {O_F e}) :=
  BigO (asboolT (opp_bigO_subproof df)).

Lemma oppO (F : filter_on T) (f : T -> V) e : - [O_F e of f] =O_F e.
Proof. by rewrite [RHS]bigOE. Qed.

Lemma oppOx (F : filter_on T) (f : T -> V) e x :
  - [O_F e of f] x = [O_F e of - [O_F e of f]] x.
Proof. by move: x; rewrite -/(- _ =1 _) {1}oppO. Qed.

Lemma add_bigO_subproof (F : filter_on T) e (df dg : {O_F e}) :
  bigO_def F (df \+ dg) e.
Proof.
near=> k; near=> x; apply: ler_trans (ler_normm_add _ _) _.
by rewrite (splitr k) mulrDl ler_add //; near: x; near: k;
  [apply: near_pinfty_div2 (bigOP df)|apply: near_pinfty_div2 (bigOP dg)].
Grab Existential Variables. all: end_near. Qed.

Canonical add_bigO (F : filter_on T) e (df dg : {O_F e}) :=
  @BigO _ _ (_ + _) (asboolT (add_bigO_subproof df dg)).
Canonical addfun_bigO (F : filter_on T) e (df dg : {O_F e}) :=
  BigO (asboolT (add_bigO_subproof df dg)).

Lemma addO (F : filter_on T) (f g: T -> V) e :
  [O_F e of f] + [O_F e of g] =O_F e.
Proof. by rewrite [RHS]bigOE. Qed.

Lemma addOx (F : filter_on T) (f g: T -> V) e x :
  [O_F e of f] x + [O_F e of g] x =
  [O_F e of [O_F e of f] + [O_F e of g]] x.
Proof. by move: x; rewrite -/(_ + _ =1 _) {1}addO. Qed.

Lemma eqadd_some_OP (F : filter_on T) (f g : T -> V) (e : T -> W) h :
  f = g + [O_F e of h] -> bigO_def F (f - g) e.
Proof.
rewrite /the_bigO /insubd=> ->.
case: insubP => /= [u /asboolP fg_o_e ->|_].
  by rewrite addrAC subrr add0r; apply: fg_o_e.
by rewrite addrC addKr; apply: bigOP.
Qed.

Lemma eqaddOP (F : filter_on T) (f g : T -> V) (e : T -> W) :
   (f = g +O_ F e) <-> (bigO_def F (f - g) e).
Proof. by split=> [/eqadd_some_OP|fg_O_e]; rewrite ?bigOE // addrC addrNK. Qed.

Lemma eqOP (F : filter_on T) (e : T -> W) (f : T -> V) :
   (f =O_ F e) <-> (bigO_def F f e).
Proof. by rewrite -[f]subr0 -eqaddOP -[f \- 0]/(f - 0) subr0 add0r. Qed.

Lemma eqO_exP (F : filter_on T) (e : T -> W) (f : T -> V) :
   (f =O_ F e) <-> (bigO_ex_def F f e).
Proof. apply: iff_trans (iff_sym (bigO_exP _ _ _)); apply: eqOP. Qed.

Lemma eq_some_OP (F : filter_on T) (e : T -> W) (f : T -> V) h :
   f = [O_F e of h] -> bigO_def F f e.
Proof. by have := @eqadd_some_OP F f 0 e h; rewrite add0r subr0. Qed.

Lemma bigO_eqO (F : filter_on T) (g : T -> W) (f : {O_F g}) :
   (f : _ -> _) =O_F g.
Proof. by apply/eqOP; apply: bigOP. Qed.

Lemma eqO_bigO (F : filter_on T) (e : T -> W) (f : T -> V) :
   f =O_ F e -> bigO_def F f e.
Proof. by rewrite eqOP. Qed.

(* replaces a 'O_F e by a "canonical one" *)
(* mostly to prevent problems with dependent types *)
Lemma eqaddOE (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  f = g + mkbigO a_tag F h e -> f = g +O_ F e.
Proof.  by move=> /eqadd_some_OP /eqaddOP. Qed.

Lemma eqOE (F : filter_on T) (f : T -> V) h (e : T -> W) :
  f = mkbigO a_tag F h e -> f =O_F e.
Proof. by move=> /eq_some_OP /eqOP. Qed.

Lemma eqOEx (F : filter_on T) (f : T -> V) h (e : T -> W) :
  (forall x, f x = mkbigO a_tag F h e x) ->
  (forall x, f x =O_(x \near F) e x).
Proof. by have := @eqOE F f h e; rewrite !funeqE. Qed.

Lemma eqaddOEx (F : filter_on T) (f g : T -> V) h (e : T -> W) :
  (forall x, f x = g x + mkbigO a_tag F h e x) ->
  (forall x, f x = g x +O_(x \near F) (e x)).
Proof. by have := @eqaddOE F f g h e; rewrite !funeqE. Qed.

Lemma eqoO (F : filter_on T) (f : T -> V) (e : T -> W) :
  [o_F e of f] =O_F e.
Proof. by apply/eqOP; exists 0 => k kgt0; apply: littleoP. Qed.
Hint Resolve eqoO : core.

Lemma littleo_eqO (F : filter_on T) (e : T -> W) (f : {o_F e}) :
   (f : _ -> _) =O_F e.
Proof. by apply: eqOE; rewrite littleo_eqo. Qed.

Canonical littleo_is_bigO (F : filter_on T) (e : T -> W) (f : {o_F e}) :=
  BigO (asboolT (eqO_bigO (littleo_eqO f))).
Canonical the_littleo_bigO (tag : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := [bigO of the_littleo tag F phF f h].

End Domination.

Notation "{o_ F f }" := (@littleo_type _ _ _ _ F f).
Notation "{O_ F f }" := (@bigO_type _ _ _ _ F f).

Notation "[littleo 'of' f 'for' fT ]" :=
  (@littleo_clone _ _ _ _ _ _ f fT _ idfun).
Notation "[littleo 'of' f ]" := (@littleo_clone _ _ _ _ _ _ f _ _ idfun).

Notation "[bigO 'of' f 'for' fT ]" := (@bigO_clone _ _ _ _ _ _ f fT _ idfun).
Notation "[bigO 'of' f ]" := (@bigO_clone _ _ _ _ _ _ f _ _ idfun).

Arguments the_littleo {_ _ _ _} _ _ _ _ _ : simpl never.
Arguments the_bigO {_ _ _ _} _ _ _ _ _ : simpl never.
Local Notation PhantomF x := (Phantom _ [filter of x]).

Notation mklittleo tag x := (the_littleo tag _ (PhantomF x)).
(* Parsing *)
Notation "[o_ x e 'of' f ]" := (mklittleo gen_tag x f e).
Notation "[o_( x \near F ) e 'of' f ]" :=
  (mklittleo gen_tag F (fun x => f) (fun x => e) x).
Notation "'o_ x" := (the_littleo _ _ (PhantomF x) _).
Notation "'o" := (the_littleo _ _ _ _).
(*Printing*)
Notation "[o '_(' x \near F ')' e 'of' f ]" :=
  (the_littleo _ _ (PhantomF F) (fun x => f) (fun x => e) x).
Notation "[o '_' x e 'of' f ]" := (the_littleo _ _ (Phantom _ x) f e).
(* These notations are printing only in order to display 'o
   without looking at the contents, use showo to display *)
Notation "''o_' x e " := (the_littleo the_tag _ (Phantom _ x) _ e).
Notation "''a_o_' x e " := (the_littleo a_tag _ (Phantom _ x) _ e).
Notation "''o' '_' x" := (the_littleo gen_tag _ (Phantom _ x) _).

Notation "''o_(' x \near F ')' e" :=
  (the_littleo the_tag _ (PhantomF F) _ (fun x => e) x).
Notation "''a_o_(' x \near F ')' e" :=
  (the_littleo a_tag _ (PhantomF F) _ (fun x => e) x).
Notation "''o' '_(' x \near F ')' e" :=
  (the_littleo gen_tag _ (PhantomF F) _ (fun x => e) x).

Notation mkbigO tag x := (the_bigO tag _ (PhantomF x)).
(* Parsing *)
Notation "[O_ x e 'of' f ]" := (mkbigO gen_tag x f e).
Notation "[O_( x \near F ) e 'of' f ]" :=
  (mkbigO gen_tag F (fun x => f) (fun x => e) x).
Notation "'O_ x" := (the_bigO _ _ (PhantomF x) _).
Notation "'O" := (the_bigO _ _ _ _).
(*Printing*)
Notation "[O '_' x e 'of' f ]" := (the_bigO _ _ (Phantom _ x) f e).
Notation "[O '_(' x \near F ')' e 'of' f ]" :=
  (the_bigO _ _ (PhantomF F) (fun x => f) (fun x => e) x).
(* These notations are printing only in order to display 'o
   without looking at the contents, use showo to display *)
Notation "''O_' x e " := (the_bigO the_tag _ (Phantom _ x) _ e).
Notation "''a_O_' x e " := (the_bigO a_tag _ (Phantom _ x) _ e).
Notation "''O' '_' x" := (the_bigO gen_tag _ (Phantom _ x) _).

Notation "''O_(' x \near F ')' e" :=
  (the_bigO the_tag _ (PhantomF F) _ (fun x => e) x).
Notation "''a_O_(' x \near F ')' e" :=
  (the_bigO a_tag _ (PhantomF F) _ (fun x => e) x).
Notation "''O' '_(' x \near F ')' e" :=
  (the_bigO gen_tag _ (PhantomF F) _ (fun x => e) x).

Notation "f = g '+o_' F h" :=
  (f%function = g%function + mklittleo the_tag F (f \- g) h).
Notation "f '=o_' F h" := (f%function = (mklittleo the_tag F f h)).
Notation "f == g '+o_' F h" :=
  (f%function == g%function + mklittleo the_tag F (f \- g) h).
Notation "f '==o_' F h" := (f%function == (mklittleo the_tag F f h)).
Notation "fx = gx '+o_(' x \near F ')' hx" :=
  (fx = gx + mklittleo the_tag F
                  ((fun x => fx) \- (fun x => gx%R)) (fun x => hx) x).
Notation "fx '=o_(' x \near F ')' hx" :=
  (fx = (mklittleo the_tag F (fun x => fx) (fun x => hx) x)).
Notation "fx == gx '+o_(' x \near F ')' hx" :=
  (fx == gx + mklittleo the_tag F
                  ((fun x => fx) \- (fun x => gx%R)) (fun x => hx) x).
Notation "fx '==o_(' x \near F ')' hx" :=
  (fx == (mklittleo the_tag F (fun x => fx) (fun x => hx) x)).

Notation "f = g '+O_' F h" :=
  (f%function = g%function + mkbigO the_tag F (f \- g) h).
Notation "f '=O_' F h" := (f%function = mkbigO the_tag F f h).
Notation "f == g '+O_' F h" :=
  (f%function == g%function + mkbigO the_tag F (f \- g) h).
Notation "f '==O_' F h" := (f%function == mkbigO the_tag F f h).
Notation "fx = gx '+O_(' x \near F ')' hx" :=
  (fx = gx + mkbigO the_tag F
                  ((fun x => fx) \- (fun x => gx%R)) (fun x => hx) x).
Notation "fx '=O_(' x \near F ')' hx" :=
  (fx = (mkbigO the_tag F (fun x => fx) (fun x => hx) x)).
Notation "fx == gx '+O_(' x \near F ')' hx" :=
  (fx == gx + mkbigO the_tag F
                  ((fun x => fx) \- (fun x => gx%R)) (fun x => hx) x).
Notation "fx '==O_(' x \near F ')' hx" :=
  (fx == (mkbigO the_tag F (fun x => fx) (fun x => hx) x)).

Hint Extern 0 (_ = 'o__ _) => apply: eqoE; reflexivity : core.
Hint Extern 0 (_ = 'O__ _) => apply: eqOE; reflexivity : core.
Hint Extern 0 (_ = 'O__ _) => apply: eqoO; reflexivity : core.
Hint Extern 0 (_ = _ + 'o__ _) => apply: eqaddoE; reflexivity : core.
Hint Extern 0 (_ = _ + 'O__ _) => apply: eqaddOE; reflexivity : core.
Hint Extern 0 (\forall k \near +oo, \forall x \near _,
  is_true (`|[_ x]| <= k * `|[_ x]|)) => solve[apply: bigOP] : core.
Hint Extern 0 (locally _ _) => solve[apply: bigOP] : core.
Hint Extern 0 (prop_near1 _) => solve[apply: bigOP] : core.
Hint Extern 0 (prop_near2 _) => solve[apply: bigOP] : core.
Hint Extern 0 (forall e, is_true (0 < e) -> \forall x \near _,
  is_true (`|[_ x]| <= e * `|[_ x]|)) => solve[apply: littleoP] : core.
Hint Extern 0 (locally _ _) => solve[apply: littleoP] : core.
Hint Extern 0 (prop_near1 _) => solve[apply: littleoP] : core.
Hint Extern 0 (prop_near2 _) => solve[apply: littleoP] : core.
Hint Resolve littleo_class : core.
Hint Resolve bigO_class : core.
Hint Resolve littleo_eqO : core.

Arguments bigO {_ _ _ _}.

(* NB: see also scaleox *)
Lemma scaleolx (K : absRingType) (V W : normedModType K) {T : Type}
  (F : filter_on T) (a : W) (k : T -> K^o) (e : T -> V) (x : T) :
  ([o_F e of k] x) *: a = [o_F e of (fun y => [o_F e of k] y *: a)] x.
Proof.
rewrite [in RHS]littleoE //.
have [->|a0] := eqVneq a 0.
  by move=> ??; apply: filterE => ?; rewrite scaler0 normm0 pmulr_rge0.
move=> _/posnumP[eps].
have ea : 0 < eps%:num / `|[ a ]| by rewrite divr_gt0 // normm_gt0.
have [g /(_ _ ea) ?] := littleo; near=> y.
rewrite normmZ -ler_pdivl_mulr; first by rewrite mulrAC; near: y.
by rewrite ltr_def normm_eq0 a0 normm_ge0.
Grab Existential Variables. all: end_near. Qed.

Section Limit.

Context {K : absRingType} {T : Type} {V W X : normedModType K}.

Lemma eqolimP (F : filter_on T) (f : T -> V) (l : V) :
  f @ F --> l <-> f = cst l +o_F (cst (1 : K^o)).
Proof.
split=> fFl.
  apply/eqaddoP => _/posnumP[eps]; near=> x.
  rewrite /cst ltrW //= normmB; near: x.
  by apply: (flim_norm _ fFl); rewrite mulr_gt0 // ?absr1_gt0.
apply/flim_normP=> _/posnumP[eps]; rewrite /= near_simpl.
have lt_eps x : x <= (eps%:num / 2%:R) * `|1 : K^o|%real -> x < eps.
  rewrite absr1 mulr1 => /ler_lt_trans; apply.
  by rewrite ltr_pdivr_mulr // ltr_pmulr // ltr1n.
near=> x; rewrite [X in X x]fFl opprD addNKr normmN lt_eps //; near: x.
by rewrite /= !near_simpl; apply: littleoP; rewrite divr_gt0.
Grab Existential Variables. all: end_near. Qed.

Lemma eqolim (F : filter_on T) (f : T -> V) (l : V) e :
  f = cst l + [o_F (cst (1 : K^o)) of e] -> f @ F --> l.
Proof. by move=> /eqaddoE /eqolimP. Qed.

Lemma eqolim0P (F : filter_on T) (f : T -> V) :
  f @ F --> (0 : V) <-> f =o_F (cst (1 : K^o)).
Proof. by rewrite eqolimP add0r -[f \- cst 0]/(f - 0) subr0. Qed.

Lemma eqolim0 (F : filter_on T) (f : T -> V) :
  f =o_F (cst (1 : K^o)) -> f @ F --> (0 : V).
Proof. by move=> /eqoE /eqolim0P. Qed.

(* ideally the precondition should be f = '[O_F g of f'] with a *)
(* universally quantified f' which is irrelevant and replaced by *)
(* a hole, on the fly, by ssreflect rewrite *)

Lemma littleo_bigO_eqo {F : filter_on T}
  (g : T -> W) (f : T -> V) (h : T -> X) :
  f =O_F g -> [o_F f of h] =o_F g.
Proof.
move->; apply/eqoP => _/posnumP[e]; have [k c] := bigO _ g.
apply: filter_app; near=> x.
rewrite -!ler_pdivr_mull //; apply: ler_trans; rewrite ler_pdivr_mull // mulrA.
by near: x; apply: littleoP.
Grab Existential Variables. all: end_near. Qed.
Arguments littleo_bigO_eqo {F}.

Lemma bigO_littleo_eqo {F : filter_on T} (g : T -> W) (f : T -> V) (h : T -> X) :
  f =o_F g -> [O_F f of h] =o_F g.
Proof.
move->; apply/eqoP => _/posnumP[e]; have [k c] := bigO.
apply: filter_app; near=> x => /ler_trans; apply.
by rewrite -ler_pdivl_mull // mulrA; near: x; apply: littleoP.
Grab Existential Variables. all: end_near. Qed.
Arguments bigO_littleo_eqo {F}.

Lemma bigO_bigO_eqO {F : filter_on T} (g : T -> W) (f : T -> V) (h : T -> X) :
  f =O_F g -> ([O_F f of h] : _ -> _) =O_F g.
Proof.
move->; apply/eqOP; have [k c1 kOg] := bigO _ g. have [k' c2 k'Ok] := bigO _ k.
near=> c; move: k'Ok kOg; apply: filter_app2; near=> x => lek'c2k.
rewrite -(@ler_pmul2l _ c2) // mulrA => /(ler_trans lek'c2k) /ler_trans; apply.
by rewrite ler_pmul //; near: c; apply: locally_pinfty_ge.
Unshelve. end_near. Grab Existential Variables. all: end_near. Qed.
Arguments bigO_bigO_eqO {F}.

Lemma add2o (F : filter_on T) (f g : T -> V) (e : T -> W) :
  f =o_F e -> g =o_F e -> f + g =o_F e.
Proof. by move=> -> ->; rewrite addo. Qed.

Lemma addfo (F : filter_on T) (h f : T -> V) (e : T -> W) :
  f =o_F e -> f + [o_F e of h] =o_F e.
Proof. by move->; rewrite addo. Qed.

Lemma oppfo (F : filter_on T) (h f : T -> V) (e : T -> W) :
  f =o_F e -> - f =o_F e.
Proof. by move->; rewrite oppo. Qed.

Lemma add2O (F : filter_on T) (f g : T -> V) (e : T -> W) :
  f =O_F e -> g =O_F e -> f + g =O_F e.
Proof. by move=> -> ->; rewrite addO. Qed.

Lemma addfO (F : filter_on T) (h f : T -> V) (e : T -> W) :
  f =O_F e -> f + [O_F e of h] =O_F e.
Proof. by move->; rewrite addO. Qed.

Lemma oppfO (F : filter_on T) (h f : T -> V) (e : T -> W) :
  f =O_F e -> - f =O_F e.
Proof. by move->; rewrite oppO. Qed.

Lemma idO (F : filter_on T) (e : T -> W) : e =O_F e.
Proof. by apply/eqO_exP; exists 1 => //; apply: filterE=> x; rewrite mul1r. Qed.

Lemma littleo_littleo (F : filter_on T) (f : T -> V) (g : T -> W) (h : T -> X) :
  f =o_F g -> [o_F f of h] =o_F g.
Proof. by move=> ->; apply: eqoE; rewrite (littleo_bigO_eqo g). Qed.

End Limit.

Arguments littleo_bigO_eqo {K T V W X F}.
Arguments bigO_littleo_eqo {K T V W X F}.
Arguments bigO_bigO_eqO {K T V W X F}.

Section littleo_bigO_transitivity.

Context {K : absRingType} {T : Type} {V W Z : normedModType K}.

Lemma eqaddo_trans (F : filter_on T) (f g h : T -> V) fg gh (e : T -> W):
  f = g + [o_ F e of fg] -> g = h + [o_F e of gh] -> f = h +o_F e.
Proof. by move=> -> ->; rewrite -addrA addo. Qed.

Lemma eqaddO_trans (F : filter_on T) (f g h : T -> V) fg gh (e : T -> W):
  f = g + [O_ F e of fg] -> g = h + [O_F e of gh] -> f = h +O_F e.
Proof. by move=> -> ->; rewrite -addrA addO. Qed.

Lemma eqaddoO_trans (F : filter_on T) (f g h : T -> V) fg gh (e : T -> W):
  f = g + [o_ F e of fg] -> g = h + [O_F e of gh] -> f = h +O_F e.
Proof. by move=> -> ->; rewrite addrAC -addrA addfO. Qed.

Lemma eqaddOo_trans (F : filter_on T) (f g h : T -> V) fg gh (e : T -> W):
  f = g + [O_ F e of fg] -> g = h + [o_F e of gh] -> f = h +O_F e.
Proof. by move=> -> ->; rewrite -addrA addfO. Qed.

Lemma eqo_trans (F : filter_on T) (f : T -> V) f' (g : T -> W) g' (h : T -> Z) :
  f = [o_F g of f'] -> g = [o_F h of g'] -> f =o_F h.
Proof.  by move=> -> ->; rewrite (littleo_bigO_eqo h). Qed.

Lemma eqO_trans (F : filter_on T) (f : T -> V) f' (g : T -> W) g' (h : T -> Z) :
  f = [O_F g of f'] -> g = [O_F h of g'] -> f =O_F h.
Proof. by move=> -> ->; rewrite (bigO_bigO_eqO h). Qed.

Lemma eqOo_trans (F : filter_on T) (f : T -> V) f' (g : T -> W) g' (h : T -> Z) :
  f = [O_F g of f'] -> g = [o_F h of g'] -> f =o_F h.
Proof. by move=> -> ->; rewrite (bigO_littleo_eqo h). Qed.

Lemma eqoO_trans (F : filter_on T) (f : T -> V) f' (g : T -> W) g' (h : T -> Z) :
  f = [o_F g of f'] -> g = [O_F h of g'] -> f =o_F h.
Proof. by move=> -> ->; rewrite (littleo_bigO_eqo h). Qed.

End littleo_bigO_transitivity.

Section rule_of_products_in_R.

Variable pT : pointedType.

Lemma mulo (F : filter_on pT) (h1 h2 f g : pT -> R^o) :
  [o_F h1 of f] * [o_F h2 of g] =o_F (h1 * h2).
Proof.
rewrite [in RHS]littleoE // => _/posnumP[e]; near=> x.
rewrite [`|[_]|]absrM -(sqr_sqrtr (ltrW [gt0 of e%:num])) expr2.
rewrite [`|[_]|]normrM mulrACA ler_pmul //; near: x;
by have [/= h] := littleo; apply.
Grab Existential Variables. all: end_near. Qed.

Lemma mulO (F : filter_on pT) (h1 h2 f g : pT -> R^o) :
  [O_F h1 of f] * [O_F h2 of g] =O_F (h1 * h2).
Proof.
rewrite [RHS]bigOE//; have [ O1 k1 Oh1] := bigO; have [ O2 k2 Oh2] := bigO.
near=> k; move: Oh1 Oh2; apply: filter_app2; near=> x => leOh1 leOh2.
rewrite [`|[_]|]absrM (ler_trans (ler_pmul _ _ leOh1 leOh2)) //.
rewrite mulrACA [`|[_]| in X in _ <= X]normrM ler_wpmul2r // ?mulr_ge0 //.
by near: k; apply: locally_pinfty_ge.
Unshelve. end_near. Grab Existential Variables. end_near. Qed.

End rule_of_products_in_R.

Section Shift.

Context {R : zmodType} {T : Type}.

Definition shift (x y : R) := y + x.
Notation center c := (shift (- c)).
Arguments shift x / y.

Lemma comp_shiftK (x : R) (f : R -> T) : (f \o shift x) \o center x = f.
Proof. by rewrite funeqE => y /=; rewrite addrNK. Qed.

Lemma comp_centerK (x : R) (f : R -> T) : (f \o center x) \o shift x = f.
Proof. by rewrite funeqE => y /=; rewrite addrK. Qed.

Lemma shift0 : shift 0 = id.
Proof. by rewrite funeqE => x /=; rewrite addr0. Qed.

Lemma center0 : center 0 = id.
Proof. by rewrite oppr0 shift0. Qed.

End Shift.
Arguments shift {R} x / y.
Notation center c := (shift (- c)).

Lemma near_shift {K : absRingType} {R : normedModType K}
   (y x : R) (P : set R) :
   (\near x, P x) = (\forall z \near y, (P \o shift (x - y)) z).
Proof.
rewrite propeqE; split=> /= /locally_normP [_/posnumP[e] ye];
apply/locally_normP; exists e%:num => // t /= et.
  apply: ye; rewrite /= !opprD addrA addrACA subrr add0r.
  by rewrite opprK addrC.
have /= := ye (t - (x - y)); rewrite addrNK; apply.
by rewrite /= !opprB addrA addrCA subrr addr0.
Qed.

Lemma flim_shift {T : Type}  {K : absRingType} {R : normedModType K}
  (x y : R) (f : R -> T) :
  (f \o shift x) @ y = f @ (y + x).
Proof.
rewrite funeqE => A; rewrite /= !near_simpl (near_shift (y + x)).
by rewrite (_ : _ \o _ = A \o f) // funeqE=> z; rewrite /= opprD addNKr addrNK.
Qed.

Section Linear3.
Context (U : normedModType R) (V : normedModType R) (s : R -> V -> V)
        (s_law : GRing.Scale.law s).
Hypothesis (normm_s : forall k x, `|[s k x]| = `|k| * `|[x]|).

(* Split in multiple bits *)
(* - Locally bounded => locally lipschitz *)
(* - locally lipschitz + linear => lipschitz *)
(* - locally lipschitz => continuous at a point *)
(* - lipschitz => uniformly continous *)

Lemma linear_for_continuous (f: {linear U -> V | GRing.Scale.op s_law}) :
  (f : _ -> _) =O_ (0 : U) (cst (1 : R^o)) -> continuous f.
Proof.
move=> /eqO_exP [_/posnumP[k0] Of1] x.
apply/flim_normP => _/posnumP[e]; rewrite !near_simpl.
rewrite (near_shift 0) /= subr0; near=> y => /=.
rewrite -linearB opprD addrC addrNK linearN normmN; near: y.
suff flip : \forall k \near +oo, forall x, `|[f x]| <= k * `|[x]|.
  near +oo => k; near=> y.
  rewrite (ler_lt_trans (near flip k _ _)) // -ltr_pdivl_mull //.
  near: y; apply/locally_normP.
  by eexists; last by move=> ?; rewrite /= sub0r normmN; apply.
have /locally_normP [_/posnumP[d]] := Of1.
rewrite /cst [X in _ * X]absr1 mulr1 => fk; near=> k => y.
case: (ler0P `|[y]|) => [|y0].
  by rewrite normm_le0 => /eqP->; rewrite linear0 !normm0 mulr0.
have ky0 : 0 <= k0%:num / (k * `|[y]|).
  by rewrite pmulr_rge0 // invr_ge0 mulr_ge0 // ltrW.
rewrite -[X in _ <= X]mulr1 -ler_pdivr_mull ?pmulr_rgt0 //.
rewrite -(ler_pmul2l [gt0 of k0%:num]) mulr1 mulrA -[_ / _]ger0_norm //.
rewrite -normm_s.
have <- : GRing.Scale.op s_law =2 s by rewrite GRing.Scale.opE.
rewrite -linearZ fk //= normmB subr0 normmZ absRE ger0_norm //.
rewrite invfM mulrA mulfVK ?lt0r_neq0 // ltr_pdivr_mulr //.
by rewrite mulrC -ltr_pdivr_mulr //; near: k; apply: locally_pinfty_gt.
Grab Existential Variables. all: end_near. Qed.

End Linear3.

Arguments linear_for_continuous {U V s s_law normm_s} f _.

Lemma linear_continuous (U : normedModType R) (V : normedModType R)
  (f : {linear U -> V}) :
  (f : _ -> _) =O_ (0 : U) (cst (1 : R^o)) -> continuous f.
Proof. by apply: linear_for_continuous => ??; rewrite normmZ. Qed.

Lemma linear_for_mul_continuous (U : normedModType R)
  (f : {linear U -> R | (@GRing.mul [ringType of R^o])}) :
  (f : _ -> _) =O_ (0 : U) (cst (1 : R^o)) -> continuous f.
Proof. by apply: linear_for_continuous => ??; rewrite normmZ. Qed.

Notation "f '~_' F g" := (f = g +o_ F g).
Notation "f '~~_' F g" := (f == g +o_ F g).

Section asymptotic_equivalence.

Context {K : absRingType} {T : Type} {V W : normedModType K}.
Implicit Types F : filter_on T.

Lemma equivOLR F (f g : T -> V) : f ~_F g -> f =O_F g.
Proof. by move=> ->; apply: eqOE; rewrite {1}[g](idO F) addrC addfO. Qed.

Lemma equiv_refl F (f : T -> V) : f ~_F f.
Proof. by apply/eqaddoP; rewrite subrr. Qed.

Lemma equivoRL (W' : normedModType K) F (f g : T -> V) (h : T -> W') :
  f ~_F g -> [o_F g of h] =o_F f.
Proof.
move=> ->; apply/eqoP; move=> _/posnumP[eps]; near=> x.
rewrite -ler_pdivr_mull // -[X in g + X]opprK oppo.
rewrite (ler_trans _ (ler_distm_dist _ _)) //.
rewrite [X in _ <= X]ger0_norm ?ler_subr_addr ?add0r; last first.
  by rewrite -[X in _ <= X]mul1r; near: x; apply: littleoP.
rewrite [X in _ <= X]splitr [_ / 2]mulrC.
by rewrite ler_add ?ler_pdivr_mull ?mulrA //; near: x; apply: littleoP.
Grab Existential Variables. all: end_near. Qed.

Lemma equiv_sym F (f g : T -> V) : f ~_F g -> g ~_F f.
Proof.
move=> fg; have /(canLR (addrK _))<- := fg.
by apply:eqaddoE; rewrite oppo (equivoRL _ fg).
Qed.

Lemma equivoLR (W' : normedModType K) F (f g : T -> V) (h : T -> W') :
  f ~_F g -> [o_F f of h] =o_F g.
Proof. by move/equiv_sym/equivoRL. Qed.

Lemma equivORL F (f g : T -> V) : f ~_F g -> g =O_F f.
Proof. by move/equiv_sym/equivOLR. Qed.

Lemma eqoaddo (W' : normedModType K) F (f g : T -> V) (h : T -> W') :
  [o_F f + [o_F f of g] of h] =o_F f.
Proof. by apply: equivoLR. Qed.

Lemma equiv_trans F (f g h : T -> V) : f ~_F g -> g ~_F h -> f ~_F h.
Proof. by move=> -> ->; apply: eqaddoE; rewrite eqoaddo -addrA addo. Qed.

Lemma equivalence_rel_equiv F :
  equivalence_rel [rel f g : T -> V | f ~~_F g].
Proof.
move=> f g h; split; first by apply/eqP/equiv_refl.
by move=> /eqP fg /=; apply/eqP/eqP; apply/equiv_trans => //; apply/equiv_sym.
Qed.

End asymptotic_equivalence.

Section big_omega.

Context {K : absRingType} {T : Type} {V : normedModType K}.
Implicit Types W : normedModType K.

Let bigOmega_def W (F : set (set T)) (f : T -> V) (g : T -> W) :=
  exists2 k, k > 0 & \forall x \near F, `|[f x]| >= k * `|[g x]|.

Structure bigOmega_type {W} (F : set (set T)) (g : T -> W) := BigOmega {
  bigOmega_fun :> T -> V;
  _ : `[< bigOmega_def F bigOmega_fun g >]
}.

Notation "{Omega_ F g }" := (@bigOmega_type _ F g).

Canonical bigOmega_subtype {W} (F : set (set T)) (g : T -> W) :=
  [subType for (@bigOmega_fun W F g)].

Lemma bigOmega_class {W} (F : set (set T)) (g : T -> W) (f : {Omega_F g}) :
  `[< bigOmega_def F f g >].
Proof. by case: f => ?. Qed.
Hint Resolve bigOmega_class : core.

Definition bigOmega_clone {W} (F : set (set T)) (g : T -> W) (f : T -> V)
  (fT : {Omega_F g}) c of phant_id (bigOmega_class fT) c := @BigOmega W F g f c.
Notation "[bigOmega 'of' f 'for' fT ]" := (@bigOmega_clone _ _ _ f fT _ idfun).
Notation "[bigOmega 'of' f ]" := (@bigOmega_clone _ _ _ f _ _ idfun).

Lemma bigOmega_refl_subproof F (g : T -> V) : Filter F -> bigOmega_def F g g.
Proof.
by move=> FF; exists 1 => //; near=> x; rewrite mul1r.
Grab Existential Variables. all: end_near. Qed.

Definition bigOmega_refl (F : filter_on T) g :=
  BigOmega (asboolT (@bigOmega_refl_subproof F g _)).

Definition the_bigOmega (u : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f g :=
  bigOmega_fun (insubd (bigOmega_refl F g) f).
Arguments the_bigOmega : simpl never, clear implicits.

Notation mkbigOmega tag x := (the_bigOmega tag _ (PhantomF x)).
Notation "[Omega_ x e 'of' f ]" := (mkbigOmega gen_tag x f e). (* parsing *)
Notation "[Omega '_' x e 'of' f ]" := (the_bigOmega _ _ (PhantomF x) f e).

Definition is_bigOmega {W} (F : set (set T)) (g : T -> W) :=
  [qualify f : T -> V | `[< bigOmega_def F f g >] ].
Fact is_bigOmega_key {W} (F : set (set T)) (g : T -> W) : pred_key (is_bigOmega F g).
Proof. by []. Qed.
Canonical is_bigOmega_keyed {W} (F : set (set T)) (g : T -> W) :=
  KeyedQualifier (is_bigOmega_key F g).
Notation "'Omega_ F g" := (is_bigOmega F g).

Lemma bigOmegaP {W} (F : set (set T)) (g : T -> W) (f : {Omega_F g}) :
  bigOmega_def F f g.
Proof. exact/asboolP. Qed.
Hint Extern 0 (bigOmega_def _ _ _) => solve[apply: bigOmegaP] : core.
Hint Extern 0 (locally _ _) => solve[apply: bigOmegaP] : core.
Hint Extern 0 (prop_near1 _) => solve[apply: bigOmegaP] : core.
Hint Extern 0 (prop_near2 _) => solve[apply: bigOmegaP] : core.

Notation "f '=Omega_' F h" := (f%function = mkbigOmega the_tag F f h).

Canonical the_bigOmega_bigOmega (tag : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := [bigOmega of the_bigOmega tag F phF f h].

Variant bigOmega_spec {W} (F : set (set T)) (g : T -> W) : (T -> V) -> Prop :=
  BigOmegaSpec f (k : posreal) of 
    (\forall x \near F, `|[f x]| >= k%:num * `|[g x]|) :
  bigOmega_spec F g f.

Lemma bigOmega {W} (F : filter_on T) (g : T -> W) (f : {Omega_F g}) :
  bigOmega_spec F g f.
Proof. by have [_/posnumP[k]] := bigOmegaP f; exists k. Qed.

(* properties of big Omega *)

Lemma eqOmegaO {W} (F : filter_on T) (f : T -> V) (e : T -> W) :
  (f \is 'Omega_F(e)) = (e =O_F f) :> Prop.
Proof.
rewrite propeqE; split => [| /eqO_exP[x x0 Hx] ];
[rewrite qualifE => /asboolP[x x0 Hx]; apply/eqO_exP |
rewrite qualifE; apply/asboolP];
exists x^-1; rewrite ?invr_gt0 //; near=> y.
  by rewrite ler_pdivl_mull //; near: y.
by rewrite ler_pdivr_mull //; near: y.
Grab Existential Variables. all: end_near. Qed.

Lemma eqOmegaE (F : filter_on T) (f e : T -> V) :
  (f =Omega_F(e)) = (f \is 'Omega_F(e)).
Proof.
rewrite propeqE; split=> [->|]; rewrite qualifE; last first.
  by move=> H; rewrite /the_bigOmega val_insubd H.
by apply/asboolP; rewrite /the_bigOmega val_insubd; case: ifPn => // /asboolP.
Qed.

Lemma eqOmega_trans (F : filter_on T) (f g h : T -> V) :
  f =Omega_F(g) -> g =Omega_F(h) -> f =Omega_F(h).
Proof. rewrite !eqOmegaE !eqOmegaO => fg gh; exact: (eqO_trans gh fg). Qed.

End big_omega.

Notation "{Omega_ F f }" := (@bigOmega_type _ _ _ _ F f).
Notation "[bigOmega 'of' f ]" := (@bigOmega_clone _ _ _ _ _ _ f _ _ idfun).
Notation mkbigOmega tag x := (the_bigOmega tag (PhantomF x)).
Notation "[Omega_ x e 'of' f ]" := (mkbigOmega gen_tag x f e).
Notation "[Omega '_' x e 'of' f ]" := (the_bigOmega _ _ (PhantomF x) f e).
Notation "'Omega_ F g" := (is_bigOmega F g).
Notation "f '=Omega_' F h" := (f%function = mkbigOmega the_tag F f h).
Arguments bigOmega {_ _ _ _}.

Section big_omega_in_R.

Variable pT : pointedType.

Lemma addOmega (F : filter_on pT) (f g h : _ -> R^o)
  (f_nonneg : forall x, 0 <= f x) (g_nonneg : forall x, 0 <= g x) :
  f =Omega_F h -> f + g =Omega_F h.
Proof.
rewrite 2!eqOmegaE !eqOmegaO => /eqOP hOf; apply/eqOP.
apply: filter_app hOf; near=> k; apply: filter_app; near=> x => /ler_trans.
by apply; rewrite ler_pmul2l // ![`|[_]|]absRE !ger0_norm // ?addr_ge0 //
  ler_addl.
Unshelve. end_near. Grab Existential Variables. end_near. Qed.

Lemma mulOmega (F : filter_on pT) (h1 h2 f g : pT -> R^o) :
  [Omega_F h1 of f] * [Omega_F h2 of g] =Omega_F (h1 * h2).
Proof.
rewrite eqOmegaE eqOmegaO [in RHS]bigOE //.
have [W1 k1 ?] := bigOmega; have [W2 k2 ?] := bigOmega.
near=> k; near=> x; rewrite [`|[_]|]absrM.
rewrite (@ler_trans _ ((k2%:num * k1%:num)^-1 * `|[(W1 * W2) x]|)) //.
  rewrite invrM ?unitfE ?gtr_eqF // -mulrA ler_pdivl_mull //.
  rewrite ler_pdivl_mull // (mulrA k1%:num) mulrCA [`|[_]|]normrM.
  by rewrite ler_pmul ?mulr_ge0 //; near: x.
by rewrite ler_wpmul2r // ltrW //; near: k; exists (k2%:num * k1%:num)^-1.
Grab Existential Variables. all: end_near. Qed.

End big_omega_in_R.


Section big_theta.

Context {K : absRingType} {T : Type} {V : normedModType K}.
Implicit Types W : normedModType K.

Let bigTheta_def W (F : set (set T)) (f : T -> V) (g : T -> W) :=
  exists2 k, (k.1 > 0) && (k.2 > 0) &
  \forall x \near F, k.1 * `|[g x]| <= `|[f x]| /\ `|[f x]| <= k.2 * `|[g x]|.

Structure bigTheta_type {W} (F : set (set T)) (g : T -> W) := BigTheta {
  bigTheta_fun :> T -> V;
  _ : `[< bigTheta_def F bigTheta_fun g >]
}.

Notation "{Theta_ F g }" := (@bigTheta_type _ F g).

Canonical bigTheta_subtype {W} (F : set (set T)) (g : T -> W) :=
  [subType for (@bigTheta_fun W F g)].

Lemma bigTheta_class {W} (F : set (set T)) (g : T -> W) (f : {Theta_F g}) :
  `[< bigTheta_def F f g >].
Proof. by case: f => ?. Qed.
Hint Resolve bigTheta_class : core.

Definition bigTheta_clone {W} (F : set (set T)) (g : T -> W) (f : T -> V)
  (fT : {Theta_F g}) c of phant_id (bigTheta_class fT) c := @BigTheta W F g f c.
Notation "[bigTheta 'of' f 'for' fT ]" := (@bigTheta_clone _ _ _ f fT _ idfun).
Notation "[bigTheta 'of' f ]" := (@bigTheta_clone _ _ _ f _ _ idfun).

Lemma bigTheta_refl_subproof F (g : T -> V) : Filter F -> bigTheta_def F g g.
Proof.
by move=> FF; exists 1 => /=; rewrite ?ltr01 //; near=> x; by rewrite mul1r.
Grab Existential Variables. all: end_near. Qed.

Definition bigTheta_refl (F : filter_on T) g :=
  BigTheta (asboolT (@bigTheta_refl_subproof F g _)).

Definition the_bigTheta (u : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f g :=
  bigTheta_fun (insubd (bigTheta_refl F g) f).
Arguments the_bigOmega : simpl never, clear implicits.

Notation mkbigTheta tag x := (@the_bigTheta tag _ (PhantomF x)).
Notation "[Theta_ x e 'of' f ]" := (mkbigTheta gen_tag x f e). (* parsing *)
Notation "[Theta '_' x e 'of' f ]" := (the_bigTheta _ _ (PhantomF x) f e).

Definition is_bigTheta {W} (F : set (set T)) (g : T -> W) :=
  [qualify f : T -> V | `[< bigTheta_def F f g >] ].
Fact is_bigTheta_key {W} (F : set (set T)) (g : T -> W) : pred_key (is_bigTheta F g).
Proof. by []. Qed.
Canonical is_bigTheta_keyed {W} (F : set (set T)) (g : T -> W) :=
  KeyedQualifier (is_bigTheta_key F g).
Notation "'Theta_ F g" := (@is_bigTheta _ F g).

Lemma bigThetaP {W} (F : set (set T)) (g : T -> W) (f : {Theta_F g}) :
  bigTheta_def F f g.
Proof. exact/asboolP. Qed.
Hint Extern 0 (bigTheta_def _ _ _) => solve[apply: bigThetaP] : core.
Hint Extern 0 (locally _ _) => solve[apply: bigThetaP] : core.
Hint Extern 0 (prop_near1 _) => solve[apply: bigThetaP] : core.
Hint Extern 0 (prop_near2 _) => solve[apply: bigThetaP] : core.

Canonical the_bigTheta_bigTheta (tag : unit) (F : filter_on T)
  (phF : phantom (set (set T)) F) f h := [bigTheta of @the_bigTheta tag F phF f h].

Variant bigTheta_spec {W} (F : set (set T)) (g : T -> W) : (T -> V) -> Prop :=
    BigThetaSpec f (k1 : posreal) (k2 : posreal) of
      (\forall x \near F, k1%:num * `|[g x]| <= `|[f x]|) &
      (\forall x \near F, `|[f x]| <= k2%:num * `|[g x]|) :
  bigTheta_spec F g f.

Lemma bigTheta {W} (F : filter_on T) (g : T -> W) (f : {Theta_F g}) :
  bigTheta_spec F g f.
Proof.
have [[_ _] /andP[/posnumP[k] /posnumP[k']]] := bigThetaP f.
by move=> /near_andP[]; exists k k'.
Qed.

Notation "f '=Theta_' F h" := (f%function = mkbigTheta the_tag F f h).

(* properties of big Theta *)

Lemma bigThetaE {W} (F : filter_on T) (f : T -> V) (g : T -> W) :
  (f \is 'Theta_F(g)) = (f =O_F g /\ f \is 'Omega_F(g)) :> Prop.
Proof.
rewrite propeqE; split.
- rewrite qualifE => /asboolP[[/= k1 k2] /andP[k10 k20]] /near_andP[Hx1 Hx2].
  by split; [rewrite eqO_exP; exists k2|
    rewrite qualifE; apply/asboolP; exists k1].
- case; rewrite eqO_exP qualifE => -[k1 k10 H1] /asboolP[k2 k20 H2].
  rewrite qualifE; apply/asboolP; exists (k2, k1) => /=; first by rewrite k20.
  by apply/near_andP; split.
Qed.

Lemma eqThetaE (F : filter_on T) (f e : T -> V) :
  (f =Theta_F(e)) = (f \is 'Theta_F(e)).
Proof.
rewrite propeqE; split=> [->|]; rewrite qualifE; last first.
  by move=> H; rewrite /the_bigTheta val_insubd H.
by apply/asboolP; rewrite /the_bigTheta val_insubd; case: ifPn => // /asboolP.
Qed.

Lemma eqThetaO (F : filter_on T) (f g : T -> V) : [Theta_F g of f] =O_F g.
Proof. by have [T1 k1 k2 ? ?] := bigTheta; apply/eqO_exP; exists k2%:num. Qed.

Lemma idTheta (F : filter_on T) (f : T -> V) : f =Theta_F f.
Proof. rewrite eqThetaE bigThetaE eqOmegaO; split; exact/idO. Qed.

Lemma Theta_sym (F : filter_on T) (f g : T -> V) :
  (f =Theta_F g) = (g =Theta_F f).
Proof. by rewrite !eqThetaE propeqE !bigThetaE !eqOmegaO; split => -[]. Qed.

Lemma eqTheta_trans (F : filter_on T) (f g h : T -> V) :
  f =Theta_F g -> g =Theta_F h -> f =Theta_F h.
Proof.
rewrite !eqThetaE !bigThetaE -!eqOmegaE => -[fg gf] [gh hg]; split.
by rewrite fg (bigO_bigO_eqO _ _ _ gh).
exact: (eqOmega_trans gf hg).
Qed.

End big_theta.

Notation "{Theta_ F g }" := (@bigTheta_type _ F g).
Notation "[bigTheta 'of' f ]" := (@bigTheta_clone _ _ _ _ _ _ f _ _ idfun).
Notation mkbigTheta tag x := (the_bigTheta tag (PhantomF x)).
Notation "[Theta_ x e 'of' f ]" := (mkbigTheta gen_tag x f e).
Notation "[Theta '_' x e 'of' f ]" := (the_bigTheta _ _ (PhantomF x) f e).
Notation "'Theta_ F g" := (is_bigTheta F g).
Notation "f '=Theta_' F h" := (f%function = mkbigTheta the_tag F f h).

Section big_theta_in_R.

Variable pT : pointedType.

Lemma addTheta (F : filter_on pT) (f g h : _ -> R^o)
  (f0 : forall x, 0 <= f x) (g0 : forall x, 0 <= g x) (h0 : forall x, 0 <= h x) :
  [Theta_F h of f] + [O_F h of g] =Theta_F h.
Proof.
rewrite eqThetaE bigThetaE; split; first by rewrite eqThetaO addO.
rewrite -eqOmegaE; apply: addOmega.
- by move=> ?; rewrite /the_bigTheta val_insubd /=; case: ifP.
- by move=> ?; rewrite /the_bigO val_insubd /=; case: ifP.
- rewrite eqOmegaE eqOmegaO; have [T1 k1 k2 ? ?] := bigTheta.
  rewrite bigOE //; apply/bigO_exP; exists k1%:num^-1 => //.
  by near=> x; rewrite ler_pdivl_mull //; near: x.
Grab Existential Variables. all: end_near. Qed.

Lemma mulTheta (F : filter_on pT) (h1 h2 f g : pT -> R^o) :
  [Theta_F h1 of f] * [Theta_F h2 of g] =Theta_F h1 * h2.
Proof.
rewrite eqThetaE bigThetaE; split.
  by rewrite (eqThetaO _ f) (eqThetaO _ g) mulO.
rewrite eqOmegaO [in RHS]bigOE //.
have [T1 k1 l1 P1 ?] := bigTheta; have [T2 k2 l2 P2 ?] := bigTheta.
near=> k; first near=> x.
rewrite [`|[_]|]absrM (@ler_trans _ ((k2%:num * k1%:num)^-1 * `|[(T1 * T2) x]|)) //.
  rewrite invrM ?unitfE ?gtr_eqF // -mulrA ler_pdivl_mull //.
  rewrite ler_pdivl_mull // (mulrA k1%:num) mulrCA [`|[_]|]normrM ler_pmul //;
  by [rewrite mulr_ge0 // ltrW|near: x].
by rewrite ler_wpmul2r // ltrW //; near: k; exists (k2%:num * k1%:num)^-1.
Grab Existential Variables. all: end_near. Qed.

End big_theta_in_R.
