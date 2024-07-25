From elpi Require Import elpi.


Elpi Tactic foo.



(* Elpi Accumulate lp:{{
  pred foo i:term.

  foo X :- coq.say "first case", X = {{ 3 }}.
  foo _ :- coq.say "second case".

  pred bar i:term.
  bar _ :- foo X, !, X = {{ 2 }}.

}}.
Elpi Typecheck. *)
(* 
Elpi Query lp:{{ bar {{ 2 }}. }}. *)


Elpi Tactic atomic_ho_eq.

Ltac assert_and_clear t H := 
  let H' := fresh in
  assert (H' := H);
  clear H; 
  assert (H: t) by (intros; let t := type of H' in idtac t; rewrite H'; reflexivity); clear H'.


Ltac assert_and_clear_2 t pf_t H := 
  let H' := fresh in
  assert (H' : t) by (refine pf_t);
  clear H;
  assert (H := H');
  clear H'.




Elpi Accumulate lp:{{


  pred applyLambda i:term, o:(term -> term).

  applyLambda (fun _ _ U) (x\ U x).

  applyLambda U (x\ app [U, x]).

  pred liftEq i:term, o:term, i:term, o:term.

  liftEq (app [{{ @eq }}, prod Na Ty F, T, U])
         (prod Na Ty (x\ app [{{ @eq }}, (F x), Tx x, Ux x]))
         H
         (fun Na Ty (x\ app [ {{ @eq_ind_r }}, _, _,
            fun _ _ (t\ app [{{ @eq }}, _, app [t, x], Ux x ]), app [ {{ @eq_refl }}, _, _ ], _, H ])) :-
    applyLambda T Tx,
    applyLambda U Ux.

  liftEq (prod Na Ty E) (prod Na Ty Y) B (fun Na Ty B2) :- pi x\ (liftEq (E x) (Y x) (app [B, x]) (B2 x)).

  liftEq  _ _ _ _ :-
    coq.error "[liftEq]: The argument should be a universally quantified higher order equality.".

  solve ((goal _ _ _ _ [trm H]) as G) GS :-
    coq.typecheck H PrevEq ok,
    !,
    liftEq PrevEq NewEq H NewPf,
    coq.ltac.call "assert_and_clear_2" [trm NewEq, trm NewPf, trm H] G GS.

  solve (goal _ _ _ _ [trm H]) _ :-
    coq.typecheck H _ (error S),

    coq.ltac.fail 0 "[atomic_ho_eq]: Given term is ill-typed: " S.

  solve (goal _ _ _ _ [_]) _ :- !,
    coq.error "The argument should be a term.".

  solve (goal _ _ _ _ _) _ :- !, coq.error "The tactic requires exactly one argument.".


}}.
Elpi Typecheck.

Section foo.

Variable f g : nat -> nat -> nat -> nat -> nat.

Lemma foo : (forall x, f x = g x) -> forall x y, f x y = g x y.
  intros.
  rewrite H.
  reflexivity.
Qed.

Print foo.

Definition foo2 : (forall x, (fun y => f x y) = g x) -> forall x y, f x y = g x y :=
  fun (H : forall x : nat, f x = g x) (x y : nat) =>
eq_ind_r (fun n : nat -> nat -> nat -> nat => n y = g x y) eq_refl (H x).

Lemma foo3 : f = g -> forall x, f x = g x.
  intros.
  rewrite H.
  reflexivity.
Qed.

Set Printing All.

Print foo3.

About eq_ind_r.

Goal (g = (fun x => f x)) -> False.
  intro H.
  elpi atomic_ho_eq (H).
  elpi atomic_ho_eq (H).

  elpi atomic_ho_eq (H).

  elpi atomic_ho_eq (H).

  pose (h := false).
  try elpi atomic_ho_eq.
