From elpi Require Import elpi.
Require Import List.
Import ListNotations.
From Sniper Require Import Sniper.
From Sniper.orchestrator Require Import Sniper.
(* From Sniper Require Import verit. *)
From SMTCoq Require Import Database_trakt.
From SMTCoq Require Import SMT_terms.
Require Import ZArith.
From Trakt Require Import Trakt.


Local Open Scope Z_scope.

Goal forall xs : list Z , (match xs with | [] => 3 | _ :: _ => 4 end) <= 4.
  pose (f := fun (ys : list Z) => match ys with | [] => 3 | _ :: _ => 4 end).
  intro xs.
  fold (f xs).
  snipe.
Qed.

Inductive t : Type :=
  | foo1 : t.
  (* | foo2 : t *)
  (* | foo3 : nat -> t *)
  (* | foo4 : bool -> t *)
  (* | foo5 : t -> t -> t. *)


Goal forall x y : nat, ((if x <? y then x else y) <= x)%nat.
  intros x y.
  trakt Z bool.
  Unshelve.
  pose (f := fun a b => (if a <? b then  a else b)%nat).
  intros x y.
  fold (f x y).
  snipe.
Qed.
Goal forall (xs : list nat) (o : option nat) ,
       (match xs with
         | [] => match o with
                  | None => 42
                  | Some x => x
                end
         | h::t => h
       end >= 0)%nat.
  intros xs o.
  pose (f := (fun xs' o' => match xs' with | [] => match o' with | Some x => x | None => 42 end | h :: _ => h end)%nat).
  fold (f xs o).
  scope.


(*   assert (H : CompDec Z) by admit. *)
  scope. verit_orch.
  verit_orch.
  


Elpi Tactic match_to_eqn.
Elpi Accumulate lp:{{

pred mkeqbo i:term, i:term, i:term, i:term, o:term.
mkeqbo {{ fun x => lp:(Bo x) }} K E M {{ fun x => lp:(Bo1 x) }} :- !,
  @pi-decl `x` _ x\
    mkeqbo (Bo x) {coq.mk-app K [x]} E M (Bo1 x).
mkeqbo B K E (match _ RTy Bs as M) {{ fun h : lp:E = lp:K => lp:Proof h : lp:Ty }} :-
  Proof = {{ @eq_ind_r _ lp:K lp:Pred (refl_equal lp:B) lp:E }},
  Pred = {{ fun x => lp:{{ match {{ x }} RTy Bs }} = lp:B }},
  Ty = {{ lp:M = lp:B }}.

pred mkeqn i:list term, i:list term, i:term, i:term, o:term.
mkeqn [] [] _ _ {{ _ }}.
mkeqn [B|Bs] [K|Ks] E M {{ let h := lp:Bo in lp:(R h) }} :-
  mkeqbo B K E M Bo,
  @pi-def `h` _ Bo h\
    mkeqn Bs Ks E M (R h).

solve (goal _ _ _ _ [trm (match E _ Bs as M)] as G) GL :- std.do! [
  std.assert-ok! (coq.typecheck M _) "illtyped input",
  coq.typecheck E Ty ok,
  coq.safe-dest-app Ty (global (indt I)) Args,
  coq.env.indt I _ _ Pno _ Ks _,
  std.take Pno Args Params,
  std.map Ks (x\r\ coq.mk-app (global (indc x)) Params r) KPs,
  mkeqn Bs KPs E M T,
  coq.say "M=" M "T=" {coq.term->string T},
  std.assert! (refine T G GL) "bug in term generation"
].
}}.
Elpi Typecheck.




Lemma foo : nat.

elpi match_to_eqn (match 2 with
| 0 => true
| S k => false
end).






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
