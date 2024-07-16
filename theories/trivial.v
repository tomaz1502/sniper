From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".

Ltac2 foo (a: constr) (b: constr) := apply (@conj $a $b).

Ltac foo2 a b := apply (@conj a b).

Tactic Notation "my_foo2" constr(a) constr(b) :=
  let tac :=
    ltac2:(a b |-
            let a' := Option.get (Ltac1.to_constr a) in
            let b' := Option.get (Ltac1.to_constr b) in
            foo a' b') in
  tac a b.



(* Goal forall a b , a -> b -> a /\ b. *)
(*   intros a b ha hb. *)
(*   my_foo a b. *)
(*   Abort. *)
(*   foo2 a b. *)
(*   apply (@conj a b). *)
(*   exact1 false preterm:(conj ha hb). *)
(*   Abort. *)

Ltac2 destruct_conj (h: ident) :=
  destruct h as [h1 h2].
