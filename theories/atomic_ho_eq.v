From MetaCoq.Template Require Import All.

Require Import utilities.
Require Import List.

Definition my_id (t : Type) (a : t) := a.

Fixpoint f (ho_eq_quoted : term) :=
  match ho_eq_quoted with
    | tProd name ty body => tProd name ty (f body)
    | tApp t [tProd name dom codom; lhs; rhs] =>
        if eqb_term t <% @eq %> then
          let lhs' :=
            match lhs with
              | tLambda name type body => subst10 body (tRel 0)
              | e => tApp (lift 1 0 e) [tRel 0]
            end
          in
          let rhs' :=
            match rhs with
              | tLambda name type body => subst10 body (tRel 0)
              | e => tApp (lift 1 0 e) [tRel 0]
            end
          in
          tProd name dom (tApp <% @eq %> [codom; lhs'; rhs'])
        else tVar "not an equality"%bs
    | _ => tVar "wildcard"%bs
  end.

Ltac atomic_ho_eq h :=
  let new_name := fresh in
  assert (new_name := h);
  clear h;
  let t := type of new_name in
  let t_quoted := metacoq_get_value (tmQuote t) in
  let new_goal_quoted := eval cbv in (f t_quoted) in
  let new_goal := metacoq_get_value (tmUnquoteTyped Prop new_goal_quoted) in
  assert (h : new_goal);
  [intro; try rewrite new_name; reflexivity | clear new_name].


(* Goal my_id = (fun t a => my_id t a) -> True. *)
(*   Proof. *)
(*     intro h. *)
(*     atomic_ho_eq h. *)
(*     Set Printing All. *)
(*     atomic_ho_eq h. *)
(*     Abort. *)

(* Goal *)
(*   forall A : Type, *)
(*        hd_error (A:=A) = (fun (A0 : Type) (l : list A0) => (fun _ => match l with *)
(*                                                            | [] => (fun _ => None) 0 *)
(*                                                            | x :: _ => Some x *)
(*                                                            end) 1) A -> True. *)
(*   Proof. *)
(*     intros t H. *)
(*     Eval red in H. *)
